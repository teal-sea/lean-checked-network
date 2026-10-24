#!/usr/bin/env python3
"""Restricted, stdlib-only ONNX protobuf import. No ONNX execution or float arithmetic.
Only this benchmark's zero Sub, axis-1 Flatten, MatMul/Add and Relu chain is admitted.
The ONNX-to-constants correspondence is audited, not a Lean theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, math, re, struct

ROOT = Path(__file__).resolve().parent

def fields(data):
    pos = 0
    def varint():
        nonlocal pos
        n = shift = 0
        while True:
            if pos >= len(data) or shift > 70: raise ValueError('bad varint')
            b = data[pos]; pos += 1; n |= (b & 127) << shift
            if b < 128: return n
            shift += 7
    out = {}
    while pos < len(data):
        tag = varint(); k, w = tag >> 3, tag & 7
        if k == 0: raise ValueError('invalid protobuf field')
        if w == 0: v = varint()
        elif w in (1, 2, 5):
            n = varint() if w == 2 else (8 if w == 1 else 4)
            if pos + n > len(data): raise ValueError('truncated field')
            v = data[pos:pos+n]; pos += n
        else: raise ValueError('unsupported protobuf wire type')
        out.setdefault(k, []).append(v)
    return out

def one(d, k, default=None):
    v = d.get(k, [])
    if len(v) > 1: raise ValueError('duplicate scalar')
    return v[0] if v else default

def text(d, k): return one(d, k, b'').decode('utf8')
def packed(v):
    # packed repeated positive varints, e.g. tensor dimensions
    out=[]; n=shift=0
    for b in v:
        n |= (b & 127) << shift
        if b < 128: out.append(n); n=shift=0
        else: shift += 7
    if shift: raise ValueError('truncated packed varint')
    return out

def tensor(raw):
    d=fields(raw)
    if one(d,2) != 1 or 13 in d or 14 in d: raise ValueError('only embedded float32')
    dims=[]
    for v in d.get(1,[]): dims.extend(packed(v) if isinstance(v,bytes) else [v])
    if any(n <= 0 for n in dims): raise ValueError('invalid dimensions')
    if 4 in d and 9 in d: raise ValueError('ambiguous tensor encoding')
    raw=one(d,9)
    if raw is None: raw=b''.join(d.get(4,[]))
    if len(raw)!=4*math.prod(dims): raise ValueError('tensor byte length')
    values=[]; bits=[]
    for (b,) in struct.iter_unpack('<I',raw):
        sign=-1 if b>>31 else 1; e=(b>>23)&255; m=b&0x7fffff
        if e==255: raise ValueError('nonfinite float32')
        n=m if e==0 else m+(1<<23); power=-149 if e==0 else e-150
        values.append(sign*F(n)*(F(2)**power)); bits.append(f'{b:08x}')
    return text(d,8), {'dims':dims,'values':values,'bits':bits}

def valueinfo(raw):
    d=fields(raw); ty=fields(one(d,2)); tt=fields(one(ty,1)); shape=fields(one(tt,2))
    if one(tt,1)!=1: raise ValueError('nonfloat input/output')
    return text(d,1), [one(fields(x),1) for x in shape.get(1,[])]

def decode(raw):
    model=fields(raw)
    if 20 in model or 25 in model: raise ValueError('training graphs / functions unsupported')
    opsets=[fields(x) for x in model.get(8,[])]
    if len(opsets)!=1 or text(opsets[0],1)!='' or one(opsets[0],2)!=8: raise ValueError('only ONNX default opset 8')
    if one(model,1)!=3: raise ValueError('only frozen ONNX IR version 3')
    g=fields(one(model,7)); ts={}
    if 15 in g: raise ValueError('sparse initializers unsupported')
    for t in g.get(5,[]):
        name,val=tensor(t)
        if name in ts: raise ValueError('duplicate initializer')
        ts[name]=val
    input_list=[valueinfo(x) for x in g.get(11,[])]
    output_list=[valueinfo(x) for x in g.get(12,[])]
    ins=dict(input_list); outs=dict(output_list)
    if len(ins)!=len(input_list) or len(outs)!=len(output_list): raise ValueError('duplicate interface names')
    if {k: v for k,v in ins.items() if k not in ts} != {'input':[1,1,1,5]}: raise ValueError('external input shape')
    for k in ts:
        if k in ins and ins[k]!=ts[k]['dims']: raise ValueError('initializer declaration mismatch')
    nodes=[]
    for x in g.get(1,[]):
        n=fields(x)
        if text(n,7): raise ValueError('custom operator domain')
        attrs={}
        for ar in n.get(5,[]):
            a=fields(ar); key=text(a,1)
            if key in attrs: raise ValueError('duplicate attribute')
            if one(a,20)!=2 or 3 not in a: raise ValueError('unsupported attribute')
            attrs[key]=one(a,3)
        nodes.append((text(n,4), [v.decode() for v in n.get(1,[])], [v.decode() for v in n.get(2,[])],attrs))
    expected=['Sub','Flatten']+['MatMul','Add','Relu']*6+['MatMul','Add']
    if [n[0] for n in nodes]!=expected: raise ValueError('unsupported operator sequence')
    prev='input'; used=set(); produced={prev}; layers=[]; dim=5
    for i,(op,inputs,outputs,attrs) in enumerate(nodes):
        if len(outputs)!=1 or outputs[0] in produced or outputs[0] in ts: raise ValueError('output name collision')
        if not inputs or inputs[0]!=prev: raise ValueError('non-chain graph')
        if op=='Flatten':
            if inputs!=[prev] or attrs!={'axis':1}: raise ValueError('flatten semantics')
        elif op=='Relu':
            if inputs!=[prev] or attrs: raise ValueError('Relu semantics')
        else:
            if len(inputs)!=2 or inputs[1] not in ts or attrs: raise ValueError('binary operator semantics')
            t=ts[inputs[1]]; used.add(inputs[1])
            if op=='Sub':
                if t['dims']!=[1,1,1,5] or any(t['values']): raise ValueError('nonidentity normalization')
            elif op=='MatMul':
                k=5 if i==len(nodes)-2 else 50
                if t['dims']!=[dim,k]: raise ValueError('matrix dimensions')
                layers.append({'n':dim,'m':k,'w':t['values'],'weight_name':inputs[1]}); dim=k
            else:
                if t['dims']!=[dim]: raise ValueError('bias dimensions')
                layers[-1]['b']=t['values']; layers[-1]['bias_name']=inputs[1]
        prev=outputs[0]; produced.add(prev)
    if used!=set(ts) or outs!={prev:[1,5]}: raise ValueError('unused initializer / output mismatch')
    return layers,nodes,ts

def property_data(raw):
    s=raw.decode('ascii'); active='\n'.join(x.split(';')[0] for x in s.splitlines())
    lo=['0.6','-0.5','-0.5','0.45','-0.5']; hi=['0.679857769','0.5','0.5','0.5','-0.45']; th='3.991125645861615'
    assertions=re.findall(r'\(assert\s+\((<=|>=)\s+([XY]_\d)\s+(-?[\d.]+)\)\)',active)
    expected=[('>=',f'X_{i}',v) for i,v in enumerate(lo)]+[('<=',f'X_{i}',v) for i,v in enumerate(hi)]+[('>=','Y_0',th)]
    if sorted(assertions)!=sorted(expected) or active.count('(assert')!=len(expected): raise ValueError('property token mismatch')
    # Byte strings above match tokens exactly; no float parsing or decimal reformatting.
    return lo,hi,th

def lit(x): return f'({x.numerator} / {x.denominator} : Rat)'
def arr(xs): return '#['+', '.join(lit(x) for x in xs)+']'
def sha(b): return hashlib.sha256(b).hexdigest()

def validate_sources(raw, prop):
    if sha(raw) != '843f7110bf5a8b7f0eeb9b1c548d9d558db9099328b392423d5a7444a0656dd4':
        raise ValueError('wrong frozen ONNX bytes')
    if sha(prop) != '7a9a9930711817c6cc39940f5c1d0f8c51f2ed82f38e203c4b5de03c19bd4ced':
        raise ValueError('wrong frozen property bytes')

def main():
    raw=(ROOT/'ACASXU_run2a_1_1_batch_2000.onnx').read_bytes(); pr=(ROOT/'prop_1.vnnlib').read_bytes()
    validate_sources(raw, pr)
    layers,nodes,ts=decode(raw); lo,hi,th=property_data(pr)
    code=['-- Generated by importer.py; exact binary32 rationals. Do not edit.',
          'import NN.Verification.Cert.CROWNQuery', 'namespace Frozen',
          'open Spec TorchLean TorchLean.Tensor',
          'open NN.Verification.Cert.CROWNQuery',
          'open scoped Spec.RationalAlgebraic', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0']
    for k,t in enumerate(layers):
        n,m=t['n'],t['m']; w=t['w']
        # ONNX W is [in,out], TorchLean weights are [out,in].
        code += [f'def w{k} : Tensor Rat [{m}, {n}] :=',
                 f'  Tensor.Internal.Rep.ofArray {arr([w[i*m+j] for j in range(m) for i in range(n)])} (by decide)',
                 f'def b{k} : Tensor Rat [{m}] :=',f'  Tensor.Internal.Rep.ofArray {arr(t["b"])} (by decide)',
                 f'def layer{k} : Network {n} {m} := .linear ⟨w{k}, b{k}⟩']
    expr='layer6'
    for k in reversed(range(6)):
        expr=f'.comp layer{k} (.comp (.relu (Tensor.full [50] (0 : Rat))) ({expr}))'
    code += ['def network : Network 5 5 := '+expr,
             '-- Rational evaluator uses the same module operations as Network.model.',
             'def evalQ {n m : Nat} : Network n m → Tensor Rat [n] → Tensor Rat [m]',
             '  | .linear l, x => Tensor.addSpec (matVecMulSpec l.weights x) l.bias',
             '  | .relu _, x => Activation.reluSpec x',
             '  | .comp a b, x => evalQ b (evalQ a x)', 'end Frozen']
    (ROOT/'Net.lean').write_text('\n'.join(code)+'\n')
    spec='''import Net
namespace Frozen
open Spec TorchLean TorchLean.Tensor
noncomputable def lo : Fin 5 → ℝ := ![3/5, -1/2, -1/2, 9/20, -1/2]
noncomputable def hi : Fin 5 → ℝ := ![679857769/1000000000, 1/2, 1/2, 1/2, -9/20]
noncomputable def threshold : ℝ := 3991125645861615/1000000000000000
/-- Frozen real safety statement; deliberately no proof. Inputs already normalized.
ONNX importer correspondence, IEEE execution and aircraft behavior are outside this Prop. -/
def ACASXu_1_1_Property1 : Prop :=
  ∀ x : Tensor ℝ [5],
    (∀ i : Fin 5, lo i ≤ x.getScalar i ∧ x.getScalar i ≤ hi i) →
    (network.model.forward x).getScalar 0 < threshold
end Frozen
'''
    (ROOT/'Spec.lean').write_text(spec)
    # Independent Python forward uses original ONNX [in,out] orientation, not generated tensors.
    def forward(x):
        for k,t in enumerate(layers):
            x=[sum((x[i]*t['w'][i*t['m']+j] for i in range(t['n'])),t['b'][j]) for j in range(t['m'])]
            if k<6: x=[max(F(0),v) for v in x]
        return x
    points=[[F(lo[i])+(F(hi[i])-F(lo[i]))*F((j*(i+3)+i*7)%19,18) for i in range(5)] for j in range(20)]
    # Include both corners and midpoint; remaining deterministic mixed-coordinate rationals.
    points[0]=list(map(F,lo)); points[1]=list(map(F,hi)); points[2]=[(F(a)+F(b))/2 for a,b in zip(lo,hi)]
    results=[forward(x) for x in points]
    check=['import Net','open Spec TorchLean TorchLean.Tensor','open Frozen', 'open scoped Spec.RationalAlgebraic','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for j,(x,y) in enumerate(zip(points,results)):
        check += [f'def input{j} : Tensor Rat [5] := Tensor.Internal.Rep.ofArray {arr(x)} (by decide)',
                  f'def expected{j} : Array Rat := {arr(y)}',
                  f'#eval (List.finRange 5).all (fun i => decide ((evalQ network input{j}).getScalar i = expected{j}[i.val]!))']
    (ROOT/'Agreement.lean').write_text('\n'.join(check)+'\n')
    (ROOT/'agreement.json').write_text(json.dumps({'label':'derived exact rational test vectors','inputs':[[str(v) for v in x] for x in points],'outputs':[[str(v) for v in y] for y in results]},indent=2)+'\n')
    manifest={'label':'measured source metadata; rational embedding derived from bits','onnx_sha256':sha(raw),'property_sha256':sha(pr),'importer_sha256':sha((ROOT/'importer.py').read_bytes()),'onnx_ir_version':3,'onnx_default_opset':8,'Net.lean_sha256':sha((ROOT/'Net.lean').read_bytes()),'Spec.lean_sha256':sha((ROOT/'Spec.lean').read_bytes()),'decimal_tokens':{'lo':lo,'hi':hi,'threshold':th},'operators':[n[0] for n in nodes],'dimensions':[[t['n'],t['m']] for t in layers], 'initializers':{k:{'dims':t['dims'],'bits_sha256':sha(''.join(t['bits']).encode())} for k,t in ts.items()}}
    (ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    with (ROOT/'runs.jsonl').open('a') as f: f.write(json.dumps({'experiment':'import-and-python-forward','status':'pass','label':'measured','inputs':len(points),'manifest':manifest})+'\n')
    print(json.dumps(manifest,indent=2))
if __name__=='__main__': main()
