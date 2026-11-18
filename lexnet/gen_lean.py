"""Generate exact Lean integer semantics from the pinned binary, never C.

Sparse affine rows are emitted without changing arithmetic. All recurrent
coefficients are integral. Head logits are doubled to remove the sole half bias.
The automaton is a dependency slice of the full forward cell, linked by rfl.
"""
import argparse, hashlib, json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from exact import Model, WEIGHTS
p=argparse.ArgumentParser(); p.add_argument('--fault',action='store_true'); p.add_argument('--weights',default=str(WEIGHTS)); p.add_argument('--out',default=None); a=p.parse_args()
m=Model(a.weights)
if a.fault: m.fwd[0]['W'][5][10] = -1  # star coefficient in block-comment opener
certificate=json.loads((ROOT/'evidence/automaton.json').read_text())
def integer(n):
    assert int(n)==n
    return str(int(n)) if n>=0 else f'({int(n)})'
def lst(xs): return '['+', '.join(map(str,xs))+']'
def ilst(xs): return lst(map(integer,xs))

lines=['import Std', '', '/- Generated from SHA256 '+hashlib.sha256(pathlib.Path(a.weights).read_bytes()).hexdigest()+'. -/',
       'namespace Lexnet', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
       'abbrev Byte := Fin 256', 'abbrev AState := List Int',
       'structure Features where', '  flags : List Int', '  code : Int',
       'structure FState where', '  auto : AState',
       '  W : Int', '  N : Int', '  d : Int', '  h1 : Int', '  h2 : Int',
       'def embedding (b : Byte) : Features :=', '  match b.val with']
for b in range(128):
    row=m.emb[b]
    lines.append(f'  | {b} => ⟨{ilst(row[:13])}, {integer(row[13])}⟩')
lines.append(f'  | _ => ⟨{ilst(m.emb[127][:13])}, {integer(m.emb[127][13])}⟩')

def graph(cell, inputs, prefix):
    nodes={}; v=inputs
    for li,l in enumerate(cell):
        out=[]
        for ri,(row,b,hi) in enumerate(zip(l['W'],l['b'],l['hi'])):
            name=f'{prefix}{li}_{ri}'
            terms=[f'({integer(w)} * {v[i]})' for i,w in enumerate(row) if w]
            expr=' + '.join([integer(b)]+terms)
            expr=f'max (0 : Int) ({expr})'
            if hi!=float('inf'): expr=f'min {integer(hi)} ({expr})'
            deps=[v[i] for i,w in enumerate(row) if w and v[i] in nodes]
            nodes[name]=(expr,deps)
            out.append(name)
        v=out+[v[i] for i in l['skip']]
    return nodes,v

ins=[f'(x.flags.getD {i} 0)' for i in range(13)]+['x.code']
hs=[f'(h.auto.getD {i} 0)' for i in range(13)]+['h.W','h.N','h.d','h.h1','h.h2']
nodes,v=graph(m.fwd,ins+hs,'f')
state=[v[i] for i in m.fs]; fout=[v[i] for i in m.fo]
def emit_nodes(nodes,needed=None,replacements=()):
    if needed is not None:
        seen=set()
        def visit(n):
            if n in seen or n not in nodes: return
            seen.add(n)
            for d in nodes[n][1]: visit(d)
        for n in needed: visit(n)
    else: seen=nodes
    for name,(expr,_) in nodes.items():
        if name in seen:
            for old,new in replacements: expr=expr.replace(old,new)
            lines.append(f'  let {name} := {expr}')

lines.append('def forward (x : Features) (h : FState) : FState × List Int :=')
emit_nodes(nodes)
lines.append(f'  (⟨{lst(state[:13])}, '+', '.join(state[13:])+'⟩, '+lst(fout)+')')
lines.append('def autoStep (x : List Int) (h : AState) : AState :=')
emit_nodes(nodes,state[:13],[('x.flags','x'),('h.auto','h')])
lines.append('  '+lst(state[:13]))
lines += ['theorem projection (x : Features) (h : FState) :',
          '    (forward x h).1.auto = autoStep x.flags h.auto := by rfl']

bnodes,bv=graph(m.bwd,[f'(f.getD {i} 0)' for i in range(m.nfo)]+[f'(h.getD {i} 0)' for i in range(m.nbs)],'b')
lines.append('def backward (f h : List Int) : List Int × List Int :=')
emit_nodes(bnodes)
logits=[]
for row,b in zip(m.head2,m.hb2):
    logits.append('('+' + '.join([integer(b)]+[f'({integer(w)} * {bv[i]})' for i,w in enumerate(row) if w])+')')
lines.append('  ('+lst([bv[i] for i in m.bs])+', '+lst(logits)+')')
lines += [f'def initial : FState := ⟨{ilst(m.h0[:13])}, '+', '.join(map(integer,m.h0[13:]))+'⟩',
          'def initialAuto : AState := initial.auto',
          'def inputs : List (List Int) := [']
lines += ['  '+ilst(x)+',' for x in certificate['inputs']]
lines += [']','def reach : List AState := [']
lines += ['  '+ilst(h)+',' for h in certificate['reach']]
lines += [']']

lines += [(ROOT/'lean/Proof.inc').read_text()]
target=pathlib.Path(a.out) if a.out else ROOT/'lean'/('ExpectedFail.lean' if a.fault else 'Pilot.lean')
target.write_text('\n'.join(lines)+'\n')
stats=dict(fault=a.fault, generated_lines=len(target.read_text().splitlines()),
           generated_bytes=target.stat().st_size, forward_affine_rows=len(nodes),
           backward_affine_rows=len(bnodes), weight_sha256=hashlib.sha256(pathlib.Path(a.weights).read_bytes()).hexdigest())
print(json.dumps(stats,indent=2))
if not a.out: (ROOT/'evidence'/('generation-fault.json' if a.fault else 'generation.json')).write_text(json.dumps(stats,indent=2))
