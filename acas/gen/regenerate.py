#!/usr/bin/env python3
"""Regenerate the frozen importer, receipts and concrete Lean instances in isolation."""
import difflib,argparse,hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
G=Path(__file__).resolve().parent; A=G.parent; L=A/'lean/ACASChecked'

def generated(p):
 s=str(p)
 return (p.parts[0].startswith('N') and p.parts[0][1:].isdigit()) or p.parts[0] in ('Instances','ParamChunks') or p.stem in ('Net','Spec','Weights','CoverageData','AllLeaves','ControlDual','ControlWeight','UnsafeNode13','UnsafeControl13','CoverageControl','Final','NodeNC') or p.stem.startswith('Parameters')

def rename(s):
 mods={str(p.relative_to(L).with_suffix('')).replace('/','.') for p in L.rglob('*.lean')}
 return re.sub(r'(?m)^import (\S+)\s*$',lambda m:'import ACASChecked.'+m[1] if m[1] in mods else m[0],s)

def run(script,cwd):
 p=subprocess.run([sys.executable,str(script)],cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if p.returncode: raise RuntimeError(p.stdout.decode())

def parameters(out):
 common='namespace ACASCommon\nopen RouteA RouteNC Spec TorchLean TorchLean.Tensor\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
 (out/'ParamChunks').mkdir(exist_ok=True)
 for k in range(7):
  if k in range(1,6):
   for chunk in range(10):
    s='import Common\nimport Net\n'+common
    for j in range(5*chunk,5*chunk+5):
     s+=f'theorem paramW{k}row{j} : ∀ i : Fin 50,\n    ((matrix (weights {k}) i {j} : Int) : Rat) = (Q : Rat)*get2 Frozen.w{k} ⟨{j},by decide⟩ i := by decide +kernel\n'
    (out/f'ParamChunks/P{k}_{chunk}.lean').write_text(s+'end ACASCommon\n')
   s=''.join(f'import ParamChunks.P{k}_{c}\n' for c in range(10))+common
   s+=f'theorem paramW{k} : ∀ (i j : Fin 50),\n    ((matrix (weights {k}) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w{k} j i := by\n  intro i j\n  fin_cases j\n'
   s+=''.join(f'  · exact paramW{k}row{j} i\n' for j in range(50))
  else:
   s='import Common\nimport Net\n'+common
   typ='(i : Fin 5) (j : Fin 50)' if k==0 else '(i : Fin 50) (j : Fin 1)'
   idx='j' if k==0 else '(0 : Fin 5)'
   s+=f'theorem paramW{k} : ∀ {typ},\n    ((matrix (weights {k}) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w{k} {idx} i := by decide +kernel\n'
  if k<6:s+=f'theorem paramB{k} : ∀ j : Fin 50,\n    (((biases {k}).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b{k}.getScalar j := by decide +kernel\n'
  else:s+='theorem paramB6 : (((biases 6).getD 0 0 : Int) : Rat) = (Q : Rat)*Frozen.b6.getScalar 0 := by decide +kernel\n'
  s+=f'#print axioms paramW{k}\n#print axioms paramB{k}\nend ACASCommon\n'
  (out/f'Parameters{k}.lean').write_text(s)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--inputs',type=Path,default=A/'inputs');args=ap.parse_args()
 scratch=A/'work/regeneration';scratch.mkdir(parents=True,exist_ok=True)
 pins=json.loads((G/'input-hashes.json').read_text())
 for name,digest in pins['release_files'].items():
  if hashlib.sha256((A/name).read_bytes()).hexdigest()!=digest:raise ValueError('wrong frozen input: '+name)
 with tempfile.TemporaryDirectory(prefix='acas-regenerate-',dir=scratch) as temp:
  root=Path(temp); out=root/'route-a-all';out.mkdir(); w2=root/'w2-producer/work';w2.mkdir(parents=True); step2=root/'step2';step2.mkdir()
  shutil.copy(A/'producer/certificate.json',w2/'cert-supported-crown-1_1-p1.json')
  shutil.copy(A/'producer/crownint-weight-mutation.json',w2/'crownint-weight-mutation.json')
  for name in ['ACASXU_run2a_1_1_batch_2000.onnx','prop_1.vnnlib']:shutil.copy(args.inputs/name,out/name)
  shutil.copy(G/'importer.py',out/'importer.py');run(out/'importer.py',out)
  shutil.copytree(G/'legacy',out/'templates')
  for name in ['Node.lean','Accept.lean','ShapeNC.lean']:shutil.copy(G/'templates'/name,root/name)
  # The original emitter's scratch directory layout is explicit and private to this run.
  route=root/'route-a';route.mkdir()
  for p in G.joinpath('templates').glob('*.lean'):shutil.copy(p,route/p.name)
  for name in ['prepare.py','patch-generated.py','coveragegen.py','assemble.py','controls-gen.py']:shutil.copy(G/'legacy'/name,out/name)
  run(out/'prepare.py',out);run(out/'coveragegen.py',out);run(out/'assemble.py',out);run(out/'controls-gen.py',out)
  # Generic proof templates are not generated; instances are derived from the leaf list.
  run(G/'legacy/generate_instances.py',step2)
  for p in step2.rglob('*.lean'):
   dest=out/p.relative_to(step2);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy(p,dest)
  parameters(out)
  from generate_final import render
  (out/'Final.lean').write_text(render(json.loads((out/'leaves.json').read_text())))
  from generate_core import render as render_core
  (out/'NodeNC.lean').write_text(render_core((G/'templates/Node.lean').read_text()))
  (out/'CoverageControl.lean').write_text((G/'templates/CoverageControl.lean').read_text())
  bad=[];files=[]
  for dest in sorted(L.rglob('*.lean')):
   rel=dest.relative_to(L)
   if not generated(rel):continue
   src=out/rel
   if not src.exists():raise FileNotFoundError(rel)
   expected=rename(src.read_text()).encode();files.append(str(rel))
   if args.check:
    if dest.read_bytes()!=expected:
     if not bad:print(''.join(difflib.unified_diff(dest.read_text().splitlines(True),expected.decode().splitlines(True)))[:2500],flush=True)
     bad.append(str(rel))
   else:dest.write_bytes(expected)
  if bad:raise SystemExit('Generated files differ: '+', '.join(bad))
  # The importer forward fixtures are Python regression data, not proof premises.
  fixture=G/'agreement.json'
  if args.check:
   if fixture.read_bytes()!=(out/'agreement.json').read_bytes():raise SystemExit('agreement.json differs')
  else:shutil.copy(out/'agreement.json',fixture)
  print(json.dumps({'stage':'regenerate','label':'measured','check':args.check,'files':len(files),'status':'pass'}))
if __name__=='__main__':main()
