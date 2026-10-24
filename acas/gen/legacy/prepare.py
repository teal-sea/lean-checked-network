import json, pathlib, subprocess, sys, re, shutil, os
P=pathlib.Path; root=P.cwd(); cert=root.parent/'w2-producer/work/cert-supported-crown-1_1-p1.json'
c=json.loads(cert.read_text()); leaves=[i for i,n in enumerate(c['nodes']) if n.get('terminal')]; assert len(leaves)==34
(root/'leaves.json').write_text(json.dumps(leaves))
for i in leaves:
 d=root/f'N{i}'; d.mkdir(exist_ok=True); shutil.copy(root/'Net.lean',d/'Net.lean')
 for p in (root/'templates').glob('*.py'): shutil.copy(p,d/p.name)
 for name in ['emit.py','verify.py','gen-node.py']:
  p=d/name;s=p.read_text().replace('../w2-producer/work/cert-supported-crown-1_1-p1.json',str(cert)).replace("c['nodes'][38]",f"c['nodes'][{i}]");p.write_text(s)
 for name in ['Node.lean','Accept.lean','ShapeNC.lean']:
  shutil.copy(root.parent/'route-a'/name,d/name)
 for script in ['emit.py','verify.py','gen.py','gen-node.py','gen-variants.py','gen-chunks.py']:
  r=subprocess.run([sys.executable,script],cwd=d,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (d/(script+'.log')).write_bytes(r.stdout)
  if r.returncode: raise RuntimeError((i,script,r.stdout.decode()))
 # Share only weights; all per-leaf numerical claims and duals remain separate.
 weights='import Block\nnamespace SharedWeights\n'
 for k in range(6):
  p=d/f'DataNC{k}.lean';s=p.read_text(); lines=s.splitlines(True);wlines=[l for l in lines if l.startswith('noncomputable def w')];weights+=''.join(wlines)
  s=''.join(l for l in lines if l not in wlines).replace('import Block','import Weights').replace('namespace RouteNC','namespace RouteNC\nopen SharedWeights')
  p.write_text(s)
 weights+='end SharedWeights\n'
 if i==leaves[0]:(root/'Weights.lean').write_text(weights)
 else: assert weights==(root/'Weights.lean').read_text()
 selected=[*(f'DataNC{k}' for k in range(6)),*(f'PackedNC{k}' for k in range(6)),'NodeDataNC','ShapeNC',*(f'ChunkNC{k}' for k in range(6)),*(f'EndpointNC{k}' for k in range(6)),'MarginNC','AcceptNC']
 for m in selected:
  p=d/(m+'.lean');s=p.read_text().replace('RouteNC',f'Leaf{i}').replace('node38NC',f'node{i}NC').replace(f'namespace Leaf{i}\n',f'namespace Leaf{i}\nopen SharedWeights\n')
  lines=s.splitlines();imports=[l for l in lines if l.startswith('import ')];body=[l for l in lines if not l.startswith('import ')]
  imports=[('import '+f'N{i}.'+l[7:]) if l[7:] in selected else l for l in imports]
  # Data namespace stays top-level; theorem namespaces prevent name collisions.
  if m=='NodeDataNC': body=[l.replace('open RouteA','open RouteA RouteNC SharedWeights') for l in body]
  if m.startswith('DataNC') or m=='NodeDataNC': out='\n'.join(imports+body)+'\n'
  else: out='\n'.join(imports)+f'\nnamespace Proof{i}\nopen SharedWeights\n'+'\n'.join(body)+f'\nend Proof{i}\n'
  p.write_text(out)
 # Keep only final proof sources and reproducible generator inputs; discard huge duplicated drafts.
 for p in d.glob('*.lean'):
  if p.stem not in selected: p.unlink()
 with (root/'runs.jsonl').open('a') as f:
  for line in (d/'runs.jsonl').read_text().splitlines():
   a=json.loads(line);a['leaf']=i;f.write(json.dumps(a)+'\n')
 print(i,flush=True)
