import json
from pathlib import Path
r=json.load(open('receipt.json'))
def lit(x):
 if isinstance(x,list):return '['+','.join(map(lit,x))+']'
 return '(Int.ofNat '+str(x)+')' if x>=0 else '(Int.negSucc '+str(-x-1)+')'
for k,bl in enumerate(r['blocks']):
 s='import Block\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nnamespace RouteA\n'
 for key in ('w','v','c'):
  for i,row in enumerate(bl[key]):s+=f'def {key}{k}r{i} : List Int := {lit(row)}\n'
  s+=f'def {key}{k} : List (List Int) := ['+','.join(f'{key}{k}r{i}' for i in range(len(bl[key])))+']\n'
 s+='end RouteA\n';Path(f'Data{k}.lean').write_text(s)
 for mode in ('Packed','Scalar'):
  ck='block' if mode=='Packed' else 'scalar'
  Path(f'{mode}{k}.lean').write_text(f'import Data{k}\nopen RouteA\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem {mode.lower()}{k} : {ck} w{k} v{k} c{k} = true := by decide +kernel\n#print axioms {mode.lower()}{k}\n')
Path('Controls.lean').write_text('''import Data0
open RouteA
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def corrupt : List (List Int) → List (List Int)
 | [] => []
 | [] :: rs => [] :: rs
 | (x :: xs) :: rs => (Int.add x 1 :: xs) :: rs
theorem badC : block w0 v0 (corrupt c0) = false := by decide +kernel
theorem badW : block (corrupt w0) v0 c0 = false := by decide +kernel
#print axioms badC
#print axioms badW
''')
