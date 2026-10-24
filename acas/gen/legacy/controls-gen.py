from pathlib import Path
import json,re
from fractions import Fraction as F
for i,kind in [(8,'Dual'),(17,'Weight')]:
 term='w0 (corrupt Leaf8.v0) Leaf8.c0' if i==8 else '(corrupt w0) Leaf17.v0 Leaf17.c0'
 s=f'''import N{i}.DataNC0
open RouteA SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Control{kind}
noncomputable def corrupt : List (List Int) → List (List Int)
 | [] => []
 | [] :: rs => [] :: rs
 | (x :: xs) :: rs => (Int.add x 1 :: xs) :: rs
theorem rejected : block {term} = false := by decide +kernel
#print axioms rejected
end Control{kind}
'''
 if kind=='Weight':
  rr=json.load(open('N17/receipt.json'));j=next(j for j,row in enumerate(rr['blocks'][0]['v']) if any(row))
  s=s.replace('theorem rejected : block (corrupt w0)',f'noncomputable def changedWeights := w0.set 0 ((w0.headD []).set {j} (Int.add ((w0.headD []).getD {j} 0) 1))\ntheorem rejected : block changedWeights')
 Path(f'Control{kind}.lean').write_text(s)
c=json.load(open('../w2-producer/work/crownint-weight-mutation.json'));r=json.load(open('N13/receipt.json'));q=r['Q']
s=Path('N13/NodeDataNC.lean').read_text().replace('namespace Leaf13','namespace Unsafe13').replace('end Leaf13','end Unsafe13').replace('open RouteA RouteNC SharedWeights','open RouteA RouteNC SharedWeights Leaf13')
row=[-int(F(x)*q)*q for x in c['layers'][6]['w'][0]]
def lit(n):return f'(Int.ofNat {n})' if n>=0 else f'(Int.negSucc {-n-1})'
s=re.sub(r'noncomputable def afinal[^\n]*', 'noncomputable def afinal : List (List Int) := ['+','.join('['+lit(x)+']' for x in row)+']',s)
Path('UnsafeNode13.lean').write_text(s)
Path('UnsafeControl13.lean').write_text('''import UnsafeNode13
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem unsafe13_rejected : Unsafe13.marginCheck = false := by decide +kernel
#print axioms unsafe13_rejected
''')
