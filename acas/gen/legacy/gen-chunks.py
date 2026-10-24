from pathlib import Path
s=Path('NodeDataNC.lean').read_text().replace('(scale (Int.neg (Int.mul Q Q)) b6)','(scale (Int.neg (Int.mul Q Q)) (b6.take 1))')
for k in range(6):s=s.replace(f'(claims.drop {max(0,k-1)*100})',f'((claims.drop {max(0,k-1)*100}).take 100)')
s=s.replace('(claims.getD 500 0)', '(((claims.drop 500).take 1).headD 0)')
Path('NodeDataNC.lean').write_text(s)
for j in range(6):
 n=100 if j<5 else 1;offset=100*j
 expr=f'(RouteNC.claims.drop {offset}).take {n}';sup=f'(RouteNC.supplied.drop {offset}).take {n}'
 out=f'''import NodeDataNC
import SameSpec
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool{j} : RouteA.same ({expr}) ({sup}) = true := by decide +kernel
theorem chunk{j} : {expr} = {sup} := RouteA.same_spec _ _ chunkBool{j}
#print axioms chunk{j}
'''
 Path(f'ChunkNC{j}.lean').write_text(out)
for k in range(6):
 if k==0:
  s='''import NodeDataNC
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : RouteNC.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
'''
 else:
  s=f'''import ChunkNC{k-1}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC{k} : RouteNC.endpoints{k} = true := by
 unfold RouteNC.endpoints{k}
 rw [chunk{k-1}]
 decide +kernel
#print axioms endpointsNC{k}
'''
 Path(f'EndpointNC{k}.lean').write_text(s)
s='''import ChunkNC5
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : RouteNC.marginCheck = true := by
 unfold RouteNC.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
''';Path('MarginNC.lean').write_text(s)

p=Path('AcceptNC.lean')
s=p.read_text()
if 'import ShapeNC' not in s:
 s='import ShapeNC\n'+s
 s=s.replace('RouteNC.marginCheck = true :=','RouteNC.marginCheck = true ∧ RouteNC.claims.length = 501 :=').replace(', marginNC⟩',', marginNC, claims_length⟩')
 p.write_text(s)
