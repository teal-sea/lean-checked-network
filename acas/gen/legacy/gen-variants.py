from pathlib import Path
import json
s=Path('Node.lean').read_text().replace('namespace RouteA','namespace RouteFast\nopen RouteA').replace('end RouteA','end RouteFast')
a=s.index(' let ml :=');z=s.index('\ndef contrib',a)
s=s[:a]+''' let nq := Int.mul nn Q
 let pos := Int.sub aa nq
 let neg := Int.neg nq
 let ml := Int.mul (if l ≤ 0 then neg else pos) l
 let mu := Int.mul (if u ≤ 0 then neg else pos) u
 if l ≤ 0 ∧ 0 ≤ u then min 0 (min ml mu) else min ml mu) a n
'''+s[z:]
Path('NodeFast.lean').write_text(s)
s=Path('NodeData.lean').read_text().replace('import Node\n','import NodeFast\n').replace('namespace RouteA','namespace RouteFast\nopen RouteA').replace('end RouteA','end RouteFast');Path('NodeDataFast.lean').write_text(s)
s=Path('Balances.lean').read_text().replace('import NodeData','import NodeDataFast').replace('RouteA.','RouteFast.').replace('theorem balances','theorem balancesFast').replace('#print axioms balances','#print axioms balancesFast');Path('BalancesFast.lean').write_text(s)
for k in range(6):
 s=Path(f'Data{k}.lean').read_text().replace('namespace RouteA','namespace RouteNC').replace('end RouteA','end RouteNC').replace('def ','noncomputable def ')
 Path(f'DataNC{k}.lean').write_text(s)
 Path(f'PackedNC{k}.lean').write_text(f'import DataNC{k}\nopen RouteA RouteNC\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem packedNC{k} : block w{k} v{k} c{k} = true := by decide +kernel\n#print axioms packedNC{k}\n')
s=Path('NodeFast.lean').read_text().replace('RouteFast','RouteNC');Path('NodeNC.lean').write_text(s)
s=Path('NodeDataFast.lean').read_text().replace('import NodeFast','import NodeNC').replace('RouteFast','RouteNC')
for k in range(6):s=s.replace(f'import Data{k}\n',f'import DataNC{k}\n')
s=s.replace('\ndef ','\nnoncomputable def ');Path('NodeDataNC.lean').write_text(s)
s=Path('BalancesFast.lean').read_text().replace('NodeDataFast','NodeDataNC').replace('RouteFast','RouteNC').replace('balancesFast','balancesNC');Path('BalancesNC.lean').write_text(s)
for k in range(6):
 s=Path(f'Endpoint{k}.lean').read_text().replace('import Balances','import BalancesNC').replace('RouteA.','RouteNC.').replace('[balances]','[balancesNC]').replace(f'theorem endpoints{k}',f'theorem endpointsNC{k}').replace(f'axioms endpoints{k}',f'axioms endpointsNC{k}')
 Path(f'EndpointNC{k}.lean').write_text(s)
s=Path('Margin.lean').read_text().replace('import Balances','import BalancesNC').replace('RouteA.','RouteNC.').replace('[balances]','[balancesNC]').replace('theorem margin','theorem marginNC').replace('axioms margin','axioms marginNC');Path('MarginNC.lean').write_text(s)
s=Path('Accept.lean').read_text().replace('RouteA.','RouteNC.').replace('open RouteA','open RouteA RouteNC').replace('node38','node38NC')
for k in range(6):s=s.replace(f'import Packed{k}',f'import PackedNC{k}').replace(f'import Endpoint{k}',f'import EndpointNC{k}').replace(f'packed{k},',f'packedNC{k},').replace(f'endpoints{k},',f'endpointsNC{k},')
s=s.replace('import Margin\n','import MarginNC\n').replace(', margin⟩',', marginNC⟩');Path('AcceptNC.lean').write_text(s)
# These changes preserve every literal and list body.
assert all(Path(f'DataNC{k}.lean').read_text().replace('noncomputable def ','def ').replace('RouteNC','RouteA')==Path(f'Data{k}.lean').read_text() for k in range(6))
Path('BalancesNC.lean').write_text('''import NodeDataNC
import SameSpec
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem balanceBoolNC : RouteA.same RouteNC.claims RouteNC.supplied = true := by decide +kernel
theorem balancesNC : RouteNC.claims = RouteNC.supplied := RouteA.same_spec _ _ balanceBoolNC
#print axioms balancesNC
''')
