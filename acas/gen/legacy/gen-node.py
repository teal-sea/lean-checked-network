exec(open('gen.py').read().split('for k,bl')[0])
c=json.load(open('../w2-producer/work/cert-supported-crown-1_1-p1.json'))
Q=r['Q'];from fractions import Fraction as F
b=[[int(F(x)*Q) for x in layer['b']] for layer in c['layers']]
s='import Node\n'+''.join(f'import Data{k}\n' for k in range(6))+'\nnamespace RouteA\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
for k in range(7):s+=f'def b{k} : List Int := {lit(b[k])}\n'
for k in range(6):
 s+=f'def lo{k} : List Int := {lit([p[0] for p in r["pre"][k]])}\ndef hi{k} : List Int := {lit([p[1] for p in r["pre"][k]])}\n'
s+=f'def boxl : List Int := {lit(r["box"][0])}\ndef boxu : List Int := {lit(r["box"][1])}\n'
s+=f'def afinal : List (List Int) := {lit([[-int(F(x)*Q)*Q] for x in c["layers"][6]["w"][0]])}\n'
for k in reversed(range(6)):
 a='afinal' if k==5 else f'(appendRows (rowsSign w{k+1}) c{k+1})'
 base='(scale (Int.neg (Int.mul Q Q)) (b6.take 1))' if k==5 else f'((scale (Int.mul Q Q) (signs b{k+1})) ++ s{k+1})'
 s+=f'noncomputable def s{k} : List Int := addV {base} (contrib lo{k} hi{k} b{k} {a} v{k})\n'
s+='noncomputable def claims := addV s0 (inputCost boxl boxu c0)\n'
for k in range(6):
 ins='boxl boxu' if k==0 else f'(nonneg lo{k-1}) (nonneg hi{k-1})'
 s+=f'noncomputable def endpoints{k} := checkEndpoints lo{k} hi{k} (transpose w{k}) b{k} {ins} (claims.drop {max(0,k-1)*100}) '+('true' if k==0 else 'false')+'\n'
s+='noncomputable def marginCheck := decide (Int.add (Int.mul (claims.getD 500 0) 1000000000000000) (Int.mul 3991125645861615 (Int.mul Q (Int.mul Q Q))) > 0)\n'
s+='def supplied : List Int := '+lit([h['bound'] for h in r['witnesses']])+'\nend RouteA\n';Path('NodeData.lean').write_text(s)
Path('Balances.lean').write_text('import NodeData\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem balances : RouteA.claims = RouteA.supplied := by decide +kernel\n#print axioms balances\n')
for k in range(6):
 Path(f'Endpoint{k}.lean').write_text(f'import Balances\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem endpoints{k} : RouteA.endpoints{k} = true := by\n unfold RouteA.endpoints{k}\n rw [balances]\n decide +kernel\n#print axioms endpoints{k}\n')
Path('Margin.lean').write_text('import Balances\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ntheorem margin : RouteA.marginCheck = true := by\n unfold RouteA.marginCheck\n rw [balances]\n decide +kernel\n#print axioms margin\n')
