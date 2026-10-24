import json
from fractions import Fraction
from pathlib import Path
Q=1<<50
c=json.load(open('../w2-producer/work/cert-supported-crown-1_1-p1.json'))
def z(x):
 a=Fraction(x)*Q;assert a.denominator==1;n=a.numerator
 return f'(Int.ofNat {n})' if n>=0 else f'(Int.negSucc {-n-1})'
def box(b):return '['+','.join(f'({z(l)},{z(u)})' for l,u in zip(*b))+']'
s='import Coverage\nopen TreePilot\nset_option maxHeartbeats 0\ndef root : Box := '+box(c['root'])+'\ndef nodes : Array Node := #[\n'
for n in c['nodes']:
 kind='.leaf' if n.get('terminal') else f'.split {n["dim"]} {z(n["cut"])} {n["children"][0]} {n["children"][1]}'
 s+=f'  ⟨{box(n["box"])}, {kind}⟩,\n'
s=s[:-2]+']\ntheorem coverage_checked : TreePilot.check root nodes = true := by decide +kernel\n#print axioms coverage_checked\n'
Path('CoverageData.lean').write_text(s)
