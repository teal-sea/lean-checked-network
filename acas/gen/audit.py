#!/usr/bin/env python3
"""Audit new source tokens, the frozen statement, and the final theorem's axiom log."""
import argparse,hashlib,json,re
from pathlib import Path
A=Path(__file__).resolve().parents[1];L=A/'lean/ACASChecked'
def source_audit():
 forbidden=r'\b(sorry|admit|native_decide|implemented_by|axiom|ofReduceBool|trustCompiler)\b'
 bad=[]
 for p in sorted(L.rglob('*.lean')):
  for m in re.finditer(forbidden,p.read_text()):bad.append((str(p.relative_to(A)),m[0]))
 if bad:raise ValueError(bad)
 original=(L/'Spec.lean').read_bytes().replace(b'import ACASChecked.Net',b'import Net')
 assert hashlib.sha256(original).hexdigest()=='fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0'
 assert hashlib.sha256((L/'Net.lean').read_bytes()).hexdigest()=='4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426'
 return dict(stage='source-audit',status='pass',label='measured',modules=len(list(L.rglob('*.lean'))),frozen_statement_restored_sha256=hashlib.sha256(original).hexdigest())
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--build',type=Path,default=A/'work/build');args=ap.parse_args();result=source_audit()
 state=json.loads((args.build/'state.json').read_text());entry=state['ACASChecked.Final']
 logs=[Path(x['log']) for x in entry['outcomes'] if x['phase']=='compile']
 if not logs:raise ValueError('no final compilation log in build state')
 line=next(line for line in logs[-1].read_text().splitlines() if "'ACASChecked.acas_1_1_property1' depends on axioms:" in line)
 axioms=re.search(r'\[(.*)\]',line)[1].split(', ')
 assert len(axioms)==3 and set(axioms)=={'propext','Classical.choice','Quot.sound'},axioms
 result.update(axiom_line=line,axioms=axioms)
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
