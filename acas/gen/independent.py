#!/usr/bin/env python3
"""Re-emit and independently check all receipts; exercise deliberate stale-receipt failures."""
import copy,hashlib,json,subprocess,sys,tempfile,time
from pathlib import Path
A=Path(__file__).resolve().parents[1];G=A/'gen'
def main():
 cert=A/'producer/certificate.json';c=json.loads(cert.read_text());leaves=[i for i,n in enumerate(c['nodes']) if n.get('terminal')]
 out=A/'work/independent';out.mkdir(parents=True,exist_ok=True);start=time.monotonic();results=[]
 with tempfile.TemporaryDirectory(prefix='receipts-',dir=out) as temp:
  root=Path(temp);(root/'Net.lean').write_bytes((A/'lean/ACASChecked/Net.lean').read_bytes())
  def invoke(name):
   p=subprocess.run([sys.executable,str(root/name)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
   return p
  verifier=(G/'legacy/verify.py').read_text().replace('../w2-producer/work/cert-supported-crown-1_1-p1.json',str(cert))
  (root/'verify.py').write_text(verifier)
  saved={}
  for node in leaves:
   s=(G/'legacy/emit.py').read_text().replace('../w2-producer/work/cert-supported-crown-1_1-p1.json',str(cert)).replace("c['nodes'][38]",f"c['nodes'][{node}]")
   (root/'emit.py').write_text(s);p=invoke('emit.py')
   if p.returncode:raise RuntimeError(p.stdout)
   p=invoke('verify.py')
   if p.returncode:raise RuntimeError(p.stdout)
   results.append(dict(node=node,status='pass',receipt_sha256=hashlib.sha256((root/'receipt.json').read_bytes()).hexdigest(),output=p.stdout.strip()))
   if node in [8,13]:saved[node]=json.loads((root/'receipt.json').read_text())
  # The clean twins have just passed with the same interpreter and exact checker.
  tests=[]
  r=copy.deepcopy(saved[8]);r['blocks'][0]['v'][0][0]+=1
  tests.append(('corrupted-dual',r,verifier,'assert nu=='))
  r=copy.deepcopy(saved[8]);r['witnesses'][0]['products'][0][0]+=1
  tests.append(('corrupted-product',r,verifier,'assert p=='))
  mutation=A/'producer/crownint-weight-mutation.json'
  tests.append(('real-unsafe-weight',saved[13],verifier.replace(str(cert),str(mutation)),'assert p=='))
  # The unsafe output weight changes the residual bound rather than an earlier W^T nu.
  for name,r,code,expected in tests:
   (root/'receipt.json').write_text(json.dumps(r));(root/'verify.py').write_text(code);p=invoke('verify.py')
   if p.returncode==0 or 'AssertionError' not in p.stdout:raise RuntimeError((name,p.stdout))
   if name=='real-unsafe-weight':
    # The changed output objective is tested in the endpoint/kink residual inequalities.
    assert 'assert m<=' in p.stdout,p.stdout
   else:assert expected in p.stdout,p.stdout
   results.append(dict(control=name,status='rejected',reason=p.stdout.strip()))
 result=dict(stage='independent-receipts',label='measured',accepted_leaves=len(leaves),results=results,wall_s=time.monotonic()-start)
 (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
