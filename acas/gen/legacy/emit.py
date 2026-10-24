import json,time,hashlib,re
from fractions import Fraction as F
from pathlib import Path
start=time.process_time(); Q=1<<50
src=Path('../w2-producer/work/cert-supported-crown-1_1-p1.json'); c=json.loads(src.read_text())
def exact(x):
 y=F(x)*Q; assert y.denominator==1; return y.numerator
W=[[[exact(x) for x in r] for r in l['w']] for l in c['layers']]; b=[[exact(x) for x in l['b']] for l in c['layers']]
frozen=Path('Net.lean').read_text()
for k,l in enumerate(c['layers']):
 for key,vals in [('w',[v for r in l['w'] for v in r]),('b',l['b'])]:
  s=frozen.split(f'def {key}{k} :',1)[1].split('\ndef ',1)[0]
  assert [F(int(a),int(d)) for a,d in re.findall(r'\((-?\d+) / (\d+) : Rat\)',s)]==list(map(F,vals))
box=[[exact(x) for x in r] for r in c['nodes'][38]['box']]; pre=[]; witnesses=[]; Vs=[[] for _ in range(6)]; Cs=[[] for _ in range(6)]
def product(k,v):return [sum(w[j]*n for w,n in zip(W[k],v)) for j in range(len(W[k][0]))]
def witness(t,j,sign):
 # t=6 is final -Y0, otherwise signed preactivation
 a=[sign*x*Q for x in W[t][j]]; total=sign*b[t][j]*Q*Q; ns=[]; ps=[]; mins=[]
 for k in reversed(range(t)):
  nu=[]; mm=[]
  for aa,(l,u) in zip(a,pre[k]):
   if u<=0:n=0
   elif l>=0:n=aa//Q
   elif aa>=0:n=aa//Q if u > -l else 0
   else:n=(aa*u)//((u-l)*Q)
   m=min(aa*max(0,l)-n*l*Q,aa*max(0,u)-n*u*Q,0 if l<=0<=u else 10**200)
   assert m<=aa*max(0,l)-n*l*Q and m<=aa*max(0,u)-n*u*Q
   nu.append(n);mm.append(m)
  p=product(k,nu); Vs[k].append(nu); Cs[k].append(p)
  total+=sum(n*bb*Q+m for n,bb,m in zip(nu,b[k],mm)); ns.append(nu);ps.append(p);mins.append(mm);a=p
 total+=sum(min(r*l,r*u) for r,l,u in zip(a,*box))
 witnesses.append(dict(t=t,j=j,sign=sign,nu=list(reversed(ns)),products=list(reversed(ps)),mins=list(reversed(mins)),bound=total))
 return total
ibps=[]
for t in range(6):
 inputs=list(zip(*box)) if t==0 else [(max(0,l),max(0,u)) for l,u in pre[-1]]
 ibp=[];ends=[]
 for j,(row,bb) in enumerate(zip(W[t],b[t])):
  low=bb*Q+sum(min(w*l,w*u) for w,(l,u) in zip(row,inputs)); high=bb*Q+sum(max(w*l,w*u) for w,(l,u) in zip(row,inputs))
  il=low//Q;iu=-((-high)//Q);ibp.append([il,iu])
  if t:il=max(il,witness(t,j,1)//(Q*Q));iu=min(iu,-(witness(t,j,-1)//(Q*Q)))
  assert il<=iu;ends.append([il,iu])
 ibps.append(ibp);pre.append(ends)
final=witness(6,0,-1);margin=F(final,Q**3)+F('3.991125645861615');assert margin>0
blocks=[]
for k in range(6):
 v=list(map(list,zip(*Vs[k])));p=list(map(list,zip(*Cs[k])));wt=list(map(list,zip(*W[k])))
 assert len(Vs[k])==[501,401,301,201,101,1][k]
 assert all(sum(w*n for w,n in zip(row,col))==p[j][t] for j,row in enumerate(wt) for t,col in enumerate(Vs[k]))
 blocks.append(dict(w=wt,v=v,c=p))
receipt=dict(Q=Q,box=box,pre=pre,ibp=ibps,witnesses=witnesses,blocks=blocks,margin=str(margin))
Path('receipt.json').write_text(json.dumps(receipt,separators=(',',':')))
result=dict(experiment='emitter',status='accept',cpu_s=time.process_time()-start,margin_exact=str(margin),margin_decimal=float(margin),columns=[len(v) for v in Vs],nu_max_bits=max(abs(n).bit_length() for vs in Vs for v in vs for n in v),hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [src,Path('Net.lean'),Path('receipt.json')]})
Path('emitter-result.json').write_text(json.dumps(result,indent=2));open('runs.jsonl','a').write(json.dumps(result)+'\n');print(json.dumps(result,indent=2))
