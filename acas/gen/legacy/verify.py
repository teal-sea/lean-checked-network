# Independent receipt replay: no optimization or slope reconstruction.
import json,time
from fractions import Fraction as F
start=time.process_time();r=json.load(open('receipt.json'));c=json.load(open('../w2-producer/work/cert-supported-crown-1_1-p1.json'));Q=r['Q']
W=[[[int(F(x)*Q) for x in row] for row in l['w']] for l in c['layers']];b=[[int(F(x)*Q) for x in l['b']] for l in c['layers']]
pre=[]; idx=0; counts=[0]*6
for t in range(7):
 if t<6:
  inputs=list(zip(*r['box'])) if not t else [(max(0,l),max(0,u)) for l,u in pre[-1]];ends=[]
  for j,row in enumerate(W[t]):
   ll=b[t][j]*Q+sum(min(w*l,w*u) for w,(l,u) in zip(row,inputs));uu=b[t][j]*Q+sum(max(w*l,w*u) for w,(l,u) in zip(row,inputs))
   il=ll//Q;iu=-((-uu)//Q);assert r['ibp'][t][j]==[il,iu]
   if t:
    bounds=[]
    for sign in [1,-1]:
     h=r['witnesses'][idx];idx+=1
     assert (h['t'],h['j'],h['sign'])==(t,j,sign)
     total=sign*b[t][j]*Q**2
     for k,(nu,p,mm) in enumerate(zip(h['nu'],h['products'],h['mins'])):
      a=[sign*w*Q for w in W[t][j]] if k==t-1 else h['products'][k+1]
      assert p==[sum(row[d]*n for row,n in zip(W[k],nu)) for d in range(len(W[k][0]))]
      bl=r['blocks'][k];col=counts[k];counts[k]+=1
      assert nu==[row[col] for row in bl['v']] and p==[row[col] for row in bl['c']]
      for aa,n,m,(l,u),bb in zip(a,nu,mm,pre[k],b[k]):
       assert m<=aa*max(0,l)-n*l*Q and m<=aa*max(0,u)-n*u*Q
       if l<=0<=u: assert m<=0
       total+=n*bb*Q+m
     total+=sum(min(a*l,a*u) for a,l,u in zip(h['products'][0],*r['box']));assert total==h['bound'];bounds.append(total)
    il=max(il,bounds[0]//Q**2);iu=min(iu,-(bounds[1]//Q**2))
   assert [il,iu]==r['pre'][t][j] and il<=iu;ends.append([il,iu])
  pre.append(ends)
# Final same residual rule, all domains established.
h=r['witnesses'][idx];assert h['t']==6 and h['sign']==-1
s=-b[6][0]*Q**2
for k,(nu,p,mm) in enumerate(zip(h['nu'],h['products'],h['mins'])):
 a=[-w*Q for w in W[6][0]] if k==5 else h['products'][k+1]
 assert p==[sum(row[d]*n for row,n in zip(W[k],nu)) for d in range(len(W[k][0]))]
 bl=r['blocks'][k];col=counts[k];counts[k]+=1
 assert nu==[row[col] for row in bl['v']] and p==[row[col] for row in bl['c']]
 for aa,n,m,(l,u),bb in zip(a,nu,mm,pre[k],b[k]):
  assert m<=aa*max(0,l)-n*l*Q and m<=aa*max(0,u)-n*u*Q
  if l<=0<=u:assert m<=0
  s+=n*bb*Q+m
s+=sum(min(a*l,a*u) for a,l,u in zip(h['products'][0],*r['box']))
assert s==h['bound'];margin=F(s,Q**3)+F('3.991125645861615');assert margin==F(r['margin']) and margin>0
result=dict(experiment='independent_receipt_check',accept=True,cpu_s=time.process_time()-start,margin=str(margin),columns=counts)
open('runs.jsonl','a').write(json.dumps(result)+'\n');print(result)
