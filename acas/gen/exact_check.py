"""Independent exact ACAS box certificate replay. Checking path uses stdlib only.
Bounds are over real arithmetic with exact binary32 parameters, not IEEE execution.
Each scalar arithmetic call is counted, with both operand numerator/denominator bits.
Fixed precision uses directed rounding after EVERY scalar operation. Interval-valued
backward coefficients retain soundness when coefficient arithmetic is rounded.
"""
from fractions import Fraction as F
import json,time,collections,argparse,copy
class Arithmetic:
    def __init__(self,p=None):
        self.p=p;self.scale=1<<p if p else None;self.count=collections.Counter();self.hist=collections.Counter();self.maxbits=0
    def record(self,op,*args):
        self.count[op]+=1
        for x in args:
            for n in (x.numerator,x.denominator):
                b=abs(n).bit_length();self.hist[b]+=1;self.maxbits=max(self.maxbits,b)
    def cmp(self,x,y):
        self.record('compare',x,y);return (x>y)-(x<y)
    def op(self,op,x,y,up=False):
        self.record(op,x,y)
        if op=='add': z=x+y
        elif op=='sub':z=x-y
        elif op=='mul':z=x*y
        else:z=x/y
        # Count result width too: raw products/divisions can exceed rounded width.
        for n in (z.numerator,z.denominator):self.maxbits=max(self.maxbits,abs(n).bit_length())
        if self.p:
            n=z.numerator*self.scale;d=z.denominator
            self.maxbits=max(self.maxbits,abs(n).bit_length(),d.bit_length())
            z=F(-((-n)//d) if up else n//d,self.scale)
            self.count['round_up' if up else 'round_down']+=1
        return z
    def add(self,x,y):return (self.op('add',x[0],y[0]),self.op('add',x[1],y[1],True))
    def mul(self,x,y):
        # Endpoint enumeration also valid when intervals cross zero.
        ls=[self.op('mul',a,b) for a in x for b in y];us=[self.op('mul',a,b,True) for a in x for b in y]
        for v in ls[1:]: self.cmp(v,ls[0])
        for v in us[1:]: self.cmp(v,us[0])
        return min(ls),max(us)
    def scale_by(self,x,w):
        if self.cmp(w,F(0))>=0:return self.op('mul',x[0],w),self.op('mul',x[1],w,True)
        return self.op('mul',x[1],w),self.op('mul',x[0],w,True)
    def stats(self):return {'operations':dict(self.count),'operand_bit_histogram':dict(sorted(self.hist.items())),'largest_integer_bits':self.maxbits}
def pair(x): x=F(x);return x,x
def tree_check(cert):
    if not cert['complete']:raise ValueError('incomplete certificate')
    nodes=cert['nodes'];seen=set();leaves=[]
    def visit(i,expected):
        if not isinstance(i,int) or not 0<=i<len(nodes) or i in seen:raise ValueError('invalid tree index')
        seen.add(i);n=nodes[i];box=[[F(v) for v in row] for row in n['box']]
        if box!=expected:raise ValueError('box mismatch / gap')
        if n.get('terminal'):
            if 'children' in n:raise ValueError('ambiguous terminal')
            leaves.append(i);return
        d=n['dim'];cut=F(n['cut'])
        if not 0<=d<len(box[0]) or not box[0][d]<cut<box[1][d]:raise ValueError('invalid split')
        left=copy.deepcopy(box);right=copy.deepcopy(box);left[1][d]=cut;right[0][d]=cut
        if len(n['children'])!=2:raise ValueError('missing child')
        visit(n['children'][0],left);visit(n['children'][1],right)
    root=[[F(v) for v in row] for row in cert['root']]
    # Decimal benchmark region must be enclosed by binary32 root.
    lo,hi=cert['manifest']['decimal_box']
    if not all(root[0][i]<=F(lo[i])<=F(hi[i])<=root[1][i] for i in range(len(lo))):raise ValueError('root misses benchmark')
    visit(0,root)
    if len(seen)!=len(nodes):raise ValueError('unreachable nodes')
    return leaves

def replay(cert,node,ar):
    layers=cert['layers'];x=list(zip(*[[F(v) for v in row] for row in node['box']]));pre=[]
    # Exact/directed IBP independent of exported floating bounds.
    for layer in layers[:-1]:
        z=[]
        for row,b in zip(layer['w'],layer['b']):
            acc=pair(b)
            for w,v in zip(row,x):acc=ar.add(acc,ar.scale_by(v,F(w)))
            z.append(acc)
        pre.append(z);x=[]
        for l,u in z:
            ar.cmp(l,F(0));ar.cmp(u,F(0));x.append((max(F(0),l),max(F(0),u)))
    return backward(layers,pre,node['box'],cert['c'][node['objective']],
                    -F(cert['rhs'][node['objective']]),node['alphas'],ar)

def backward(layers,pre,box,objective,offset,alphas,ar):
    coeff=[pair(v) for v in objective];bias=pair(offset)
    for t in reversed(range(len(layers))):
        layer=layers[t]
        active=[(a,row,b) for a,row,b in zip(coeff,layer['w'],layer['b']) if a != pair(0)]
        for a,row,b in active:bias=ar.add(bias,ar.scale_by(a,F(b)))
        new=[]
        for j in range(len(layer['w'][0])):
            acc=pair(0)
            for a,row,b in active:acc=ar.add(acc,ar.scale_by(a,F(row[j])))
            new.append(acc)
        coeff=new
        if t:
            for j,((l,u),a) in enumerate(zip(pre[t-1],coeff)):
                if ar.cmp(u,F(0))<=0:coeff[j]=pair(0)
                elif ar.cmp(l,F(0))>=0:pass
                else:
                    alpha=F(alphas[t-1][j])
                    if not 0<=alpha<=1:raise ValueError('alpha outside [0,1]')
                    # upper ReLU secant u/(u-l), intercept -l*u/(u-l).
                    # Compute exact rational secant for the sound IBP endpoints,
                    # then enclose arithmetic; no unchecked float relaxation.
                    denlo=ar.op('sub',u,l);denhi=ar.op('sub',u,l,True)
                    slope=(ar.op('div',u,denhi),ar.op('div',u,denlo,True))
                    intercept=ar.scale_by(slope,-l)
                    # Split coefficient interval by sign; enclosing both cases is sound.
                    if ar.cmp(a[0],F(0))>=0: coeff[j]=ar.scale_by(a,alpha)
                    elif ar.cmp(a[1],F(0))<=0:
                        bias=ar.add(bias,ar.mul(a,intercept));coeff[j]=ar.mul(a,slope)
                    else:
                        neg=(a[0],F(0));pos=(F(0),a[1]);nb=ar.mul(neg,intercept);bias=ar.add(bias,(min(F(0),nb[0]),max(F(0),nb[1])))
                        n=ar.mul(neg,slope);p=ar.scale_by(pos,alpha);coeff[j]=(min(n[0],p[0]),max(n[1],p[1]))
    for a,v in zip(coeff,zip(*[[F(v) for v in row] for row in box])):bias=ar.add(bias,ar.mul(a,v))
    return bias[0]
def crown_intermediates(cert,node,ar,mode='crown',trace=None):
    layers=cert['layers'];pre=[]
    for t,layer in enumerate(layers[:-1]):
        # Identity objectives give independent preactivation lower/upper proofs.
        # The first affine layer is exactly interval propagation.
        bounds=[]
        adaptive=[[int(u > -l) for l,u in z] for z in pre]
        inputs=list(zip(*[[F(v) for v in row] for row in node['box']])) if t==0 else [(max(F(0),l),max(F(0),u)) for l,u in pre[-1]]
        ibp=[]
        for row,b in zip(layer['w'],layer['b']):
            acc=pair(b)
            for w,v in zip(row,inputs):acc=ar.add(acc,ar.scale_by(v,F(w)))
            ibp.append(acc)
        for j in range(len(layer['b'])):
            if t==0:
                bounds.append(ibp[j]);continue
            ends=[]
            for side,sign in enumerate((1,-1)):
                slopes=adaptive
                if mode=='crown-alpha':
                    slopes=node['intermediate_alphas'][t][side][j]
                objective=[0]*len(layer['b']);objective[j]=sign
                ends.append(backward(layers[:t+1],pre,node['box'],objective,0,slopes,ar))
            bounds.append((max(ends[0],ibp[j][0]),min(-ends[1],ibp[j][1])))
        if 'intermediate_bounds' in node:
            claimed=node['intermediate_bounds'][t]
            if len(claimed)!=len(bounds):raise ValueError('intermediate bound shape')
            scale=1 << cert['endpoint_scale_bits']
            carried=[]
            for (l,u),ends in zip(bounds,claimed):
                if len(ends)!=2 or not all(isinstance(v,int) for v in ends):
                    raise ValueError('intermediate bound encoding')
                cl,cu=(F(v,scale) for v in ends)
                if not cl<=l<=u<=cu:raise ValueError('unproved intermediate endpoint')
                carried.append((cl,cu))
            bounds=carried
        pre.append(bounds)
        if trace is not None:trace.append([[str(l),str(u)] for l,u in bounds])
    return pre

def replay_crown(cert,node,ar,mode='crown',trace=None):
    pre=crown_intermediates(cert,node,ar,mode,trace)
    return backward(cert['layers'],pre,node['box'],cert['c'][node['objective']],
                    -F(cert['rhs'][node['objective']]),node['alphas'],ar)

def run(cert,p=None,mode="ibp"):
    leaves=tree_check(cert);ar=Arithmetic(p);start=time.monotonic();margins=[]
    for i in leaves:
        margin=(replay(cert,cert['nodes'][i],ar) if mode=='ibp' else replay_crown(cert,cert['nodes'][i],ar,mode));margins.append(margin)
    return {'experiment':'exact_check','precision':p or 'Fraction','leaves':len(leaves),'passed':sum(m>0 for m in margins),'failed':sum(m<=0 for m in margins),'min_margin':str(min(margins)),'min_margin_float':float(min(margins)),'failure_margins':[str(m) for m in margins if m<=0],'seconds':time.monotonic()-start,**ar.stats()}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate');p.add_argument('--precision',default='exact');p.add_argument('--output');p.add_argument('--intermediate',choices=['ibp','crown','crown-alpha'],default='ibp');args=p.parse_args();cert=json.load(open(args.certificate));result=run(cert,None if args.precision=='exact' else int(args.precision),args.intermediate);result['certificate']=args.certificate
    output=json.dumps(result);print(output);open('runs.jsonl','a').write(output+'\n')
    if args.output:open(args.output,'w').write(output+'\n')
