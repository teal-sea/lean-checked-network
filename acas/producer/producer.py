"""Restricted CPU input-split producer using pinned alpha-beta-CROWN auto_LiRPA.
Exports before discarding accepted boxes. No clipping, attacks, beta or cuts.
"""
import os,sys,time,json,gzip,re,hashlib,struct,zlib
os.environ['OMP_NUM_THREADS']='8'
sys.path.insert(0,os.path.abspath('abc/auto_LiRPA'))
import torch,onnx
from onnx import numpy_helper
from auto_LiRPA import BoundedModule,BoundedTensor
from auto_LiRPA.perturbations import PerturbationLpNorm
torch.set_num_threads(8)
def load(net,prop):
    base='benchmarks/benchmarks/acasxu/'
    raw=gzip.open(base+f'onnx/ACASXU_run2a_{net}_batch_2000.onnx.gz','rb').read()
    m=onnx.load_model_from_string(raw); vals={v.name:numpy_helper.to_array(v).copy() for v in m.graph.initializer}
    assert not vals['input_AvgImg'].any()
    layers=[]; modules=[]
    for node in m.graph.node:
        if node.op_type=='MatMul':
            w=vals[node.input[1]].T; layers.append({'w':w.tolist()})
        elif node.op_type=='Add':
            b=vals[node.input[1]]; layers[-1]['b']=b.tolist()
            lin=torch.nn.Linear(len(layers[-1]['w'][0]),len(b)); lin.weight.data.copy_(torch.tensor(layers[-1]['w'])); lin.bias.data.copy_(torch.tensor(b)); modules.append(lin)
        elif node.op_type=='Relu': modules.append(torch.nn.ReLU())
        else: assert node.op_type in ['Sub','Flatten']
    spec=gzip.open(base+f'vnnlib/prop_{prop}.vnnlib.gz','rt').read()
    lo=[None]*5;hi=[None]*5
    for op,i,v in re.findall(r'\(assert \((<=|>=) X_(\d) ([-\d.]+)\)\)',spec):
        (hi if op=='<=' else lo)[int(i)]=v
    # Outward binary32 enclosure of decimal VNNLIB bounds, never inward cast.
    from fractions import Fraction as F
    def outward(v,lower):
        x=torch.tensor(float(v),dtype=torch.float32)
        if (F(float(x))>F(v)) if lower else (F(float(x))<F(v)):
            x=torch.nextafter(x,torch.tensor(-float('inf') if lower else float('inf')))
        return float(x)
    box=[[outward(v,True) for v in lo],[outward(v,False) for v in hi]]
    if prop==1: c=[[-1.,0,0,0,0]];rhs=[-3.991125] # overridden from exact property text below
    elif prop in [3,4]: c=[[1. if j==0 else -1. if j==i else 0. for j in range(5)] for i in range(1,5)];rhs=[0.]*4
    else: raise ValueError('supported properties 1,3,4')
    if prop==1:
        threshold=re.search(r'\(assert \(>= Y_0 ([\d.]+)\)\)',spec).group(1);rhs=[-float(threshold)]
    return torch.nn.Sequential(*modules).eval(),layers,box,c,rhs,{'onnx_sha256':hashlib.sha256(raw).hexdigest(),'vnnlib':spec,'decimal_box':[lo,hi]}
def main():
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--net',default='1_1');p.add_argument('--prop',type=int,default=3);p.add_argument('--max-leaves',type=int,default=4096);p.add_argument('--iterations',type=int,default=10);p.add_argument('--out',default='cert.json');args=p.parse_args()
    model,layers,root,c,rhs,manifest=load(args.net,args.prop)
    bm=BoundedModule(model,torch.zeros(1,5),bound_opts={'sparse_features_alpha':False,'sparse_spec_alpha':False,'sparse_intermediate_bounds':False,'optimize_bound_args':{'iteration':args.iterations,'enable_alpha_crown':True,'fix_interm_bounds':True}},device='cpu')
    relus=[n for n in bm.nodes() if n.__class__.__name__=='BoundRelu']
    cert={'schema':'restricted-acas-box-v1','manifest':manifest,'layers':layers,'root':root,'c':c,'rhs':rhs,'nodes':[{'box':root}],'net':args.net,'prop':args.prop}
    todo=[0];start=time.monotonic();accepted=0;calls=0
    while todo and len(cert['nodes'])<args.max_leaves*2:
        idx=todo.pop();node=cert['nodes'][idx];lo,hi=node['box'];l=torch.tensor([lo]);u=torch.tensor([hi]);x=BoundedTensor((l+u)/2,PerturbationLpNorm(norm=float('inf'),x_L=l,x_U=u));C=torch.tensor([c])
        # Explicit IBP intermediate bounds, frozen during alpha optimisation.
        bm.compute_bounds(x=(x,),method='IBP')
        interm={r.inputs[0].name:(r.inputs[0].lower.detach().clone(),r.inputs[0].upper.detach().clone()) for r in relus}
        needed={bm.output_name[0]:[bm.input_name[0]]}
        lb,_,ad=bm.compute_bounds(x=(x,),C=C,method='CROWN-Optimized',bound_upper=False,return_A=True,needed_A_dict=needed,interm_bounds=interm)
        calls+=1; scores=lb[0]-torch.tensor(rhs);best=int(scores.argmax()); margin=float(scores[best]);node['producer_margin']=margin
        if margin>0:
            a=ad[bm.output_name[0]][bm.input_name[0]]
            node.update({'terminal':True,'objective':best,'A':a['lA'][0,best].detach().tolist(),'b':float(a['lbias'][0,best]),'alphas':[r.alpha[bm.output_name[0]][0,best,0].detach().tolist() for r in relus]});accepted+=1
        else:
            # Widest relative coordinate; cyclic balanced splitting follows widths.
            dim=max(range(5),key=lambda d:hi[d]-lo[d])
            cut=float(torch.tensor((lo[dim]+hi[dim])/2,dtype=torch.float32));assert lo[dim]<cut<hi[dim]
            left=[lo.copy(),hi.copy()];right=[lo.copy(),hi.copy()];left[1][dim]=cut;right[0][dim]=cut
            children=[len(cert['nodes']),len(cert['nodes'])+1];node.update({'dim':dim,'cut':cut,'children':children});cert['nodes'].extend([{'box':left},{'box':right}]);todo.extend(reversed(children))
        if calls%10==0: print(json.dumps({'calls':calls,'accepted':accepted,'pending':len(todo),'seconds':time.monotonic()-start}),flush=True)
    cert['producer_seconds']=time.monotonic()-start;cert['complete']=not todo;cert['calls']=calls
    data=json.dumps(cert,separators=(',',':')).encode();open(args.out,'wb').write(data);open(args.out+'.zlib','wb').write(zlib.compress(data,9))
    result={'experiment':'producer','net':args.net,'prop':args.prop,'seconds':cert['producer_seconds'],'calls':calls,'leaves':accepted,'complete':not todo,'json_bytes':len(data),'zlib_bytes':len(zlib.compress(data,9))}
    print(json.dumps(result),flush=True);open('runs.jsonl','a').write(json.dumps(result)+'\n')
if __name__=='__main__':main()
