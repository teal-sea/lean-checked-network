"""Normalize actual CLI event stream into explicit binary covering tree."""
import json,sys,os,zlib,time
from producer import load

def flat(x):
 if not isinstance(x,list):return [x]
 return [v for y in x for v in flat(y)]
def key(box):return tuple(tuple(flat(r)) for r in box)
def main():
 events,out,net=sys.argv[1:];model,layers,_,cs,rhs,manifest=load(net,1)
 # Check the original exact decimal threshold, not the CLI's rounded RHS.
 import re
 rhs=[str(-__import__('fractions').Fraction(re.search(r'\(assert \(>= Y_0 ([\d.]+)\)\)',manifest['vnnlib']).group(1)))]
 nodes=[];indices={};bounds={}
 def add(box):
  box=[flat(r) for r in box];k=key(box)
  if k not in indices:indices[k]=len(nodes);nodes.append({'box':box})
  return indices[k]
 for line in open(events):
  e=json.loads(line)
  if e['event']=='bound':
   for i in range(len(e['x_L'])):
    box=[flat(e['x_L'][i]),flat(e['x_U'][i])];add(box);bounds[key(box)]=(e,i)
  elif e['event']=='binary_split':
   assert e['partitions']==2
   batch=len(e['parent_L'])
   for i in range(batch):
    parent=[e['parent_L'][i],e['parent_U'][i]];idx=add(parent)
    high=[e['child_L'][i],e['child_U'][i]];low=[e['child_L'][i+batch],e['child_U'][i+batch]]
    dim=e['indices'][i];cut=flat(high[0])[dim]
    nodes[idx].update({'dim':dim,'cut':cut,'children':[add(low),add(high)]})
 # Every terminal box must have a positive floating producer margin.
 for n in nodes:
  if 'children' in n:continue
  e,i=bounds[key(n['box'])];lb=flat(e['lower'][i]);best=max(range(len(lb)),key=lambda k:lb[k]-float(__import__('fractions').Fraction(rhs[k])))
  assert lb[best]>float(__import__('fractions').Fraction(rhs[best])),('unverified leaf',lb)
  output=next(iter(e['A']));inp=next(iter(e['A'][output]));a=e['A'][output][inp]
  alpha=[]
  for r in e['relus']:
   if output in r['alpha']:alpha.append(r['alpha'][output][0][best][i])
   else:alpha.append([float(u>-l) for l,u in zip(flat(r['lower'][i]),flat(r['upper'][i]))])
  n.update({'terminal':True,'objective':best,'producer_margin':lb[best]-float(__import__('fractions').Fraction(rhs[best])),'A':flat(a['lA'][i][best]),'b':flat(a['lbias'][i])[best],'alphas':alpha})
 cert={'schema':'restricted-acas-box-v1','manifest':manifest,'net':net,'prop':1,'layers':layers,'root':nodes[0]['box'],'nodes':nodes,'c':cs,'rhs':rhs,'complete':True,'source_events':events}
 from exact_check import tree_check
 leaves=tree_check(cert)
 data=json.dumps(cert,separators=(',',':')).encode();open(out,'wb').write(data);open(out+'.zlib','wb').write(zlib.compress(data,9))
 result={'experiment':'normalize_cli_certificate','net':net,'prop':1,'leaves':len(leaves),'splits':len(nodes)-len(leaves),'nodes':len(nodes),'json_bytes':len(data),'zlib_bytes':len(zlib.compress(data,9)),'raw_event_bytes':os.path.getsize(events),'coverage':'pass'}
 print(json.dumps(result),flush=True);open('runs.jsonl','a').write(json.dumps(result)+'\n')
if __name__=='__main__':main()
