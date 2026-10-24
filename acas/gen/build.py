#!/usr/bin/env python3
"""Resource-bounded source build and optional clean-environment kernel replay.
Run lake update and lake exe cache get first. Never copies ACAS/TorchLean oleans.
"""
import argparse,concurrent.futures,fcntl,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
G=Path(__file__).resolve().parent; A=G.parent; L=A/'lean'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
 return re.findall(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)',p.read_text())

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--replay',action='store_true');ap.add_argument('--only-replay',action='store_true');ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--out',type=Path,default=A/'work/build');ap.add_argument('--all',action='store_true',help='include controls and auxiliary new modules');args=ap.parse_args()
 if not 1<=args.jobs<=4:ap.error('jobs must be between 1 and 4')
 tool=Path(shutil.which('lean')).resolve().parent
 output=args.out.resolve();output.mkdir(parents=True,exist_ok=True);(output/'scratch').mkdir(exist_ok=True);(output/'logs').mkdir(exist_ok=True)
 lp=subprocess.check_output([str(tool/'lake'),'env','printenv','LEAN_PATH'],cwd=L,text=True).strip()
 env=os.environ.copy();env.update(XDG_RUNTIME_DIR=f'/run/user/{os.getuid()}',DBUS_SESSION_BUS_ADDRESS=f'unix:path=/run/user/{os.getuid()}/bus')
 roots=[L,*sorted((L/'.lake/packages').glob('*'))];paths=[L/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in roots[1:]],tool.parent/'lib/lean'];lp=':'.join(map(str,paths))
 modules={};deps={};external={}
 def locate(m):
  rel=Path(m.replace('.','/')+'.lean')
  for r in roots:
   p=r/rel
   if p.exists():return r,p
  return None
 def add(m):
  if m in modules or m in external:return
  found=locate(m)
  if not found:
   if not any((p/(m.replace('.','/')+'.olean')).exists() for p in paths):raise RuntimeError('missing dependency '+m)
   external[m]='toolchain';return
  root,p=found;o=root/'.lake/build/lib/lean'/Path(m.replace('.','/')+'.olean')
  # Only Mathlib and its pinned dependencies may use downloaded cache artifacts.
  if root!=L and root.name!='TorchLean' and o.exists():external[m]=sha(o);return
  modules[m]=(root,p,o);deps[m]=imports(p)
  for d in deps[m]:add(d)
 targets=[str(p.relative_to(L).with_suffix('')).replace('/','.') for p in sorted((L/'ACASChecked').rglob('*.lean'))] if args.all else ['ACASChecked.Final']
 for m in targets:add(m)
 statefile=output/'state.json';state=json.loads(statefile.read_text()) if statefile.exists() else {};done=set();active=set();slots=list(range(args.jobs));fail=[];started=time.time()
 def fingerprint(m):return hashlib.sha256((sha(modules[m][1])+''.join(state[d]['olean_sha256'] if d in state else external[d] for d in deps[m])).encode()).hexdigest()
 def run(m,slot,fp):
  root,source,olean=modules[m];olean.parent.mkdir(parents=True,exist_ok=True)
  outcomes=[]
  phases=['replay'] if args.only_replay else ['compile','replay'] if args.replay else ['compile']
  for phase in phases:
   if shutil.disk_usage(output).free<45_000_000_000:raise RuntimeError('disk reserve reached')
   name=f'{m}-{phase}-{time.time_ns()}';log=output/'logs'/f'{name}.log';tim=log.with_suffix('.time');cpus=f'{slot*2}-{slot*2+1}'
   if phase=='compile':cmd=[str(tool/'lean'),'-j2','-R',str(root),'-o',str(olean),str(source)]
   else:cmd=['/usr/bin/env','-i',f'PATH={tool}:/usr/bin:/bin',f'HOME={output}/scratch',f'TMPDIR={output}/scratch',f'LEAN_PATH={lp}','LEAN_NUM_THREADS=2',str(tool/'leanchecker'),'-v',m]
   command=['systemd-run','--user','--quiet','--wait','--pipe','--slice=certcheck.slice',f'--unit=acas-{slot}-{time.time_ns()}','-pMemoryMax=16G',f'-pCPUAffinity={cpus}',f'-pWorkingDirectory={L}','/usr/bin/env',f'LEAN_PATH={lp}','LEAN_NUM_THREADS=2','OMP_NUM_THREADS=2','/usr/bin/time','-v','-o',str(tim),'taskset','-c',cpus,*cmd]
   start=time.time()
   with log.open('w') as f:p=subprocess.run(command,env=env,stdout=f,stderr=subprocess.STDOUT)
   status=p.returncode
   if phase=='compile' and status==0 and (not olean.exists() or olean.stat().st_mtime<start):status=143
   record=dict(module=m,phase=phase,status=status,started_unix=start,wall_s=time.time()-start,source_sha256=sha(source),command=command,log=str(log),time=str(tim),label='measured')
   if olean.exists():record['olean_sha256']=sha(olean)
   if tim.exists():
    txt=tim.read_text()
    for key,label in [('user_s','User time (seconds)'),('sys_s','System time (seconds)'),('rss_kib','Maximum resident set size (kbytes)')]:
     hit=re.search(re.escape(label)+r':\s*([\d.]+)',txt)
     if hit:record[key]=float(hit[1])
   with (output/'runs.jsonl').open('a') as f:
    fcntl.flock(f,fcntl.LOCK_EX);f.write(json.dumps(record)+'\n')
   outcomes.append(record)
   if status:raise RuntimeError(f'{m} {phase}: {status}: {log}')
  return dict(fingerprint=fp,source_sha256=sha(source),olean_sha256=sha(olean),replayed=args.replay or args.only_replay,outcomes=outcomes)
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
  futures={}
  while len(done)<len(modules):
   for m in modules:
    if m in done or m in active or any(d in modules and d not in done for d in deps[m]):continue
    fp=fingerprint(m);old=state.get(m)
    if old and old['fingerprint']==fp and modules[m][2].exists() and sha(modules[m][2])==old['olean_sha256'] and (not(args.replay or args.only_replay) or old['replayed']):done.add(m);continue
    if not slots or fail:continue
    slot=slots.pop(0);futures[pool.submit(run,m,slot,fp)]=(m,slot);active.add(m)
   if not futures:
    if fail:break
    if len(done)==len(modules):break
    raise RuntimeError('dependency cycle or missing dependency')
   finished,_=concurrent.futures.wait(futures,return_when=concurrent.futures.FIRST_COMPLETED)
   for future in finished:
    m,slot=futures.pop(future);slots.append(slot);active.remove(m)
    try:state[m]=future.result();done.add(m)
    except Exception as e:fail.append(str(e));print(str(e),flush=True)
    statefile.write_text(json.dumps(state,indent=2)+'\n')
    status=dict(stage='source-build-and-replay',completed=len(done),total=len(modules),active=sorted(active),failed=fail,updated_unix=time.time(),elapsed_s=time.time()-started,label='measured')
    (output/'STATUS.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status),flush=True)
   if fail and not futures:break
 if fail:raise SystemExit('\n'.join(fail))
 print('BUILD COMPLETE',len(done),flush=True)
if __name__=='__main__':main()
