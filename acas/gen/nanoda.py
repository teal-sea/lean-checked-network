#!/usr/bin/env python3
"""Export the final theorem closure and independently check it with a hard axiom allowlist."""
import argparse,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
A=Path(__file__).resolve().parents[1];L=A/'lean'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=A/'work/nanoda');args=ap.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True);(out/'scratch').mkdir(exist_ok=True)
 tool=Path(shutil.which('lean')).resolve().parent
 roots=[L/'.lake/build/lib/lean',*sorted((L/'.lake/packages').glob('*/.lake/build/lib/lean')),tool.parent/'lib/lean'];lp=':'.join(map(str,roots))
 objects={str(p):sha(p) for root in roots for p in sorted(root.rglob('*.olean'))}
 (out/'objects.json').write_text(json.dumps(objects,indent=2)+'\n')
 env=os.environ.copy();env.update(XDG_RUNTIME_DIR=f'/run/user/{os.getuid()}',DBUS_SESSION_BUS_ADDRESS=f'unix:path=/run/user/{os.getuid()}/bus')
 def run(stage,cmd,stdout,memory):
  if shutil.disk_usage(out).free<45_000_000_000:raise RuntimeError('disk reserve reached')
  tim=out/(stage+'.time');err=out/(stage+'.err');start=time.time()
  args=['systemd-run','--user','--quiet','--wait','--pipe','--slice=certcheck.slice',f'--unit=acas-{stage}-{time.time_ns()}',f'-pWorkingDirectory={L}',f'-pMemoryMax={memory}','-pCPUAffinity=0-1','/usr/bin/time','-v','-o',str(tim),'taskset','-c','0-1','/usr/bin/env','-i',f'PATH={tool}:/usr/bin:/bin',f'HOME={out}/scratch',f'TMPDIR={out}/scratch',f'LEAN_PATH={lp}','LEAN_NUM_THREADS=2',*cmd]
  with stdout.open('w') as f,err.open('w') as e:p=subprocess.run(args,env=env,stdout=f,stderr=e)
  record=dict(stage=stage,status=p.returncode,wall_s=time.time()-start,label='measured',command=args,stdout=str(stdout),stderr=str(err),time=str(tim))
  if tim.exists():
   txt=tim.read_text()
   for key,label in [('user_s','User time (seconds)'),('sys_s','System time (seconds)'),('rss_kib','Maximum resident set size (kbytes)')]:
    h=re.search(re.escape(label)+r':\s*([\d.]+)',txt)
    if h:record[key]=float(h[1])
  with (out/'runs.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
  (out/'STATUS.json').write_text(json.dumps(record,indent=2)+'\n')
  if p.returncode:raise SystemExit(json.dumps(record))
  return record
 exp=out/'final.ndjson';run('leanexport',[str(tool/'leanexport'),'ACASChecked.Final','--','ACASChecked.acas_1_1_property1'],exp,'16G')
 config=dict(export_file_path=str(exp),use_stdin=False,permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,pp_declars=[],pp_to_stdout=False,print_success_message=True)
 (out/'nanoda.json').write_text(json.dumps(config,indent=2)+'\n')
 result=run('nanoda',[str(tool/'nanoda_bin'),str(out/'nanoda.json')],out/'nanoda.log','64G')
 lines=[x for x in (out/'nanoda.log').read_text().splitlines() if re.search(r'Checked [\d,]+ declarations',x)]
 if not lines:raise RuntimeError('no Checked N declarations success line')
 assert objects=={str(p):sha(Path(p)) for p in objects},'olean bytes changed during independent replay'
 result.update(checked_line=lines[-1],export_sha256=sha(exp),object_manifest_sha256=sha(out/'objects.json'),axioms=config['permitted_axioms'])
 (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
