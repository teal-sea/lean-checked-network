"""Resolve elan shims to the actual toolchain without starting an uncapped Lean job."""
import json,os,subprocess,time
from pathlib import Path

def toolchain_bin(out):
 env=os.environ.copy();env.update(XDG_RUNTIME_DIR=f'/run/user/{os.getuid()}',DBUS_SESSION_BUS_ADDRESS=f'unix:path=/run/user/{os.getuid()}/bus')
 command=['systemd-run','--user','--quiet','--wait','--pipe','--slice=certcheck.slice',f'--unit=acas-toolchain-{time.time_ns()}','-pMemoryMax=16G','-pCPUAffinity=0-1',f'-pWorkingDirectory={Path(__file__).resolve().parents[1]/"lean"}','/usr/bin/env',f'PATH={os.environ["PATH"]}','LEAN_NUM_THREADS=2','OMP_NUM_THREADS=2','lean','--print-prefix']
 start=time.time();p=subprocess.run(command,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 record=dict(phase='toolchain-discovery',status=p.returncode,label='measured',command=command,wall_s=time.time()-start,stdout=p.stdout.strip(),stderr=p.stderr.strip())
 out.mkdir(parents=True,exist_ok=True)
 with (out/'runs.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 if p.returncode:raise RuntimeError(p.stderr)
 tool=Path(p.stdout.strip())/'bin'
 if not (tool/'leanchecker').exists():raise RuntimeError('toolchain is missing leanchecker')
 return tool
