#!/usr/bin/env python3
"""Run canonical public instructions and independently asserted negative controls."""
import hashlib, json, os, re, subprocess, time
from pathlib import Path

ROOT=Path.cwd(); RESULTS=[]

def run(label, cmd, *, cwd=ROOT, env=None, timeout=None):
    start=time.monotonic()
    with (ROOT/(label+'.log')).open('w') as output:
        result=subprocess.run(cmd,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,text=True,timeout=timeout)
    result.stdout=(ROOT/(label+'.log')).read_text()
    elapsed=round(time.monotonic()-start,3)
    RESULTS.append({'test':label,'seconds':elapsed,'returncode':result.returncode})
    print(f'{label}: rc={result.returncode}, measured {elapsed}s',flush=True)
    if result.returncode or label == 'reader':
        print(result.stdout[-6000:], flush=True)
    return result

def need(ok, message):
    if not ok: raise RuntimeError(message)

def main():
    doc=Path('/input/VERIFY.md').read_text()
    blocks=re.findall(r'```bash\n# DOC-START\n(.*?)# DOC-END\n```',doc,re.S)
    need(len(blocks)==1,'expected exactly one canonical fenced block')
    (ROOT/'canonical.sh').write_text(blocks[0])
    positive=run('reader', ['bash',str(ROOT/'canonical.sh')])
    need(positive.returncode==0,'canonical reader sequence failed; see reader.log')
    need('leanchecker replay passed: 20 new modules' in positive.stdout and '\nPASS: TransformerBridge.FinalRaw.raw_model_adds_mod_113\n' in positive.stdout,'missing proof replay success markers')
    bundle=ROOT/'lean-evidence-r2/transformer-final-raw-evidence-r2'
    env=dict(os.environ,PATH=str(Path.home()/'.elan/bin')+':/usr/bin:/bin')
    probe=run('from-source',['bash','verify.sh','--from-source','--work',str(ROOT/'source-work')],cwd=bundle,env=env)
    record=ROOT/'source-work/from-source.json'
    need(record.exists(),'source probe failed without a comparison record')
    comparison=json.loads(record.read_text())
    need(probe.returncode==int(not comparison['byte_identical']),'source probe return code disagrees with recorded comparison')
    RESULTS.append({'test':'source-comparison','result':comparison})
    # Scratch copy excludes verifier work. No release asset is modified.
    scratch=ROOT/'scratch'
    copied=run('scratch-copy',['cp','-a','--reflink=auto',str(bundle),str(scratch)])
    need(copied.returncode==0,'scratch copy failed')
    target=scratch/'lib/TransformerBridge/FinalRaw.olean'
    with target.open('r+b') as f:
        first=f.read(1); f.seek(0); f.write(bytes([first[0]^1]))
    corrupt=run('corruption',['bash','verify.sh','--work',str(ROOT/'corrupt-work')],cwd=scratch,env=env,timeout=30)
    need(corrupt.returncode!=0 and 'FAIL: sha256 mismatch:' in corrupt.stdout and 'FinalRaw.olean' in corrupt.stdout,'corruption did not fail for the checksum reason')
    need('2/6' not in corrupt.stdout,'corruption reached toolchain execution')
    # Restore the file, then deliberately update only the scratch checksum inventory.
    # This bypasses the integrity layer so rejection must come from Lean mathematics.
    subprocess.run(['cp',str(bundle/'lib/TransformerBridge/FinalRaw.olean'),str(target)],check=True)
    fixture=scratch/'KernelControl.lean'
    original=fixture.read_text(); mutated=original.replace('(0 : Nat) = 0','(0 : Nat) = 1')
    need(mutated!=original,'mutant did not change a proved statement')
    fixture.write_text(mutated)
    sums=scratch/'SHA256SUMS'; rows=sums.read_text().splitlines()
    sums.write_text('\n'.join((hashlib.sha256(fixture.read_bytes()).hexdigest()+'  KernelControl.lean') if row.endswith('  KernelControl.lean') else row for row in rows)+'\n')
    mutant=run('mutant',['bash','verify.sh','--work',str(ROOT/'mutant-work')],cwd=scratch,env=env,timeout=120)
    need(mutant.returncode!=0 and 'FAIL: kernel declaration rejected:' in mutant.stdout and 'Tactic `decide` proved that the proposition' in mutant.stdout and 'is false' in mutant.stdout,'mutant was not rejected mathematically')
    need('sha256 mismatch' not in mutant.stdout and 'Traceback' not in mutant.stdout,'mutant failed at the wrong boundary')
    missing_home=ROOT/'empty-home';missing_home.mkdir()
    missing=run('no-lean',['/usr/bin/env','-i','HOME='+str(missing_home),'PATH=/usr/bin:/bin','/bin/bash','verify.sh','--work',str(ROOT/'missing-work')],cwd=bundle,timeout=10)
    expected='FAIL: install elan and run lean --version in this bundle, or pass --toolchain DIR (Lean 4.35.0)\n'
    need(missing.returncode!=0 and missing.stdout==expected,'missing-Lean diagnostic must be exactly one actionable line')
    print('PASS: reader, checksum corruption, mutant declaration, no-Lean diagnostic',flush=True)

try:
    main()
finally:
    (ROOT/'gate-results.json').write_text(json.dumps(RESULTS,indent=2)+'\n')
    print(json.dumps(RESULTS,indent=2),flush=True)
