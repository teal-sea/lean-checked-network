#!/usr/bin/env python3
"""Repackage an extracted original release without changing evidence bytes."""
import argparse, hashlib, json, shutil, subprocess
from pathlib import Path

def digest(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def inventory(root):
    return {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*')) if p.is_file()}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('original',type=Path);ap.add_argument('output',type=Path)
    args=ap.parse_args(); original=args.original.resolve(); out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=True)
    name='transformer-final-raw-evidence-r2'; bundle=out/name
    if bundle.exists(): shutil.rmtree(bundle)
    shutil.copytree(original,bundle)
    root=Path(__file__).resolve().parent
    shutil.copyfile(root/'verify-release.sh',bundle/'verify.sh');(bundle/'verify.sh').chmod(0o755)
    shutil.copyfile(root/'KernelControl.lean',bundle/'KernelControl.lean')
    (bundle/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
    readme=(original/'README.md').read_text()
    a=readme.index('## Running the check');b=readme.index('## What `verify.sh` checks',a)
    readme=readme[:a]+'''## Running the check

Use the single canonical command block in [VERIFY.md](https://github.com/teal-sea/lean-checked-network/blob/release/coherent-evidence-r2/VERIFY.md).
This r2 bundle supersedes transformer-final-raw-evidence. The verifier is included and inventoried; no overlay is needed.
Supported gate environment: Ubuntu 24.04, Linux x86_64, Python 3.11 or newer, curl, git, tar, zstd and a C toolchain. Dependency downloads require network access. Allow at least 30 GB free disk space. Fresh installation and replay timing is reported separately; a 3 to 5 minute total is a target, not a measured guarantee.

`--toolchain DIR` selects an existing official Lean 4.35.0 installation. Otherwise install elan, run `lean --version` in this bundle to install the pinned version, then run the verifier. Discovery uses only `elan which lean` with the bundle as its current directory.
`--packages DIR` uses an existing pinned dependency cache. `--threads N` accepts 1 through 4, default 2. `--full` replays all project objects and `--controls` runs the existing paired data controls. The default always checks the small KernelControl.lean packaging fixture with `decide +kernel`.
`--from-source` rebuilds only TransformerCore.Model from bundled source using the authenticated core toolchain and compares SHA256 bytes with the shipped object. It writes verify-work/from-source.json and exits nonzero if bytes differ. This core-only probe does not test Mathlib dependency rebuilding or certify all project sources.

## Source and object trust boundary

The default check establishes that Lean accepts the shipped theorem term for the printed proposition, audits its standard axioms, and replays the 20 new modules with leanchecker. It assumes the authenticated earlier project, Mathlib and core objects, the checker, host runtime, hardware and release origin. It does not establish that all shipped objects were built from src/. The manifest records source/object hashes and historical provenance, but is not a complete reproducible build recipe binding every object to one source commit.
To establish the remaining source relationship, rebuild every project module from src/ with the exact pinned toolchain and dependency revisions, record compiler options and generated inputs, compare objects, and investigate any differences. The bounded --from-source probe supplies evidence for one module only. No whole-bundle source reproducibility claim is made. Measured on Ubuntu 24.04 with the pinned Lean 4.35.0: TransformerCore.Model recompiles successfully, but its bytes differ (shipped 950cfc7e79f0878b24813aa23bb64ce66b6e7c5edc4c420ef6be21e6c6e47d5b; rebuilt 4bb28b599c3b5b29e5b315e6d02f05feb08d94fa51e00ee2dcb49f773b2f571c). This does not show a mathematical discrepancy; the original complete build recipe has not been reproduced. Treat the shipped objects as supplied proof artifacts, with replay and the stated assumptions.

''' +readme[b:]
    (bundle/'README.md').write_text(readme)
    before=inventory(original); after=inventory(bundle)
    changes=[]
    for rel in sorted(before.keys()|after.keys()):
        if before.get(rel)!=after.get(rel):
            if rel not in {'verify.sh','README.md','lean-toolchain','KernelControl.lean','SHA256SUMS'}:
                raise SystemExit('non-packaging change: '+rel)
            changes.append({'path':rel,'old_sha256':before.get(rel),'new_sha256':after.get(rel)})
    (bundle/'SHA256SUMS').write_text(''.join(f'{h}  {n}\n' for n,h in sorted(after.items()) if n!='SHA256SUMS'))
    changes.append({'path':'SHA256SUMS','old_sha256':before.get('SHA256SUMS'),'new_sha256':digest(bundle/'SHA256SUMS')})
    archive=out/(name+'.tar.zst')
    subprocess.run(['tar','--sort=name','--mtime=@0','--owner=0','--group=0','--numeric-owner','--zstd','-cf',str(archive),'-C',str(out),name],check=True)
    final={archive.name:digest(archive)}
    final.update({name+'/'+n:h for n,h in inventory(bundle).items()})
    (out/'SHA256SUMS').write_text(''.join(f'{h}  {n}\n' for n,h in sorted(final.items())))
    result={'changes':changes,'evidence_unchanged':all(after[n]==h for n,h in before.items() if n not in {'verify.sh','README.md','SHA256SUMS'}),
            'original_files':len(before),'bundle_files':len(inventory(bundle)), 'archive_sha256':digest(archive),
            'sha256sums_sha256':digest(out/'SHA256SUMS'),'internal_sha256sums_sha256':digest(bundle/'SHA256SUMS')}
    (out/'build-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__': main()
