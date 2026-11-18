#!/usr/bin/env python3
"""Single entrypoint for the generated Lean files (stdlib only, repo-relative paths).

  python3 generate.py --check    pinned inputs, accepted Lean source digests, and byte-identical,
                                 deterministic regeneration of Pilot.lean, NetExtra.lean and FloatTables.lean
                                 (all outputs go to a temporary directory)
  python3 generate.py            regenerate those three files in place under lean/
"""
import argparse, hashlib, pathlib, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent
GENERATED = [("gen_lean.py", "Pilot.lean"), ("gen_extra.py", "NetExtra.lean"), ("gen_float.py", "FloatTables.lean")]

def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()

def check_manifest(manifest):
    bad = []
    for line in (ROOT / manifest).read_text().splitlines():
        digest, name = line.split(None, 1)
        name = name.strip().lstrip("*")
        if not (ROOT / name).is_file() or sha(ROOT / name) != digest:
            bad.append(name)
    return bad

def run_generator(script, out):
    subprocess.run([sys.executable, "-I", "-B", str(ROOT / script), "--out", str(out)], check=True,
                   cwd=ROOT, stdout=subprocess.DEVNULL)

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args(argv)
    if not a.check:
        for script, target in GENERATED:
            run_generator(script, ROOT / "lean" / target)
            print("wrote lean/" + target)
        return 0
    failed = False
    for manifest in ("upstream/SHA256SUMS", "SHA256SUMS.lean"):
        bad = check_manifest(manifest)
        print(f"{manifest}: {'OK' if not bad else 'MISMATCH ' + ', '.join(bad)}")
        failed |= bool(bad)
    with tempfile.TemporaryDirectory() as t1, tempfile.TemporaryDirectory() as t2:
        for script, target in GENERATED:
            outs = []
            for t in (t1, t2):
                out = pathlib.Path(t) / target
                run_generator(script, out)
                outs.append(out.read_bytes())
            same_runs = outs[0] == outs[1]
            same_committed = outs[0] == (ROOT / "lean" / target).read_bytes()
            print(f"{script} -> lean/{target}: deterministic={same_runs} byte-identical-to-committed={same_committed}")
            failed |= not (same_runs and same_committed)
    print("generate --check:", "FAIL" if failed else "PASS")
    return 1 if failed else 0

if __name__ == "__main__":
    sys.exit(main())
