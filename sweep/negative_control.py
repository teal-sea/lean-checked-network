"""Negative control: remove one pair from a generated wrong list and show the kernel rejects it.

Usage: python3 negative_control.py OUTDIR [Trained|CircleOnly]

Copies OUTDIR/lean to OUTDIR/negative_control/lean, deletes the first wrong pair from
`wrongRows` and from `wrongPairs` (and lowers the stated length by one, so the only thing left
to fail is the row theorem itself), runs `lake build`, and exits 0 only if the build FAILS with
an error from the kernel on that row. Exits non-zero if the corrupted package builds, or if the
failure is not the kernel's.
"""
import re
import shutil
import subprocess
import sys
import os
from pathlib import Path

out = Path(sys.argv[1]).resolve()
which = sys.argv[2] if len(sys.argv) > 2 else "Trained"
src = out / "lean"
dst = out / "negative_control" / "lean"
if dst.exists():
    shutil.rmtree(dst)
shutil.copytree(src, dst, ignore=shutil.ignore_patterns(".lake"))
weights = next(dst.rglob(f"{which}/Weights.lean"))
table = weights.parent / "Table.lean"
txt = weights.read_text()
m = re.search(r"def wrongPairs : List \(Nat × Nat\) := \[\((\d+), (\d+)\)", txt)
if not m:
    print("no wrong pair to remove: the list is empty, this control needs a wrong network"); sys.exit(2)
a, b = int(m.group(1)), int(m.group(2))
txt = txt.replace(f"def wrongPairs : List (Nat × Nat) := [({a}, {b}), ", "def wrongPairs : List (Nat × Nat) := [", 1) \
    if f"[({a}, {b}), " in txt else txt.replace(f"[({a}, {b})]", "[]", 1)
rows = re.search(r"def wrongRows : List \(List Nat\) := \[\n(.*?)\]\n", txt, re.S)
lines = rows.group(1).split("\n")
row = lines[a]
assert row.strip().startswith(f"[{b},") or row.strip().startswith(f"[{b}]"), row
lines[a] = row.replace(f"[{b}, ", "[", 1) if f"[{b}, " in row else row.replace(f"[{b}]", "[]", 1)
txt = txt.replace(rows.group(1), "\n".join(lines))
weights.write_text(txt)
t = table.read_text()
k = int(re.search(r"wrongPairs.length = (\d+)", t).group(1))
table.write_text(t.replace(f"wrongPairs.length = {k}", f"wrongPairs.length = {k - 1}"))
print(f"removed ({a}, {b}) from {which}.wrongRows and wrongPairs; stated length {k} -> {k - 1}")
env = dict(os.environ, PATH=str(Path.home() / ".elan" / "bin") + os.pathsep + os.environ.get("PATH", ""))
r = subprocess.run(["lake", "build", "LeanCheckedNetwork"], cwd=dst, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(out / "negative_control" / "build.log").write_text(r.stdout)
# How a `decide +kernel` rejection shows up (toolchain source, src/lean/Lean/Elab/Tactic/Decide.lean,
# `doKernel`): the tactic builds the proof only through `mkAuxLemma`, which the kernel checks. If the
# kernel throws, the `catch` branch re-reduces the proposition in the elaborator just to word the
# message: "Tactic `decide` proved that the proposition ... is false" when that reduction reaches
# `false`, otherwise the kernel's own text ("(kernel) ..."). Either text means the kernel refused.
errors = [l for l in r.stdout.splitlines() if "error" in l]
kernel = [l for l in r.stdout.splitlines() if "(kernel)" in l or "proved that the proposition" in l]
print("lake build exit", r.returncode)
for l in errors[:10]:
    print(" ", l)
if r.returncode == 0:
    print("PROBLEM: the corrupted wrong list was accepted"); sys.exit(1)
if not kernel:
    print("PROBLEM: the build failed, but not at a `decide +kernel` step"); sys.exit(1)
at_row = [m.group(1) for l in errors for m in [re.search(r"error: (\S+Rows\d+\.lean):(\d+):", l)] if m]
rowfile = at_row[0] if at_row else None
print(f"rejected at the kernel-checked row theorem ({rowfile}): {kernel[0].strip()}")
# the rejected file must be the one holding row a
if rowfile is not None:
    txt = Path(dst / rowfile).read_text() if (dst / rowfile).exists() else ""
    if f"theorem fast_{a} " not in txt:
        print(f"PROBLEM: the failing file does not hold fast_{a}"); sys.exit(1)
    print(f"and that file holds fast_{a}, the row the pair ({a}, {b}) was removed from")
sys.exit(0)
