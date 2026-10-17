"""A Python mirror of the bound certificates, read straight from the committed Net/W/*.lean literals (NOT kernel
evidence: the kernel checks in Net/B/ and Net/Cols.lean are). It tells us before CI whether any certificate can fail:
every vector has the length `tablesOk` states and entries within the `bnd` of Net/Weights.lean, and the G column sums.
Usage: python3 -I transformer/lean/mirror_bounds.py"""
import re, sys
from pathlib import Path

net = Path(__file__).resolve().parent / "Transformer" / "Net"
bnd = dict(zip(("kTI", "kCI", "kTU", "kCU", "kG"), map(int, re.search(
    r"def bnd : Bnd := \{ kTI := (\d+), kCI := (\d+), kTU := (\d+), kCU := (\d+), kG := (\d+) \}", (net / "Weights.lean").read_text()).groups())))
lit = re.compile(r"\(\.(ofNat|negSucc) (\d+)\)")
vecs = {}
for f in sorted((net / "W").glob("*.lean")):
    for m in re.finditer(r"^def (\w+) : List Int := (\[.*\])$", f.read_text(), re.M):
        vecs[m.group(1)] = [int(n) if kind == "ofNat" else -int(n) - 1 for kind, n in lit.findall(m.group(2))]
rows = {"TI0": 512, "TI1": 512, "TU0": 113, "TU1": 113}
k_of = {"TI": bnd["kTI"], "TU": bnd["kTU"]}
bad, counts, maxabs = [], {}, {}
for name, v in vecs.items():
    m = re.fullmatch(r"(TI0|TI1|TU0|TU1)_(\d)_(\d+)", name)
    if m:
        n, k = rows[m.group(1)], k_of[m.group(1)[:2]]
    elif re.fullmatch(r"TI2_\d", name):
        n, k = 512, bnd["kTI"]
    elif re.fullmatch(r"TU2_\d", name):
        n, k = 113, bnd["kTU"]
    elif name == "CI":
        n, k = 512, bnd["kCI"]
    elif name == "CU":
        n, k = 113, bnd["kCU"]
    elif re.fullmatch(r"G_\d+", name):
        n, k = 113, bnd["kG"]
    else:
        continue  # score vectors sc0/sc1/sc2 are not part of tablesOk
    key = re.sub(r"_\d.*", "", name) if name[0] in "TG" else name
    counts[key] = counts.get(key, 0) + 1
    maxabs[key] = max(maxabs.get(key, 0), max(abs(x) for x in v))
    if len(v) != n or max(abs(x) for x in v) > k:
        bad.append(f"{name}: length {len(v)} (want {n}), max |x| {max(abs(x) for x in v)} (bound {k})")
G = [vecs[f"G_{i}"] for i in range(512)]
cols = [sum(abs(r[k]) for r in G) for k in range(113)]
bound = 8774 * 2025
if max(cols) > bound:
    bad.append(f"G column sum {max(cols)} > {bound}")
print("vectors per table:", counts)
print("max |entry| per table:", maxabs, "bnd:", bnd)
print(f"G: 512 rows, max column sum {max(cols)} (bound {bound}); bad = {len(bad)}")
for b in bad:
    print("BAD", b)
sys.exit(1 if bad else 0)
