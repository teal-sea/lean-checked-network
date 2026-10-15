"""Check, without Lean, that the Lean files describe the networks in network/*.npz.

Parses each lean/LeanCheckedNetwork/<Name>/Weights.lean with its own small parser (not the
generator), compares every entry with the .npz weights, evaluates the network from the parsed
Lean weights on all p * p input pairs exactly as Network.lean defines it (highest score, first
index on a tie), and checks the expected outcome: the trained and circle-only networks are right
on every pair, the planted fault is wrong on 226 pairs.

Usage: python3 verify_weights.py      (exit code 0 only if every check passes)
"""
import re
import sys
from pathlib import Path
import numpy as np

ENTRY = re.compile(r"\(\.(ofNat|negSucc) (\d+)\)")

def parse_table(src, name):
    m = re.search(rf"def {name} : List \(List Int\) := \[(.*?)\]\]", src, re.S)
    rows = re.findall(r"\[([^\[\]]*)\]", m.group(1) + "]")
    return np.array([[int(n) if k == "ofNat" else -int(n) - 1 for k, n in ENTRY.findall(r)] for r in rows],
                    dtype=np.int64)

def answers(E1, E2, W2):
    p = E1.shape[0]
    a, b = np.divmod(np.arange(p * p), p)
    z = E1[a] + E2[b]
    scores = (z * z) @ W2.T            # exact in int64 for these weight sizes
    return a, b, scores.argmax(1)       # argmax returns the first index on a tie, like Network.lean

ok = True
for name, npz, expect_wrong in [("Trained", "trained", 0), ("CircleOnly", "circle_only", 0), ("Fault", "fault", 226)]:
    src = Path(f"lean/LeanCheckedNetwork/{name}/Weights.lean").read_text()
    lean = {t: parse_table(src, t) for t in ["E1", "E2", "W2"]}
    net = np.load(f"network/{npz}.npz")
    same = all(np.array_equal(lean[t], net[f"{t}q"]) for t in lean)
    a, b, ans = answers(lean["E1"], lean["E2"], lean["W2"])
    wrong = int((ans != (a + b) % lean["E1"].shape[0]).sum())
    good = same and wrong == expect_wrong
    ok &= good
    print(f"{name:10s} Lean weights equal {npz}.npz: {same}; wrong on {wrong} of {len(ans)} pairs "
          f"(expected {expect_wrong}): {'ok' if good else 'FAIL'}")
sys.exit(0 if ok else 1)
