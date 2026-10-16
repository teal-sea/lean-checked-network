"""Check, without Lean, that the literals in a generated Lean file are exactly the frozen npz weights.
Usage: python3 verify_lean_weights.py FROZEN.npz LEANFILE"""
import re, sys, numpy as np
Q = np.load(sys.argv[1]); txt = open(sys.argv[2]).read()
def ints(field):
    body = re.search(field + r" := (\[.*?\])(?=,\n  [A-Za-z]|\n\}|\})", txt, re.S).group(1)
    vals = [int(n) if k == "ofNat" else -int(n) - 1 for k, n in re.findall(r"\.(ofNat|negSucc) (\d+)", body)]
    return np.array(vals)
def one(field):
    k, n = re.search(field + r" := \(\.(ofNat|negSucc) (\d+)\)", txt).groups()
    return int(n) if k == "ofNat" else -int(n) - 1
checks = {
    "Wh": np.array_equal(ints("Wh"), Q["Wh"].ravel()),
    "Wxa": np.array_equal(ints("Wxa"), Q["Wx"][:, 0]), "Wxb": np.array_equal(ints("Wxb"), Q["Wx"][:, 1]),
    "bh": np.array_equal(ints("bh"), Q["bh"]), "Wo": np.array_equal(ints("Wo"), Q["Wo"]),
    "Woa": one("Woa") == int(Q["Wox"][0]), "Wob": one("Wob") == int(Q["Wox"][1]), "bo": one("bo") == int(Q["bo"]),
    "Wc": np.array_equal(ints("Wc"), Q["Wc"]), "bc": one("bc") == int(Q["bc"]),
}
print(sys.argv[2], "matches", sys.argv[1], ":", all(checks.values()), {k: v for k, v in checks.items() if not v})
sys.exit(0 if all(checks.values()) else 1)
