"""Pick, for each (p, H, seed), the all-right frozen network trained on the smallest fraction of pairs.
Prints the chosen .npz paths, one per line, and a summary to stderr."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean_mod_add_proof/lean_mod_add_proof"))
from gen_dataset import check_network  # noqa: E402
here = Path(__file__).resolve().parent
order = ["runs_wd1_f07", "runs_wd1_f09", "runs_wd02_f09", "runs_wd1_f10"]   # preference: least training data first
chosen = {}
for d in order:
    for f in sorted((here / d).glob("p*_h*_s*.npz")):
        if "_step" in f.name:
            continue
        key = f.stem
        if key in chosen:
            continue
        net = np.load(f)
        E1, E2, W2 = (net[k].astype(np.int64) for k in ("E1q", "E2q", "W2q"))
        wrong, ties = check_network(E1, E2, W2)
        if wrong == 0 and ties == 0:
            chosen[key] = (f, float(net["frac"]))
for key in sorted(chosen, key=lambda k: (int(k.split("_")[0][1:]), int(k.split("_")[1][1:]), int(k.split("_")[2][1:]))):
    print(chosen[key][0])
from collections import Counter
print("chosen per training fraction:", dict(Counter(v[1] for v in chosen.values())), file=sys.stderr)
print(f"{len(chosen)} of 63 (p,H,seed) keys have an all-right network", file=sys.stderr)
