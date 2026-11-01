"""Which part of the activation carries the adder? (fourth batch, RULES.md B; fixed before its runs.)

For every checkpoint of a train_gen.py run: the float one-wave projection of analyze_gen.py, evaluated
with the run's own activation f, with its even part (f(z) + f(-z)) / 2 alone, with its odd part
(f(z) - f(-z)) / 2 alone, with z^2 and with |z|. The same five evaluations of the trained net itself.

Usage: python3 analyze_even.py OUTDIR  -> OUTDIR/curve_even.csv, one line per checkpoint on stdout."""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze_gen import acts, one_wave, wrong  # noqa: E402

outdir = sys.argv[1]
files = sorted(glob.glob(os.path.join(outdir, "ckpt_step*.npz")), key=lambda f: int(f.split("step")[-1].split(".")[0]))
rows = []
for f in files:
    d = np.load(f)
    p, step, act = int(d["p"]), int(d["steps"]), str(d["act"])
    s = float(d["act_s"]) if "act_s" in d.files else 1.0
    fn = acts(s)[act]
    evals = {'own': fn, 'even': lambda z: (fn(z) + fn(-z)) / 2, 'odd': lambda z: (fn(z) - fn(-z)) / 2,
             'sq': lambda z: z * z, 'abs': np.abs}
    cols = [d[k] for k in ["E1", "E2", "W2"]]
    proj = one_wave(cols, p)
    row = dict(step=step, act=act, s=s, train_acc=float(d["train_acc"]), heldout_acc=float(d["heldout_acc"]))
    for name, g in evals.items():
        row[f"net_{name}"] = wrong(*cols, p, g)
        row[f"proj_{name}"] = wrong(*proj, p, g)
    rows.append(row)
    print(f"step {step:6d} {act} s {s:g} | proj own {row['proj_own']:5d} even {row['proj_even']:5d} odd {row['proj_odd']:5d} "
          f"sq {row['proj_sq']:5d} abs {row['proj_abs']:5d} | net own {row['net_own']:5d} even {row['net_even']:5d} odd {row['net_odd']:5d}",
          flush=True)
with open(os.path.join(outdir, "curve_even.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
