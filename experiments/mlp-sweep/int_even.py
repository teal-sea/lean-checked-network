"""The integer (8-bit) one-wave projection of a train_gen.py run, read with z^2 and with |z| (sixth
batch follow-up, 2026-11-01). For every checkpoint: the frozen tables E1q, E2q, W2q (as saved by
train_gen.py), each neuron reduced to its dominant wave and rounded (the pure clock of
seal_act.py / seal_cell.py --pure-clock, and analyze_act.py's circle_only), then evaluated in exact
integers with z^2 and with |z|. A cell exact under z^2 is a seal candidate for seal_cell.py, read as
an x^2 network.

Usage: python3 int_even.py OUTDIR  -> OUTDIR/curve_int_even.csv, one line per checkpoint on stdout."""
import csv
import glob
import os
import sys

import numpy as np


def clock(cols, p):
    half = (p - 1) // 2
    out = [np.zeros(c.shape, dtype=np.int64) for c in cols]
    for h in range(cols[0].shape[1]):
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1
        for F, o in zip(Fs, out):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    return out


def wrong(E1, E2, W2, p, f):
    a, b = np.divmod(np.arange(p * p), p)
    S = f(E1[a] + E2[b]) @ W2.T
    top2 = np.sort(S, 1)[:, -2:]
    return int((S.argmax(1) != (a + b) % p).sum()), int((top2[:, 0] == top2[:, 1]).sum())


outdir = sys.argv[1]
files = sorted(glob.glob(os.path.join(outdir, "ckpt_step*.npz")), key=lambda f: int(f.split("step")[-1].split(".")[0]))
rows = []
for f in files:
    d = np.load(f)
    p, step = int(d["p"]), int(d["steps"])
    cols = [d[k].astype(np.int64) for k in ("E1q", "E2q", "W2q")]
    cl = clock(cols, p)
    r = dict(step=step, act=str(d["act"]))
    for name, g in (("sq", lambda z: z * z), ("abs", np.abs)):
        r[f"net_{name}"], _ = wrong(*cols, p, g)
        r[f"clock_{name}"], r[f"clock_{name}_ties"] = wrong(*cl, p, g)
    r["clock_max_abs"] = int(max(np.abs(c).max() for c in cl))
    rows.append(r)
    print(f"step {step:6d} {r['act']} | integer clock read with z^2 {r['clock_sq']:5d} (ties {r['clock_sq_ties']}) |z| {r['clock_abs']:5d} | frozen net z^2 {r['net_sq']:5d} |z| {r['net_abs']:5d}", flush=True)
with open(os.path.join(outdir, "curve_int_even.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
