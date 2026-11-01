"""Float-scale analysis for train_gen.py runs (2026-11-01): for every checkpoint, the trained net and
its one-wave projection evaluated on the FLOAT weights with the run's own activation (no 8-bit
rounding, which is not meaningful for gelu, silu or tanh). The projection is circle_only.py's
construction without rounding: per neuron, the dominant frequency by energy summed over its E1, E2
and W2 columns, and each column replaced by its wave at that frequency.

Usage: python3 analyze_gen.py OUTDIR  -> OUTDIR/curve_gen.csv, one line per checkpoint on stdout."""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def acts():
    C = np.sqrt(2 / np.pi)
    sig = lambda z: 1 / (1 + np.exp(-z))  # noqa: E731
    return {'sq': lambda z: z * z, 'relu': lambda z: np.maximum(z, 0),
            'gelu': lambda z: 0.5 * z * (1 + np.tanh(C * (z + 0.044715 * z ** 3))),
            'silu': lambda z: z * sig(z), 'abs': np.abs, 'tanh': np.tanh}


def wrong(E1, E2, W2, p, f):
    a, b = np.divmod(np.arange(p * p), p)
    return int((f(E1[a] + E2[b]) @ W2.T).argmax(1).__ne__((a + b) % p).sum())


def one_wave(cols, p):
    H = cols[0].shape[1]; half = (p - 1) // 2; x = np.arange(p)
    out = [np.zeros_like(c) for c in cols]
    Fs = [np.fft.fft(c, axis=0) for c in cols]
    tot = sum(np.abs(F[1:half + 1]) ** 2 + np.abs(F[p - 1:p - half - 1:-1]) ** 2 for F in Fs)  # half x H
    k = tot.argmax(0) + 1
    for F, o in zip(Fs, out):
        amp = 2 * F[k, np.arange(H)] / p
        o[:] = (amp[None, :] * np.exp(2j * np.pi * np.outer(x, k) / p)).real
    return out


outdir = sys.argv[1]
files = sorted(glob.glob(os.path.join(outdir, "ckpt_step*.npz")), key=lambda f: int(f.split("step")[-1].split(".")[0]))
rows = []
for f in files:
    d = np.load(f)
    p, step = int(d["p"]), int(d["steps"]); act = str(d["act"]); fn = acts()[act]
    cols = [d[k] for k in ["E1", "E2", "W2"]]
    nw = wrong(*cols, p, fn); pw = wrong(*one_wave(cols, p), p, fn)
    rows.append(dict(step=step, act=act, opt=str(d["opt"]) if "opt" in d.files else "adam", train_acc=float(d["train_acc"]),
                     heldout_acc=float(d["heldout_acc"]), net_wrong=nw, proj_wrong=pw))
    print(f"step {step:6d} {act} net wrong {nw:5d} | projection wrong {pw:5d} | acc tr {float(d['train_acc']):.3f} te {float(d['heldout_acc']):.4f}", flush=True)
with open(os.path.join(outdir, "curve_gen.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
