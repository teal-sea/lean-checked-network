"""Build the circle-only network: every neuron keeps only its main circle wave.

For each neuron, each of its three weight columns is replaced by its component at the
neuron's own frequency k (the best-fitting wave cos(2 pi k x / p + phase)), then rounded to
whole numbers. Dead neurons stay zero. Nothing else changes.

Usage: python3 circle_only.py network/trained.npz network/circle_only.npz
"""
import sys
import numpy as np

run = np.load(sys.argv[1])
p, H = int(run["p"]), int(run["H"])
cols = [run[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
half = (p - 1) // 2
out = [np.zeros_like(c) for c in cols]
for h in range(H):
    if not any(np.any(c[:, h]) for c in cols):
        continue
    tot = np.zeros(half)
    for c in cols:
        P = np.abs(np.fft.fft(c[:, h])) ** 2
        tot += P[1:half + 1] + P[p - 1:p - half - 1:-1]
    k = int(np.argmax(tot)) + 1
    x = np.arange(p)
    for c, o in zip(cols, out):
        F = np.fft.fft(c[:, h])
        amp = 2 * F[k] / p
        o[:, h] = np.round((amp * np.exp(2j * np.pi * k * x / p)).real).astype(np.int64)
pairs = np.array([(a, b) for a in range(p) for b in range(p)])
z = out[0][pairs[:, 0]] + out[1][pairs[:, 1]]
S = (z * z) @ out[2].T
wrong = int((S.argmax(1) != (pairs.sum(1) % p)).sum())
top2 = np.sort(S, 1)[:, -2:]
print(f"circle-only network: wrong on {wrong} of {p * p}, ties {int((top2[:, 0] == top2[:, 1]).sum())}, "
      f"largest weight {int(max(np.abs(o).max() for o in out))}")
np.savez(sys.argv[2], p=p, H=H, E1q=out[0], E2q=out[1], W2q=out[2])
