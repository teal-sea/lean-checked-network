"""The circle-only network with all three tables scaled by one factor before rounding.

Same construction as the repo's circle_only.py (each neuron's three weight columns replaced by
their wave at the neuron's own frequency), except that before rounding every table is multiplied
by factor = 127 / (largest unrounded entry over all three tables), so every entry lands in
[-127, 127] and the fast evaluator applies. Used by run_one.py only when circle_only.py's own
output has an entry outside that range. This is a different network from circle_only.py's.

Usage: python3 circle_rescale.py trained.npz out.npz
"""
import sys
import numpy as np

run = np.load(sys.argv[1])
p, H = int(run["p"]), int(run["H"])
cols = [run[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
half = (p - 1) // 2
waves = [np.zeros(c.shape) for c in cols]
for h in range(H):
    if not any(np.any(c[:, h]) for c in cols):
        continue
    tot = np.zeros(half)
    for c in cols:
        P = np.abs(np.fft.fft(c[:, h])) ** 2
        tot += P[1:half + 1] + P[p - 1:p - half - 1:-1]
    k = int(np.argmax(tot)) + 1
    x = np.arange(p)
    for c, w in zip(cols, waves):
        F = np.fft.fft(c[:, h])
        amp = 2 * F[k] / p
        w[:, h] = (amp * np.exp(2j * np.pi * k * x / p)).real
largest = max(np.abs(w).max() for w in waves)
factor = 127.0 / largest if largest > 127 else 1.0
out = [np.round(w * factor).astype(np.int64) for w in waves]
pairs = np.array([(a, b) for a in range(p) for b in range(p)])
z = out[0][pairs[:, 0]] + out[1][pairs[:, 1]]
S = (z * z) @ out[2].T
wrong = int((S.argmax(1) != (pairs.sum(1) % p)).sum())
top2 = np.sort(S, 1)[:, -2:]
print(f"rescaled circle-only network: factor {factor:.6f} (largest unrounded wave entry {largest:.3f}), wrong on {wrong} of {p * p}, "
      f"ties {int((top2[:, 0] == top2[:, 1]).sum())}, largest weight {int(max(np.abs(o).max() for o in out))}")
np.savez(sys.argv[2], p=p, H=H, E1q=out[0], E2q=out[1], W2q=out[2], factor=factor, largest_unrounded=largest)
