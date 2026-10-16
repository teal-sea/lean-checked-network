"""Empirical check of the frozen integer network on random long inputs (not the proof; a sanity check).
Usage: python3 check_long.py FROZEN.npz"""
import sys, numpy as np
Q = np.load(sys.argv[1]); H = Q["Wh"].shape[0]
rng = np.random.default_rng(7)
for L in (8, 16, 64, 128, 1000, 10000):
    n = 200 if L <= 1000 else 5
    a = rng.integers(0, 2, (n, L)); b = rng.integers(0, 2, (n, L))
    h = np.zeros((n, H), np.int64); c = np.zeros(n, np.int64); ok = np.ones(n, bool)
    for t in range(L):
        x = np.stack([a[:, t], b[:, t]], 1)
        h = (h @ Q["Wh"].T + x @ Q["Wx"].T + Q["bh"] > 0).astype(np.int64)
        y = (h @ Q["Wo"] + x @ Q["Wox"] + Q["bo"] > 0).astype(np.int64)
        tot = a[:, t] + b[:, t] + c; c = tot // 2
        ok &= (y == tot % 2)
    ok &= ((h @ Q["Wc"] + Q["bc"] > 0).astype(np.int64) == c)
    print(f"  length {L:5d}: {int(ok.sum())} of {n} random pairs added correctly (sum bits and final carry)")
