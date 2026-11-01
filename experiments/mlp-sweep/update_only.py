"""Is the adder in the first update itself? (2026-11-01.) For a run checkpointed at steps 0 and 1,
take the update D = W(step 1) - W(step 0) for E1, E2, W2 (no initialization), freeze it to whole
numbers exactly as the trainer freezes weights (scale so the largest entry is 127, round), and
apply circle_only.py's one-wave projection; count wrong pairs with the network rule of
Network.lean (x^2 hidden layer). Also reported: the update itself as a network, the step-1
network, and the step-0 network.

Usage: python3 update_only.py RUN_DIR [...]"""
import sys
import numpy as np


def freeze(x):
    return np.round(x * (127 / np.abs(x).max())).astype(np.int64)


def wrong(E1, E2, W2, p):
    a, b = np.divmod(np.arange(p * p), p)
    z = E1[a] + E2[b]
    return int(((z * z) @ W2.T).argmax(1).__ne__((a + b) % p).sum())


def one_wave(cols, p, H):
    half = (p - 1) // 2
    out = [np.zeros_like(c) for c in cols]
    x = np.arange(p)
    for h in range(H):
        if not any(np.any(c[:, h]) for c in cols):
            continue
        tot = np.zeros(half)
        for c in cols:
            P = np.abs(np.fft.fft(c[:, h])) ** 2
            tot += P[1:half + 1] + P[p - 1:p - half - 1:-1]
        k = int(np.argmax(tot)) + 1
        for c, o in zip(cols, out):
            F = np.fft.fft(c[:, h])
            o[:, h] = np.round((2 * F[k] / p * np.exp(2j * np.pi * k * x / p)).real).astype(np.int64)
    return out


for run in sys.argv[1:]:
    d0, d1 = np.load(f"{run}/ckpt_step0.npz"), np.load(f"{run}/ckpt_step1.npz")
    p, H = int(d0["p"]), int(d0["H"])
    D = [freeze(d1[k] - d0[k]) for k in ["E1", "E2", "W2"]]
    W1q = [d1[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    W0q = [d0[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    print(f"{run}: p {p} H {H} | step-0 net {wrong(*W0q, p)}, projection {wrong(*one_wave(W0q, p, H), p)} | "
          f"step-1 net {wrong(*W1q, p)}, projection {wrong(*one_wave(W1q, p, H), p)} | "
          f"update alone as a net {wrong(*D, p)}, its projection {wrong(*one_wave(D, p, H), p)}", flush=True)
