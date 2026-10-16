"""Train a recurrent network with a binary hidden state to add two binary numbers, LSB first.

Architecture (one step, input bits x = (a, b)):
  pre_t = Wh h_{t-1} + Wx x_t + bh          h_t = [pre_t > 0]        (binary state, H units)
  o_t   = Wo h_t + Wox x_t + bo              sum bit  = [o_t > 0]
  c_t   = Wc h_t + bc                        carry    = [c_t > 0]    (read off the state)
Forward pass uses the hard threshold. Backward pass uses a surrogate gradient for the
threshold (derivative of a sigmoid with slope K), written by hand (BPTT in numpy).

Usage: python3 train_rnn.py H SEED STEPS CARRY_SUP OUT.npz
  CARRY_SUP = every  (carry readout supervised after every step)
            = final  (carry readout supervised only after the last step)
"""
import sys, time
import numpy as np

import argparse
ap = argparse.ArgumentParser()
ap.add_argument("H", type=int); ap.add_argument("seed", type=int); ap.add_argument("steps", type=int)
ap.add_argument("carry_sup"); ap.add_argument("out")
ap.add_argument("--mode", default="hard", help="hard: threshold forward + surrogate grad; soft: sigmoid(K*pre) forward")
ap.add_argument("--K", type=float, default=2.0); ap.add_argument("--lr", type=float, default=3e-3)
ap.add_argument("--wd", type=float, default=1e-3); ap.add_argument("--margin_w", type=float, default=0.0)
ap.add_argument("--margin", type=float, default=0.0); ap.add_argument("--B", type=int, default=256)
ap.add_argument("--quiet", action="store_true")
ap.add_argument("--margin_start", type=int, default=0, help="apply the hinge margin only from this step on")
A = ap.parse_args()
H, seed, steps, carry_sup, out = A.H, A.seed, A.steps, A.carry_sup, A.out
lr, wd, K, margin_w, margin, B, mode = A.lr, A.wd, A.K, A.margin_w, A.margin, A.B, A.mode
rng = np.random.default_rng(seed)

def sig(z): return 1 / (1 + np.exp(-z))

params = {
    "Wh": rng.normal(0, 1, (H, H)) / np.sqrt(H),
    "Wx": rng.normal(0, 1, (H, 2)),
    "bh": np.zeros(H),
    "Wo": rng.normal(0, 1, (1, H)) / np.sqrt(H),
    "Wox": rng.normal(0, 1, (1, 2)),
    "bo": np.zeros(1),
    "Wc": rng.normal(0, 1, (1, H)) / np.sqrt(H),
    "bc": np.zeros(1),
}
m = {k: np.zeros_like(v) for k, v in params.items()}
v = {k: np.zeros_like(x) for k, x in params.items()}
b1, b2 = 0.9, 0.999

def make_batch(n, L, rng):
    a = rng.integers(0, 2, (n, L)); b = rng.integers(0, 2, (n, L))
    s = np.zeros((n, L), int); c = np.zeros((n, L), int)
    carry = np.zeros(n, int)
    for t in range(L):
        tot = a[:, t] + b[:, t] + carry
        s[:, t] = tot % 2; carry = tot // 2; c[:, t] = carry
    return a, b, s, c

def forward(P, a, b, hard=True):
    n, L = a.shape
    h = np.zeros((n, H)); hs = [h]; pres = []; os_ = []; cs = []
    for t in range(L):
        x = np.stack([a[:, t], b[:, t]], 1).astype(float)
        pre = h @ P["Wh"].T + x @ P["Wx"].T + P["bh"]
        h = (pre > 0).astype(float) if hard else sig(K * pre)
        hs.append(h); pres.append(pre)
        os_.append(h @ P["Wo"].T + x @ P["Wox"].T + P["bo"])
        cs.append(h @ P["Wc"].T + P["bc"])
    return hs, pres, np.concatenate(os_, 1), np.concatenate(cs, 1)

def evaluate(P, L, n=2000, rng=np.random.default_rng(12345)):
    a, b, s, c = make_batch(n, L, rng)
    _, _, o, cc = forward(P, a, b)
    bit_ok = ((o > 0) == (s == 1))
    seq_ok = bit_ok.all(1) & (((cc[:, -1] > 0)) == (c[:, -1] == 1))
    return float(bit_ok.mean()), float(seq_ok.mean())

t0 = time.time()
for step in range(1, steps + 1):
    L = int(rng.integers(8, 17))
    a, b, s, c = make_batch(B, L, rng)
    P = params
    hs, pres, o, cc = forward(P, a, b, hard=(mode == "hard"))
    margin_w = A.margin_w if step >= A.margin_start else 0.0
    g = {k: np.zeros_like(x) for k, x in P.items()}
    # output losses (mean BCE over batch and time)
    do = (sig(o) - s) / (B * L)
    if carry_sup == "every":
        dc = (sig(cc) - c) / (B * L)
    else:
        dc = np.zeros_like(cc); dc[:, -1] = (sig(cc[:, -1]) - c[:, -1]) / B
    if margin_w > 0:   # hinge pushing the sum-bit and carry pre-activations away from 0
        do = do + margin_w * (-np.sign(o)) * (np.abs(o) < margin) / (B * L)
        dc = dc + margin_w * (-np.sign(cc)) * (np.abs(cc) < margin) / (B * L)
    loss = (-(s * np.log(sig(o) + 1e-9) + (1 - s) * np.log(1 - sig(o) + 1e-9))).mean()
    # the carry before the first step is 0: supervise the carry readout at h0 = 0 (reads bc alone)
    c0 = P["Wc"] @ hs[0][0] + P["bc"]
    dc0 = (sig(c0) - 0.0)
    if margin_w > 0:
        dc0 += margin_w * (-np.sign(c0)) * (np.abs(c0) < margin)
    g["Wc"] += dc0[:, None] * hs[0][0][None, :]; g["bc"] += dc0
    dh_next = np.zeros((B, H))
    for t in reversed(range(L)):
        x = np.stack([a[:, t], b[:, t]], 1).astype(float)
        h = hs[t + 1]; hprev = hs[t]; pre = pres[t]
        g["Wo"] += do[:, t:t+1].T @ h; g["Wox"] += do[:, t:t+1].T @ x; g["bo"] += do[:, t].sum()
        g["Wc"] += dc[:, t:t+1].T @ h; g["bc"] += dc[:, t].sum()
        dh = do[:, t:t+1] * P["Wo"] + dc[:, t:t+1] * P["Wc"] + dh_next
        sk = sig(K * pre)
        dpre = dh * K * sk * (1 - sk)   # exact for soft mode, surrogate for hard mode
        if margin_w > 0:   # hinge pushing |pre| above margin
            dpre += margin_w * (-np.sign(pre)) * (np.abs(pre) < margin) / (B * L)
        g["Wh"] += dpre.T @ hprev; g["Wx"] += dpre.T @ x; g["bh"] += dpre.sum(0)
        dh_next = dpre @ P["Wh"]
    for k in P:
        if k in ("Wh", "Wx", "Wo", "Wox", "Wc"):
            P[k] -= lr * wd * P[k]
        m[k] = b1 * m[k] + (1 - b1) * g[k]
        v[k] = b2 * v[k] + (1 - b2) * g[k] ** 2
        P[k] -= lr * (m[k] / (1 - b1 ** step)) / (np.sqrt(v[k] / (1 - b2 ** step)) + 1e-8)
    if (step % 500 == 0 and not A.quiet) or step == steps:
        r = {L: evaluate(P, L) for L in (16, 64, 128)}
        print(f"step {step} loss {loss:.4f} " + " ".join(f"L{L}: bits {r[L][0]:.4f} seq {r[L][1]:.4f}" for L in r)
              + f"  ({time.time()-t0:.0f}s)", flush=True)
np.savez(out, H=H, seed=seed, steps=steps, carry_sup=carry_sup, mode=mode, K=K, lr=lr, wd=wd, margin_w=margin_w, margin=margin, **params)
print("saved", out)
