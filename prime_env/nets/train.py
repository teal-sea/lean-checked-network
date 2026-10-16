"""Train a two-layer network to add modulo p, then freeze its weights to integers.

Architecture (Gromov 2023, "Grokking modular arithmetic"): the two inputs a and b each pick a
row of an embedding table, the rows are added, each entry is squared, and a final table turns
the result into one score per possible answer c. The answer is the c with the highest score.

The network trains on a random fraction of all p*p pairs. The frozen integer version is the
object every later check, including the Lean proof, is about.

Usage: python3 train.py P HIDDEN SEED LR WD TRAIN_FRACTION STEPS OUT.npz
"""
import sys
import numpy as np

p, H, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
lr, wd, frac, steps, out = float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7]), sys.argv[8]

rng = np.random.default_rng(seed)
pairs = np.array([(a, b) for a in range(p) for b in range(p)])
labels = (pairs[:, 0] + pairs[:, 1]) % p
perm = rng.permutation(len(pairs))
n_train = int(round(frac * len(pairs)))
tr, te = perm[:n_train], perm[n_train:]
onehot = np.eye(p)

E1 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
E2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
W2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)   # one row per answer c
params = [E1, E2, W2]
m = [np.zeros_like(x) for x in params]
v = [np.zeros_like(x) for x in params]
b1, b2 = 0.9, 0.98
A_tr, B_tr = onehot[pairs[tr, 0]], onehot[pairs[tr, 1]]

def scores(E1, E2, W2, idx):
    z = E1[pairs[idx, 0]] + E2[pairs[idx, 1]]
    return (z * z) @ W2.T

def acc(idx):
    return float((scores(*params, idx).argmax(1) == labels[idx]).mean())

def freeze(x):
    """Round to whole numbers in [-127, 127], one scale per table."""
    return np.round(x * (127 / np.abs(x).max())).astype(np.int64)

def save(path, step):
    E1q, E2q, W2q = (freeze(x) for x in params)
    z = E1q[pairs[:, 0]] + E2q[pairs[:, 1]]
    S = (z * z) @ W2q.T
    pred = S.argmax(1)
    top2 = np.sort(S, 1)[:, -2:]
    wrong = int((pred != labels).sum())
    ties = int((top2[:, 0] == top2[:, 1]).sum())
    print(f"  step {step} frozen integer network: wrong on {wrong} of {p*p}, ties {ties}, "
          f"smallest winning gap {int((top2[:,1]-top2[:,0]).min())}", file=sys.stderr, flush=True)
    np.savez(path, p=p, H=H, seed=seed, lr=lr, wd=wd, frac=frac, steps=step, train_idx=tr,
             E1=params[0], E2=params[1], W2=params[2], E1q=E1q, E2q=E2q, W2q=W2q)

for step in range(1, steps + 1):
    E1, E2, W2 = params
    z = E1[pairs[tr, 0]] + E2[pairs[tr, 1]]
    h = z * z
    logits = h @ W2.T
    logits -= logits.max(1, keepdims=True)
    pr = np.exp(logits)
    pr /= pr.sum(1, keepdims=True)
    pr[np.arange(n_train), labels[tr]] -= 1
    g = pr / n_train
    gW2 = g.T @ h
    gz = (g @ W2) * 2 * z
    grads = [A_tr.T @ gz, B_tr.T @ gz, gW2]
    for i, gr in enumerate(grads):
        params[i] -= lr * wd * params[i]          # decoupled weight decay
        m[i] = b1 * m[i] + (1 - b1) * gr
        v[i] = b2 * v[i] + (1 - b2) * gr * gr
        params[i] -= lr * (m[i] / (1 - b1 ** step)) / (np.sqrt(v[i] / (1 - b2 ** step)) + 1e-8)
    if step % 2000 == 0:
        print(f"step {step}: train {acc(tr):.4f}  held-out {acc(te):.4f}", file=sys.stderr, flush=True)
        save(out.replace(".npz", f"_step{step}.npz"), step)

save(out, steps)
