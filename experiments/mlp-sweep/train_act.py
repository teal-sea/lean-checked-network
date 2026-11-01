"""experiments/circle-curve/train_ckpt2.py with the activation as the first argument (2026-11-01).

Usage: python3 train_act.py ACT P HIDDEN SEED LR WD TRAIN_FRACTION STEPS OUTDIR, ACT in {sq, relu}.
ACT sq is train_ckpt2.py exactly (x^2). EXTRA_STEPS=1,2,3 (environment) adds checkpoints at those steps.
NOISE_FRAC=f (fifth batch) replaces the labels of a fraction f of the training pairs by wrong ones. ACT relu replaces x^2 by max(x, 0) in the forward pass, the
frozen evaluation and the gradient ((z > 0) for 2z); nothing else changes (same init, AdamW-style
decoupled weight decay, lr, schedule, 8-bit freezing, checkpoint format plus an `act` field).
"""
import os
import sys
import numpy as np

ACT = sys.argv.pop(1)
assert ACT in ('sq', 'relu')
act = (lambda z: z * z) if ACT == 'sq' else (lambda z: np.maximum(z, 0))
p, H, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
lr, wd, frac, steps, outdir = float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7]), sys.argv[8]
os.makedirs(outdir, exist_ok=True)

sched = set(([5, 10, 15, 20, 30, 40, 50, 75] if os.environ.get('EARLY') == '1' else []) + list(range(100, 1001, 100)) + list(range(1250, 4001, 250)) + list(range(4500, 10001, 500)) + list(range(11000, min(steps, 20000) + 1, 1000)) + list(range(30000, steps + 1, 10000)))
sched |= {int(x) for x in os.environ.get('EXTRA_STEPS', '').split(',') if x}  # e.g. EXTRA_STEPS=1,2,3,4

rng = np.random.default_rng(seed)
pairs = np.array([(a, b) for a in range(p) for b in range(p)])
labels = (pairs[:, 0] + pairs[:, 1]) % p
SHUFFLE = os.environ.get('SHUFFLE_LABELS') == '1'
perm = rng.permutation(len(pairs))
n_train = int(round(frac * len(pairs)))
tr, te = perm[:n_train], perm[n_train:]
if SHUFFLE:
    labels = labels.copy(); labels[tr] = labels[tr][rng.permutation(n_train)]  # control: training labels permuted
NOISE = float(os.environ.get('NOISE_FRAC', '0'))
if NOISE > 0:  # fifth batch: this fraction of the training labels replaced by wrong ones, drawn from a separate generator so that the init is the clean run's
    nrng = np.random.default_rng(10_000 + seed)
    noisy = nrng.choice(tr, int(round(NOISE * n_train)), replace=False)
    labels = labels.copy(); labels[noisy] = (labels[noisy] + nrng.integers(1, p, len(noisy))) % p
onehot = np.eye(p)

E1 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
E2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
W2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
params = [E1, E2, W2]
m = [np.zeros_like(x) for x in params]
v = [np.zeros_like(x) for x in params]
b1, b2 = 0.9, 0.98
A_tr, B_tr = onehot[pairs[tr, 0]], onehot[pairs[tr, 1]]


def scores(E1, E2, W2, idx):
    z = E1[pairs[idx, 0]] + E2[pairs[idx, 1]]
    return act(z) @ W2.T


def acc(idx):
    return float((scores(*params, idx).argmax(1) == labels[idx]).mean())


def freeze(x):
    return np.round(x * (127 / np.abs(x).max())).astype(np.int64)


def save(path, step):
    E1q, E2q, W2q = (freeze(x) for x in params)
    z = E1q[pairs[:, 0]] + E2q[pairs[:, 1]]
    S = act(z) @ W2q.T
    pred = S.argmax(1)
    top2 = np.sort(S, 1)[:, -2:]
    wrong = int((pred != labels).sum())
    ties = int((top2[:, 0] == top2[:, 1]).sum())
    print(f"step {step}: train {acc(tr):.4f} held-out {acc(te):.4f} frozen wrong {wrong} ties {ties} gap {int((top2[:,1]-top2[:,0]).min())}",
          file=sys.stderr, flush=True)
    np.savez(path, act=ACT, noise_frac=NOISE, p=p, H=H, seed=seed, lr=lr, wd=wd, frac=frac, steps=step, train_idx=tr,
             E1=params[0], E2=params[1], W2=params[2], E1q=E1q, E2q=E2q, W2q=W2q,
             train_acc=acc(tr), heldout_acc=acc(te))


save(os.path.join(outdir, 'ckpt_step0.npz'), 0)

for step in range(1, steps + 1):
    E1, E2, W2 = params
    z = E1[pairs[tr, 0]] + E2[pairs[tr, 1]]
    h = act(z)
    logits = h @ W2.T
    logits -= logits.max(1, keepdims=True)
    pr = np.exp(logits)
    pr /= pr.sum(1, keepdims=True)
    pr[np.arange(n_train), labels[tr]] -= 1
    g = pr / n_train
    gW2 = g.T @ h
    gz = (g @ W2) * (2 * z if ACT == 'sq' else (z > 0))
    grads = [A_tr.T @ gz, B_tr.T @ gz, gW2]
    for i, gr in enumerate(grads):
        params[i] -= lr * wd * params[i]
        m[i] = b1 * m[i] + (1 - b1) * gr
        v[i] = b2 * v[i] + (1 - b2) * gr * gr
        params[i] -= lr * (m[i] / (1 - b1 ** step)) / (np.sqrt(v[i] / (1 - b2 ** step)) + 1e-8)
    if step in sched:
        save(os.path.join(outdir, f"ckpt_step{step}.npz"), step)

save(os.path.join(outdir, "final.npz"), steps)
