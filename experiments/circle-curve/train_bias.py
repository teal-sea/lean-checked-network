"""train_ckpt2.py plus ONE change: an explicit output bias vector (p entries) added to the logits,
trained by the same Adam, with weight decay BIAS_WD (env, default 0). Kill test for the claim that the
readout's off-frequency components exist only to flatten the clock's per-class baseline.

Usage: python3 train_ckpt.py P HIDDEN SEED LR WD TRAIN_FRACTION STEPS OUTDIR
Writes OUTDIR/ckpt_step{N}.npz at the scheduled steps and OUTDIR/final.npz.
"""
import os
import sys
import numpy as np

p, H, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
lr, wd, frac, steps, outdir = float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7]), sys.argv[8]
os.makedirs(outdir, exist_ok=True)

sched = set(list(range(100, 1001, 100)) + list(range(1250, 4001, 250)) + list(range(4500, 10001, 500)) + list(range(11000, min(steps, 20000) + 1, 1000)) + list(range(30000, steps + 1, 10000)))

rng = np.random.default_rng(seed)
pairs = np.array([(a, b) for a in range(p) for b in range(p)])
labels = (pairs[:, 0] + pairs[:, 1]) % p
SHUFFLE = os.environ.get('SHUFFLE_LABELS') == '1'
perm = rng.permutation(len(pairs))
n_train = int(round(frac * len(pairs)))
tr, te = perm[:n_train], perm[n_train:]
if SHUFFLE:
    labels = labels.copy(); labels[tr] = labels[tr][rng.permutation(n_train)]  # control: training labels permuted
onehot = np.eye(p)

E1 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
E2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
W2 = rng.normal(0, 1, (p, H)) / np.sqrt(H)
bias = np.zeros(p)
BIAS_WD = float(os.environ.get('BIAS_WD', '0'))
params = [E1, E2, W2, bias]
m = [np.zeros_like(x) for x in params]
v = [np.zeros_like(x) for x in params]
b1, b2 = 0.9, 0.98
A_tr, B_tr = onehot[pairs[tr, 0]], onehot[pairs[tr, 1]]


def scores(E1, E2, W2, bias, idx):
    z = E1[pairs[idx, 0]] + E2[pairs[idx, 1]]
    return (z * z) @ W2.T + bias


def acc(idx):
    return float((scores(*params, idx).argmax(1) == labels[idx]).mean())


def freeze(x):
    return np.round(x * (127 / np.abs(x).max())).astype(np.int64)


def save(path, step):
    E1q, E2q, W2q = (freeze(x) for x in params[:3])
    z = E1q[pairs[:, 0]] + E2q[pairs[:, 1]]
    Sq = (z * z) @ W2q.T
    # the bias in the frozen net's units: E1 and E2 are frozen with separate scales, so the logit
    # scale is estimated as the ratio of frozen to float logit spread (bias-free, all pairs)
    zf = params[0][pairs[:, 0]] + params[1][pairs[:, 1]]
    Sf = (zf * zf) @ params[2].T
    scale = float(np.linalg.norm(Sq - Sq.mean(1, keepdims=True)) / np.linalg.norm(Sf - Sf.mean(1, keepdims=True)))
    biasq = np.round(params[3] * scale).astype(np.int64)
    S = Sq + biasq
    pred = S.argmax(1)
    top2 = np.sort(S, 1)[:, -2:]
    wrong = int((pred != labels).sum())
    ties = int((top2[:, 0] == top2[:, 1]).sum())
    print(f"step {step}: train {acc(tr):.4f} held-out {acc(te):.4f} frozen wrong {wrong} ties {ties} gap {int((top2[:,1]-top2[:,0]).min())}",
          file=sys.stderr, flush=True)
    np.savez(path, p=p, H=H, seed=seed, lr=lr, wd=wd, frac=frac, steps=step, train_idx=tr,
             E1=params[0], E2=params[1], W2=params[2], bias=params[3], E1q=E1q, E2q=E2q, W2q=W2q, biasq=biasq, bias_scale=scale, bias_wd=BIAS_WD,
             train_acc=acc(tr), heldout_acc=acc(te))


save(os.path.join(outdir, 'ckpt_step0.npz'), 0)

for step in range(1, steps + 1):
    E1, E2, W2, bias = params
    z = E1[pairs[tr, 0]] + E2[pairs[tr, 1]]
    h = z * z
    logits = h @ W2.T + bias
    logits -= logits.max(1, keepdims=True)
    pr = np.exp(logits)
    pr /= pr.sum(1, keepdims=True)
    pr[np.arange(n_train), labels[tr]] -= 1
    g = pr / n_train
    gW2 = g.T @ h
    gz = (g @ W2) * 2 * z
    grads = [A_tr.T @ gz, B_tr.T @ gz, gW2, g.sum(0)]
    for i, gr in enumerate(grads):
        params[i] -= lr * (BIAS_WD if i == 3 else wd) * params[i]
        m[i] = b1 * m[i] + (1 - b1) * gr
        v[i] = b2 * v[i] + (1 - b2) * gr * gr
        params[i] -= lr * (m[i] / (1 - b1 ** step)) / (np.sqrt(v[i] / (1 - b2 ** step)) + 1e-8)
    if step in sched:
        save(os.path.join(outdir, f"ckpt_step{step}.npz"), step)

save(os.path.join(outdir, "final.npz"), steps)
