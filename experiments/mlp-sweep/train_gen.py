"""train_act.py generalized (2026-11-01): more activations and a plain-SGD option, for the generality tests.

Usage: python3 train_gen.py ACT P HIDDEN SEED LR WD TRAIN_FRACTION STEPS OUTDIR
  ACT in {sq, relu, gelu, silu, abs, tanh}; gelu is the tanh approximation. Added for the fourth
  batch (RULES.md): gelus, silus, tanhs, the activation f(s z) / s with s from the environment
  ACT_S (default 1), saved as act_s; the six earlier activations are unchanged. Added for the sixth
  batch: sqlin (z^2 + c z) and tanhsq (tanh(z) + c z^2), c from ACT_C (default 0), saved as act_c.
  Environment: OPT=sgd
  replaces the Adam step by params -= lr * grad (decoupled weight decay unchanged); EXTRA_STEPS,
  EARLY, SHUFFLE_LABELS as in train_act.py. ACT sq and relu with OPT unset compute exactly what
  train_act.py computes. The float weights E1, E2, W2 are what matter for gelu/silu/tanh (not
  scale-invariant, so the 8-bit frozen copies are not meaningful for them); see analyze_gen.py.
Prediction fixed before running: the projection needs an even part in the activation (a z^2 term
near zero carries the a+b product), so gelu, silu and abs behave like sq and relu, and tanh fails.
"""
import os
import sys
import numpy as np

ACT = sys.argv.pop(1)
OPT = os.environ.get('OPT', 'adam')
SCALE = float(os.environ.get('ACT_S', '1'))  # not S: save() uses S for its scores
COEF = float(os.environ.get('ACT_C', '0'))
assert OPT in ('adam', 'sgd')
_C = np.sqrt(2 / np.pi)


def _gelu(z):
    return 0.5 * z * (1 + np.tanh(_C * (z + 0.044715 * z ** 3)))


def _dgelu(z):
    t = np.tanh(_C * (z + 0.044715 * z ** 3))
    return 0.5 * (1 + t) + 0.5 * z * (1 - t * t) * _C * (1 + 3 * 0.044715 * z * z)


def _sig(z):
    return 1 / (1 + np.exp(-z))


ACTS = {'sq': (lambda z: z * z, lambda z: 2 * z),
        'relu': (lambda z: np.maximum(z, 0), lambda z: (z > 0)),
        'gelu': (_gelu, _dgelu),
        'silu': (lambda z: z * _sig(z), lambda z: _sig(z) * (1 + z * (1 - _sig(z)))),
        'abs': (np.abs, np.sign),
        'tanh': (np.tanh, lambda z: 1 - np.tanh(z) ** 2),
        'gelus': (lambda z: _gelu(SCALE * z) / SCALE, lambda z: _dgelu(SCALE * z)),
        'silus': (lambda z: z * _sig(SCALE * z), lambda z: _sig(SCALE * z) * (1 + SCALE * z * (1 - _sig(SCALE * z)))),
        'tanhs': (lambda z: np.tanh(SCALE * z) / SCALE, lambda z: 1 - np.tanh(SCALE * z) ** 2),
        'sqlin': (lambda z: z * z + COEF * z, lambda z: 2 * z + COEF),
        'tanhsq': (lambda z: np.tanh(z) + COEF * z * z, lambda z: 1 - np.tanh(z) ** 2 + 2 * COEF * z)}
assert ACT in ACTS
act, dact = ACTS[ACT]
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
    np.savez(path, act=ACT, act_s=SCALE, act_c=COEF, opt=OPT, p=p, H=H, seed=seed, lr=lr, wd=wd, frac=frac, steps=step, train_idx=tr,
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
    gz = (g @ W2) * dact(z)
    grads = [A_tr.T @ gz, B_tr.T @ gz, gW2]
    for i, gr in enumerate(grads):
        params[i] -= lr * wd * params[i]
        if OPT == 'sgd':
            params[i] -= lr * gr
            continue
        m[i] = b1 * m[i] + (1 - b1) * gr
        v[i] = b2 * v[i] + (1 - b2) * gr * gr
        params[i] -= lr * (m[i] / (1 - b1 ** step)) / (np.sqrt(v[i] / (1 - b2 ** step)) + 1e-8)
    if step in sched:
        save(os.path.join(outdir, f"ckpt_step{step}.npz"), step)

save(os.path.join(outdir, "final.npz"), steps)
