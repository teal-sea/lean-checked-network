"""Kill test for 'the readout's off-frequency components exist only to flatten the clock's baseline'.
Nets retrained with an explicit output bias (train_bias.py). Prediction: the readout residual shrinks
and the one-wave projection (plus the learned bias) matches the net. Compared cell by cell with the
same configuration trained without a bias (final_weights/)."""
import sys, glob, os, numpy as np
BIAS_DIR = sys.argv[1]
def logits(E1, E2, W2, p):
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p)
    return ((E1[a] + E2[b]) ** 2) @ W2.T, (a + b) % p
def onewave(cols, p, H):
    half = (p - 1) // 2; out = [np.zeros(c.shape, dtype=np.int64) for c in cols]
    for h in range(H):
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1
        for F, o in zip(Fs, out):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    return out
def stats(d, with_bias):
    p, H = int(d['p']), int(d['H'])
    cols = [d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    bias = d['biasq'].astype(np.int64) if with_bias else np.zeros(p, dtype=np.int64)
    one = onewave(cols, p, H)
    S, c = logits(*cols, p); S1, _ = logits(*one, p)
    net = int(((S + bias).argmax(1) != c).sum())
    w1 = int((S1.argmax(1) != c).sum()); w1b = int(((S1 + bias).argmax(1) != c).sum())
    res_share = float(((cols[2] - one[2]) ** 2).sum() / (cols[2] ** 2).sum())
    emb_res = float((((cols[0] - one[0]) ** 2).sum() + ((cols[1] - one[1]) ** 2).sum()) / ((cols[0] ** 2).sum() + (cols[1] ** 2).sum()))
    base = S1.mean(0); gap = np.median(np.sort(S1, 1)[:, -1] - np.sort(S1, 1)[:, -2])
    corr = float(np.corrcoef(bias, base)[0, 1]) if with_bias and bias.std() > 0 else float('nan')
    return dict(net=net, one=w1, one_bias=w1b, res=res_share, emb_res=emb_res, base_gap=float(base.std() / gap), corr=corr, ho=float(d['heldout_acc']))
rows = []
files = sorted(glob.glob(f"{BIAS_DIR}/*/final.npz")) or sorted(glob.glob(f"{BIAS_DIR}/*.npz"))
for f in files:
    name = os.path.basename(os.path.dirname(f)) if f.endswith("final.npz") else os.path.basename(f)[:-4]
    b = stats(np.load(f), True)
    g = stats(np.load(f"final_weights/{name}.npz"), False) if os.path.exists(f"final_weights/{name}.npz") else None
    rows.append((name, b, g))
print(f"{'cell':28s} | with bias: net  1wave  1wave+b  W2res  corr(b,-base) | no bias: net  1wave  W2res  base/gap")
for name, b, g in rows:
    gs = f"{g['net']:4d} {g['one']:5d} {g['res']:.3f} {g['base_gap']:.2f}" if g else "   (no matched cell)"
    print(f"{name:28s} | {b['net']:4d} {b['one']:5d} {b['one_bias']:5d}   {b['res']:.3f}  {-b['corr']:+.2f}   | {gs}")
