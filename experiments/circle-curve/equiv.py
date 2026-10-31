"""An adder's logit table is translation-equivariant: S[a, b, c] = f((c - a - b) mod p). Split the
one-wave network's table into its equivariant part and the remainder, and the remainder into a
c-only part (the per-class baseline the bias cancels), an (a, c) part, a (b, c) part and the rest.
Report each part's spread relative to the one-wave median margin, and the wrong counts of the
one-wave net with each correction removed. For wd 0 cells also report the orbit average of the FULL
net's table over all pairs and over held-out pairs only (does the memorizer's own function carry an
adder?). Usage: python3 equiv.py final_weights [pattern]"""
import glob, os, sys, numpy as np

def onewave(cols, p, H):
    half = (p - 1) // 2; out = [np.zeros(c.shape, dtype=np.int64) for c in cols]
    for h in range(H):
        if not any(np.any(c[:, h]) for c in cols): continue
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1
        for F, o in zip(Fs, out):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    return out

def table(cols, p):
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p)
    return (((cols[0][a] + cols[1][b]) ** 2) @ cols[2].T).reshape(p, p, p).astype(float)

def dgrid(p):
    a = np.arange(p)[:, None, None]; b = np.arange(p)[None, :, None]; c = np.arange(p)[None, None, :]
    return (c - a - b) % p

def orbit_average(T, p, mask=None):
    """f(d) = mean of T[a, b, c] over the pairs (a, b) in mask (all pairs if None) with c - a - b = d."""
    d = dgrid(p); f = np.zeros(p)
    m = np.ones((p, p), bool) if mask is None else mask
    for t in range(p):
        sel = (d == t) & m[:, :, None]
        f[t] = T[sel].mean()
    return f

def parts(T, p):
    d = dgrid(p); f = orbit_average(T, p); Teq = f[d]; R = T - Teq
    Rc = R.mean(axis=(0, 1), keepdims=True); R1 = R - Rc
    Rac = R1.mean(axis=1, keepdims=True); Rbc = R1.mean(axis=0, keepdims=True)
    return Teq, Rc, Rac, Rbc, R1 - Rac - Rbc, f

def wrong(T, p):
    c = (np.arange(p)[:, None] + np.arange(p)[None, :]) % p
    return int((T.argmax(2) != c).sum())

if __name__ == '__main__':
    FW = sys.argv[1]; pat = sys.argv[2] if len(sys.argv) > 2 else '*'
    print(f"{'cell':30s} ho    | gap     | spread/gap: c-only (a,c) (b,c) rest | wrong: net 1wave 1w-c 1w-c-ac-bc eq-part | full-net orbit avg: all-pairs margin/gap, held-out-only margin/gap")
    for f in sorted(glob.glob(f"{FW}/{pat}.npz")):
        d = np.load(f); p, H = int(d['p']), int(d['H']); name = os.path.basename(f)[:-4]
        cols = [d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
        one = onewave(cols, p, H); T = table(cols, p); T1 = table(one, p)
        s = np.sort(T1, 2); gap = float(np.median(s[..., -1] - s[..., -2]))
        Teq, Rc, Rac, Rbc, Rrest, f1 = parts(T1, p)
        # full net's own orbit averages (its function, not its weights)
        sN = np.sort(T, 2); gapN = float(np.median(sN[..., -1] - sN[..., -2]))
        tr = np.zeros(p * p, bool); tr[d['train_idx']] = True; ho = ~tr.reshape(p, p)
        fa = orbit_average(T, p); fh = orbit_average(T, p, ho)
        ma = (fa[0] - np.sort(fa)[-2]) / gapN; mh = (fh[0] - np.sort(fh)[-2]) / gapN
        print(f"{name:30s} {float(d['heldout_acc']):.3f} | {gap:7.0f} | {Rc.std()/gap:5.2f} {Rac.std()/gap:5.2f} {Rbc.std()/gap:5.2f} {Rrest.std()/gap:5.2f} | {wrong(T,p):5d} {wrong(T1,p):5d} {wrong(T1-Rc,p):5d} {wrong(T1-Rc-Rac-Rbc,p):5d} {wrong(Teq,p):5d} | {ma:+6.2f} {mh:+6.2f} (peak d={int(np.argmax(fh))})", flush=True)
