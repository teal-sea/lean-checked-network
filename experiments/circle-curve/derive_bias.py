"""Derive the bias from the clock alone. For a one-wave neuron h with readout C_h cos(k_h c + psi_h) and
mean squared activation m_h, the clock's per-class baseline is
    baseline[c] = sum_k Re( e^{2 pi i k c / p} Z_k ),   Z_k = sum_{h in cluster k} m_h C_h e^{i psi_h}.
It vanishes exactly when every frequency cluster's readout phasors cancel (|Z_k| = 0). The trained net keeps
its own class marginal flat (the loss pushes a per-class offset to zero), so whatever baseline the clock
leaves must be cancelled by the rest of the readout: bias = -baseline (+ const).
Per cell: cluster imbalance sum_k |Z_k| / sum_h m_h |C_h|, baseline spread / margin, net marginal spread /
margin, and the wrong counts. Medians over seeds per configuration."""
import glob, os, collections, numpy as np
def logits(E1, E2, W2, p):
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p)
    return ((E1[a] + E2[b]) ** 2) @ W2.T, (a + b) % p
rows = collections.defaultdict(list)
for f in sorted(glob.glob("final_weights/*.npz")):
    name = os.path.basename(f)[:-4]
    if name.startswith("LONG"): continue
    d = np.load(f); p, H = int(d['p']), int(d['H']); half = (p - 1) // 2
    cols = [d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    one = [np.zeros(c.shape, dtype=np.int64) for c in cols]; ks = []; Cph = []
    for h in range(H):
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1; ks.append(k)
        for F, o in zip(Fs, one):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
        Cph.append(2 * Fs[2][k] / p)          # C_h e^{i psi_h} for the readout wave
    S, c = logits(*cols, p); S1, _ = logits(*one, p)
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p)
    m = ((one[0][a] + one[1][b]) ** 2).mean(0)
    Z = collections.defaultdict(complex)
    for h in range(H): Z[ks[h]] += m[h] * Cph[h]
    imb = sum(abs(z) for z in Z.values()) / max(1e-9, sum(m[h] * abs(Cph[h]) for h in range(H)))
    gap = np.median(np.sort(S1, 1)[:, -1] - np.sort(S1, 1)[:, -2])
    base = S1.mean(0); marg = S.mean(0)
    bias = (cols[2] - one[2]) @ m
    w1 = int((S1.argmax(1) != c).sum()); wb = int(((S1 + bias).argmax(1) != c).sum()); wn = int((S.argmax(1) != c).sum())
    rows[name.rsplit("_s", 1)[0]].append((wn, w1, wb, imb, base.std() / gap, marg.std() / gap, len(set(ks))))
print(f"{'config':24s}  net  1wave  +bias | imbalance  base/gap  netmarg/gap  freqs   (medians over seeds)")
for k in sorted(rows, key=lambda s: (float(s.split('_wd')[1]), s)):
    v = np.median(np.array(rows[k]), 0)
    print(f"{k:24s} {v[0]:5.0f} {v[1]:6.0f} {v[2]:6.0f} |   {v[3]:.2f}      {v[4]:.2f}       {v[5]:.2f}      {v[6]:.0f}")
