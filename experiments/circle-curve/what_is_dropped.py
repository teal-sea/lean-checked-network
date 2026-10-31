"""Which part of the weights does the one-wave projection throw away that the network needs?
For each checkpoint file given: wrong count and smallest margin of the frozen net and of projections
that keep, per neuron at its dominant k: {k}, {0,k} (plus the DC offset), {0,k,2k}, {0,k,2k,3k},
{0,k,...,5k}; plus the energy share of DC and of each harmonic, median over live neurons.
Exact integer arithmetic for all counts (rounded tables, as the Lean definition evaluates)."""
import sys
import numpy as np


def wrong(E1, E2, W2, p):
    pairs = np.array([(a, b) for a in range(p) for b in range(p)])
    z = E1[pairs[:, 0]] + E2[pairs[:, 1]]
    S = (z * z) @ W2.T
    pred = S.argmax(1)
    lab = pairs.sum(1) % p
    top2 = np.sort(S, 1)[:, -2:]
    return int((pred != lab).sum()), int((top2[:, 1] - top2[:, 0]).min())


def project(cols, p, H, keep):
    half = (p - 1) // 2
    out = [np.zeros(c.shape, dtype=np.int64) for c in cols]
    shares = {"dc": [], "k": [], "2k": [], "3k": [], "rest": []}
    for h in range(H):
        if not any(np.any(c[:, h]) for c in cols):
            continue
        tot = np.zeros(half)
        Fs = []
        for c in cols:
            F = np.fft.fft(c[:, h])
            Fs.append(F)
            P = np.abs(F) ** 2
            tot += P[1:half + 1] + P[p - 1:p - half - 1:-1]
        k = int(np.argmax(tot)) + 1
        E = sum(float((np.abs(F) ** 2).sum()) for F in Fs)
        dc = sum(float(np.abs(F[0]) ** 2) for F in Fs)
        def band(m):
            kk = (m * k) % p
            return sum(float(np.abs(F[kk]) ** 2 + (np.abs(F[(-kk) % p]) ** 2 if kk != 0 else 0)) for F in Fs)
        b1, b2, b3 = band(1), band(2), band(3)
        shares["dc"].append(dc / E); shares["k"].append(b1 / E); shares["2k"].append(b2 / E); shares["3k"].append(b3 / E)
        shares["rest"].append(max(0.0, 1 - (dc + b1 + b2 + b3) / E))
        freqs = set()
        for m in keep:
            freqs.add((m * k) % p); freqs.add((-m * k) % p)
        for F, o in zip(Fs, out):
            G = np.zeros_like(F)
            for f in freqs:
                G[f] = F[f]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    return out, {kk: float(np.median(v)) for kk, v in shares.items()}


for path in sys.argv[1:]:
    d = np.load(path)
    p, H = int(d["p"]), int(d["H"])
    cols = [d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    nw, ng = wrong(*cols, p)
    line = f"{path.split('/')[-2]:26s} step {int(d['steps']):6d} | net {nw:5d} gap {ng:>10d}"
    for keep, name in [((1,), "k"), ((0, 1), "k+dc"), ((0, 1, 2), "k+dc+2k"), ((0, 1, 2, 3), "+3k"), ((0, 1, 2, 3, 4, 5), "+5k")]:
        out, sh = project(cols, p, H, keep)
        w, g = wrong(*out, p)
        line += f" | {name} {w:5d}"
    line += f" | shares dc {sh['dc']:.3f} k {sh['k']:.3f} 2k {sh['2k']:.3f} 3k {sh['3k']:.3f} rest {sh['rest']:.3f}"
    print(line, flush=True)
