"""Smallest frequency set S at p=113 whose 8|S|-neuron fixed-phase network survives rounding at scale M."""
import sys, itertools, numpy as np
p, M = 113, int(sys.argv[1])
K = list(range(1, 57)); x = np.arange(p); s = np.arange(1, p)
def gap(S): return len(S) - sum(np.cos(2*np.pi*k*s/p) for k in S).max()
phis = [(a*np.pi/2, b*np.pi/2) for a in range(4) for b in range(2)]
a, b = np.divmod(np.arange(p*p), p); target = (a+b) % p
def test(S):
    E1, E2, W2 = [], [], []
    for k in S:
        for f1, f2 in phis:
            E1.append(np.cos(2*np.pi*k*x/p + f1)); E2.append(np.cos(2*np.pi*k*x/p + f2)); W2.append(np.cos(2*np.pi*k*x/p + f1 + f2))
    E1q, E2q, W2q = (np.round(M*np.array(t).T).astype(np.int64) for t in (E1, E2, W2))
    z = E1q[a] + E2q[b]; Sc = (z*z) @ W2q.T
    top2 = np.sort(Sc, 1)[:, -2:]
    return int((Sc.argmax(1) != target).sum()), int((top2[:,0] == top2[:,1]).sum()), int((top2[:,1]-top2[:,0]).min())
for size in (1, 2, 3):
    cands = sorted(itertools.combinations(K, size), key=lambda S: -gap(S))
    print(f"|S|={size}: {len(cands)} sets, best gap {gap(cands[0]):.4f} at {cands[0]}", flush=True)
    found = None
    for i, S in enumerate(cands[:400]):
        w, t, g = test(S)
        if w == 0 and t == 0:
            found = (S, gap(S), g, i); break
    print(f"  first survivor at M={M}: {found}", flush=True)
    if found: break
