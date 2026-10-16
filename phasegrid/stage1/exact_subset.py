"""p = 1009, S = [1]: the derived bound is M > 24/g = 1.24e6, where scores exceed int64. Exact Python
integers on a subset of rows a, all b and c: M just above and just below the bound, plus a scan of small M."""
import numpy as np, sys, time
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
from rounding2 import build_int, gap
p, S = 1009, [1]
g = gap(p, S); B = 24*len(S)/g
rows = sorted(np.random.default_rng(1009).choice(p, size=12, replace=False).tolist())
print(f"p={p} S={S} g={g:.6g} bound 24|S|/g={B:.6g}; rows a tested: {rows}")
def check_exact(M):
    (e1, e2, w), hd = build_int(p, S, M)
    E1, E2, W = (A.astype(object) for A in (e1, e2, w))
    U = (E1*E1) @ W.T; V = (E2*E2) @ W.T
    wrong = ties = 0; margin = None
    for a in rows:
        I = U[a][None, :] + V + 2*((E1[a]*E2) @ W.T)
        tgt = (a + np.arange(p)) % p
        best = I[np.arange(p), tgt]
        I2 = I.copy(); I2[np.arange(p), tgt] = -10**40
        other = I2.max(1)
        ans = np.array([int(np.argmax(row)) for row in I])  # first index on a tie
        wrong += int((ans != tgt).sum()); ties += int((other == best).sum())
        m = int((best - other).min()); margin = m if margin is None else min(margin, m)
    return wrong, ties, margin, hd
for M in (int(B) + 1, int(B)):
    t = time.time(); w, ti, m, hd = check_exact(M)
    print(f"  M={M} ({'just above' if M > B else 'just below'}): wrong={w} ties={ti} min margin={m} (derived lower bound {4*g*M**3-96*M**2:.4g}) half-int dist={hd:.1e} [{time.time()-t:.1f}s]", flush=True)
fails = []
for M in range(1, 31):
    w, ti, m, hd = check_exact(M)
    if w or ti: fails.append((M, w, ti))
print(f"  scan M=1..30 on these rows: failing M (wrong, ties) = {fails}")
