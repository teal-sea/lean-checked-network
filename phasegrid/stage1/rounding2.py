"""Stage 1b, this session's run: the integer phase-grid network at modulus p; M just above and below
the derived bound 24|S|/g(S); a scan of small M.  Same construction as rounding.py (half-up rounding
with exact handling of values at a half-integer), restructured so that p = 1009 with all 504
frequencies (4032 neurons) is feasible: single-threaded BLAS, no per-M scan on the big set.

Usage: python3 -I rounding2.py p [scan_cap] [--big]
"""
import sys, time
import numpy as np

def gap(p, S):
    s = np.arange(1, p)
    return len(S) - sum(np.cos(2*np.pi*k*s/p) for k in S).max()

def build_int(p, S, M):
    phis = [(j*np.pi/2, l*np.pi/2) for j in range(4) for l in range(2)]
    x = np.arange(p)
    c1, c2, cw = [], [], []
    for k in S:
        for f1, f2 in phis:
            c1.append(M*np.cos(2*np.pi*k*x/p + f1))
            c2.append(M*np.cos(2*np.pi*k*x/p + f2))
            cw.append(M*np.cos(2*np.pi*k*x/p + f1 + f2))
    reals = [np.array(c).T for c in (c1, c2, cw)]
    half_dist = min(np.abs((r + 0.5) - np.round(r + 0.5)).min() for r in reals)
    ints = []
    for r in reals:
        q = np.floor(r + 0.5)
        near = np.abs((r - 0.5) - np.round(r - 0.5)) < 1e-9   # exactly at n + 1/2 up to float noise: round up
        q[near] = np.round(r[near] - 0.5) + 1
        ints.append(q.astype(np.int64))
    return ints, half_dist

def check(p, S, M, rows=None):
    (e1, e2, w), half_dist = build_int(p, S, M)
    H = e1.shape[1]
    bound_score = 4 * H * M**3
    use_float = bound_score < 2**52
    assert bound_score < 2**62
    cast = (lambda A: A.astype(np.float64)) if use_float else (lambda A: A)
    E1, E2, W = cast(e1), cast(e2), cast(w)
    U = (E1*E1) @ W.T
    V = (E2*E2) @ W.T
    wrong = ties = 0; margin = None
    for a in (range(p) if rows is None else rows):
        X = (E1[a] * E2) @ W.T
        I = U[a][None, :] + V + 2*X
        if use_float:
            I = np.rint(I).astype(np.int64)
        tgt = (a + np.arange(p)) % p
        wrong += int((I.argmax(1) != tgt).sum())
        best = I[np.arange(p), tgt]
        I2 = I.copy(); I2[np.arange(p), tgt] = np.iinfo(np.int64).min
        other = I2.max(1)
        ties += int((other == best).sum())
        m = int((best - other).min()); margin = m if margin is None else min(margin, m)
    return wrong, ties, margin, half_dist

def run_case(p, S, label, scan_cap, rows=None):
    g = gap(p, S); n = len(S); bound = 24*n/g
    above = int(np.floor(bound)) + 1; below = int(np.ceil(bound)) - 1
    print(f"\n[{label}] p={p} S={S if n <= 8 else f'{n} freqs 1..{S[-1]}'} |S|={n} H={8*n} g(S)={g:.6g} 24|S|/g={bound:.4g}"
          + ("" if rows is None else f"  (rows a in a subset of {len(rows)} of {p})"), flush=True)
    for M, tag in [(above, "just above"), (below, "just below")]:
        if M < 1: continue
        t = time.time()
        wrong, ties, margin, hd = check(p, S, M, rows)
        print(f"  M={M} ({tag}): wrong={wrong} ties={ties} min margin={margin} "
              f"(derived lower bound 4gM^3-96|S|M^2={4*g*M**3-96*n*M**2:.4g}) half-int dist={hd:.1e} [{time.time()-t:.1f}s]", flush=True)
    cap = min(below, scan_cap)
    if cap >= 1:
        fails = []
        for M in range(1, cap + 1):
            wrong, ties, margin, hd = check(p, S, M, rows)
            if wrong or ties: fails.append((M, wrong, ties))
        ok = [M for M in range(1, cap + 1) if M not in {f[0] for f in fails}]
        print(f"  scan M=1..{cap}: failing M (wrong, ties) = {fails if fails else 'none'}; "
              f"smallest M with no wrong answer and no tie = {min(ok) if ok else 'none in range'}", flush=True)

if __name__ == "__main__":
    p = int(sys.argv[1]); scan_cap = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 40
    big = "--big" in sys.argv
    rng = np.random.default_rng(p)
    full = list(range(1, (p-1)//2 + 1)); top = (p-1)//2
    cases = []
    if big:
        rows = sorted(rng.choice(p, size=40, replace=False).tolist())
        cases.append((full, "all frequencies", None, 0))          # all rows, no scan
        cases.append((full, "all frequencies, M = 25", None, -1))
    else:
        cases.append((full, "all frequencies", None, scan_cap))
    if top >= 3: cases.append(([1, 2, 3], "adversarial, small gap {1,2,3}", None, min(scan_cap, 30)))
    cases.append(([1], "adversarial, smallest gap {1}", None, min(scan_cap, 30)))
    for d in (3, 5):
        if top >= d:
            Sr = sorted(rng.choice(np.arange(1, top + 1), size=d, replace=False).tolist())
            cases.append((Sr, f"random {d}", None, min(scan_cap, 30)))
    if p == 113: cases.append(([14, 35, 41, 42, 52], "Nanda's five", None, 30))
    for Sx, label, rows, cap in cases:
        if cap == -1:
            t = time.time(); wrong, ties, margin, hd = check(p, Sx, 25, rows)
            print(f"\n[{label}] p={p} |S|={len(Sx)} H={8*len(Sx)}: M=25: wrong={wrong} ties={ties} min margin={margin} half-int dist={hd:.1e} [{time.time()-t:.1f}s]", flush=True)
        else:
            run_case(p, Sx, label, cap, rows)
