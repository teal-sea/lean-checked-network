"""Stage 1b. The integer phase-grid network: does it add mod p, and where is the rounding threshold?

Integer tables, rounded half up as Lean's `round` does (round x = floor(x + 1/2)):
  e1[a,h] = round(M cos(2 pi k a/p + phi1)), e2[b,h] = round(M cos(2 pi k b/p + phi2)),
  w[c,h]  = round(M cos(2 pi k c/p + phi1 + phi2)),
8 neurons per k in S: phi1 in {0, pi/2, pi, 3pi/2}, phi2 in {0, pi/2}.
Score I(a,b,c) = sum_h w[c,h] (e1[a,h] + e2[b,h])^2, answer = first argmax over c.
The derived sufficient condition: M * g(S) > 24 |S|, with
  g(S) = |S| - max_{s = 1..p-1} sum_{k in S} cos(2 pi k s / p).

Usage: python3 rounding.py p [scan_cap]
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
    # distance to the nearest half-integer: if tiny, round-half-up in floats may differ from exact
    half_dist = min(np.abs((r + 0.5) - np.round(r + 0.5)).min() for r in reals)
    ints = []
    for r in reals:
        # exact half-up rounding as Lean's `round x = floor (x + 1/2)`: a value within 1e-9 of n + 1/2
        # (n an integer) rounds to n + 1, whatever floating-point noise says
        q = np.floor(r + 0.5)
        near = np.abs((r - 0.5) - np.round(r - 0.5)) < 1e-9
        q[near] = np.round(r[near] - 0.5) + 1
        ints.append(q.astype(np.int64))
    return ints, half_dist

def check(p, S, M):
    """Returns (wrong, ties_at_top, min_margin). Exact integer arithmetic (float64 BLAS when safe)."""
    (e1, e2, w), half_dist = build_int(p, S, M)
    H = e1.shape[1]
    bound_score = 4 * H * M**3          # |I| <= H * M * (2M)^2
    use_float = bound_score < 2**52
    if not use_float:
        assert bound_score < 2**62, "scores would overflow int64"
    cast = (lambda A: A.astype(np.float64)) if use_float else (lambda A: A)
    E1, E2, W = cast(e1), cast(e2), cast(w)
    U = (E1*E1) @ W.T            # p x p  [a, c]
    V = (E2*E2) @ W.T            # [b, c]
    wrong = 0; ties = 0; margin = None
    for a in range(p):
        X = (E1[a] * E2) @ W.T   # [b, c]  = sum_h e1[a,h] e2[b,h] w[c,h]
        I = U[a][None, :] + V + 2*X
        if use_float:
            I = np.rint(I).astype(np.int64)
        tgt = (a + np.arange(p)) % p
        ans = I.argmax(1)                      # first index on a tie, as the Lean argmax
        wrong += int((ans != tgt).sum())
        best = I[np.arange(p), tgt]
        I2 = I.copy(); I2[np.arange(p), tgt] = np.iinfo(np.int64).min
        other = I2.max(1)
        ties += int((other == best).sum())
        m = int((best - other).min())
        margin = m if margin is None else min(margin, m)
    return wrong, ties, margin, half_dist

def run_case(p, S, label, scan_cap):
    g = gap(p, S)
    n = len(S)
    bound = 24*n/g
    above = int(np.floor(bound)) + 1           # smallest integer M with M > bound
    below = int(np.ceil(bound)) - 1            # largest integer M with M < bound
    print(f"\n[{label}] p={p} S={S if n <= 8 else f'{n} freqs'} |S|={n} H={8*n} g(S)={g:.6g} 24|S|/g={bound:.4g}")
    for M, tag in [(above, "just above"), (below, "just below")]:
        if M < 1: continue
        t = time.time()
        wrong, ties, margin, hd = check(p, S, M)
        print(f"  M={M} ({tag}): wrong={wrong} ties={ties} min margin={margin} "
              f"(derived lower bound 4gM^3-96|S|M^2={4*g*M**3-96*n*M**2:.4g}) half-int dist={hd:.1e} [{time.time()-t:.1f}s]")
    # scan upward from M = 1 to find the failing set below the bound
    cap = min(below, scan_cap)
    fails = []
    if cap >= 1:
        for M in range(1, cap + 1):
            wrong, ties, margin, hd = check(p, S, M)
            if wrong or ties:
                fails.append((M, wrong, ties))
        ok = [M for M in range(1, cap + 1) if M not in {f[0] for f in fails}]
        print(f"  scan M=1..{cap}: failing M (wrong, ties) = {fails if fails else 'none'}; "
              f"smallest M with no wrong answer and no tie = {min(ok) if ok else 'none in range'}")

if __name__ == "__main__":
    p = int(sys.argv[1]); scan_cap = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = np.random.default_rng(p)
    full = list(range(1, (p-1)//2 + 1))
    cases = [(full, "all frequencies")]
    top = (p-1)//2
    if top >= 3:
        cases.append(([1, 2, 3], "adversarial, small gap {1,2,3}"))
    cases.append(([1], "adversarial, smallest gap {1}"))
    for d in (3, 5):
        if top >= d:
            Sr = sorted(rng.choice(np.arange(1, top + 1), size=d, replace=False).tolist())
            cases.append((Sr, f"random {d}"))
    if p == 113:
        cases.append(([14, 35, 41, 42, 52], "Nanda's five"))
    for Sx, label in cases:
        run_case(p, Sx, label, scan_cap)
