"""Stage 1 for the six-phase cycle: exact cancellation, coefficient 3, the bound 24|S| < M g, smallest M.
Usage: python3 -I cycle_check.py    (numpy only; exact int64 scores for the integer networks)
"""
import sys, numpy as np
rng = np.random.default_rng(20261016)
UV = [(1,-1), (3,1), (-1,1), (1,3), (2,2), (0,-2), (2,0), (1,1)]
print("== families: u+4v for the eight unwanted (u, v), and the cycle sum of cos(theta + (u+4v) 2 pi j/6)")
for (u, v) in UV:
    m = u + 4*v
    thetas = rng.uniform(-10, 10, 20000)
    s = sum(np.cos(thetas + m*2*np.pi*j/6) for j in range(6))
    print(f"  (u,v)=({u:2d},{v:2d}) m={m:3d} m%6={m%6} max|cycle sum|={np.abs(s).max():.2e}")
# a multiple of 6 does NOT cancel (the sanity check that the test can fail)
thetas = rng.uniform(-10, 10, 20000)
print(f"  control m=6: max|cycle sum|={np.abs(sum(np.cos(thetas + 6*2*np.pi*j/6) for j in range(6))).max():.2e} (6 cos theta, should not vanish)")

print("== one sextet: sum_j cos(tc+5phi_j)(cos(ta+phi_j)+cos(tb+4phi_j))^2 - 3 cos(ta+tb-tc) at 20000 random angle triples")
ta, tb, tc = (rng.uniform(-10, 10, 20000) for _ in range(3))
tot = np.zeros(20000)
for j in range(6):
    f1 = 2*np.pi*j/6; f2 = 4*f1
    tot += np.cos(tc + f1 + f2) * (np.cos(ta + f1) + np.cos(tb + f2))**2
print(f"  max|sextet - 3 cos(ta+tb-tc)| = {np.abs(tot - 3*np.cos(ta+tb-tc)).max():.2e}")
print(f"  fitted coefficient (least squares of sextet on cos(ta+tb-tc)): {np.dot(tot, np.cos(ta+tb-tc))/np.dot(np.cos(ta+tb-tc), np.cos(ta+tb-tc)):.12f}")

def tables(p, S):
    x = np.arange(p); E1, E2, W2 = [], [], []
    for k in S:
        for j in range(6):
            f1 = 2*np.pi*j/6; f2 = 4*f1
            E1.append(np.cos(2*np.pi*k*x/p + f1)); E2.append(np.cos(2*np.pi*k*x/p + f2)); W2.append(np.cos(2*np.pi*k*x/p + f1 + f2))
    return (np.array(t).T for t in (E1, E2, W2))

def gap(p, S):
    s = np.arange(1, p)
    w = sum(np.cos(2*np.pi*k*s/p) for k in S)
    return len(S) - w.max()

def check_int(p, S, M, E1, E2, W2):
    a, b = np.divmod(np.arange(p*p), p)
    E1q, E2q, W2q = (np.round(M*t).astype(np.int64) for t in (E1, E2, W2))
    z = E1q[a] + E2q[b]; Sc = (z*z) @ W2q.T
    ans = Sc.argmax(1); target = (a + b) % p
    top2 = np.sort(Sc, 1)[:, -2:]
    wrong = int((ans != target).sum()); ties = int((top2[:,0] == top2[:,1]).sum())
    # margin: right score minus the best wrong score (negative when wrong)
    right = Sc[np.arange(p*p), target]; Sc2 = Sc.copy(); Sc2[np.arange(p*p), target] = np.iinfo(np.int64).min
    margin = int((right - Sc2.max(1)).min())
    return wrong, ties, margin, int(max(abs(E1q).max(), abs(E2q).max(), abs(W2q).max()))

cases = [(7, "all"), (12, "all"), (113, "all"), (113, [39, 45]), (113, [14, 35, 41, 42, 52]), (257, "all"), (257, [114, 125])]
print("== per modulus: exact cancellation on the real network, gap, bound B = 24|S|/g, integer checks")
print("p | S | |S| | neurons | max|realscore - 3 wave| | g(S) | B=24|S|/g | M=ceil(B) (wrong,ties,margin) | M=ceil(B)-1 (wrong,ties,margin) | smallest M with 0 wrong 0 ties (scan 1..40) | M=127 (wrong,ties,margin,max|w|)")
for p, spec in cases:
    S = list(range(1, (p-1)//2 + 1)) if spec == "all" else spec
    E1, E2, W2 = tables(p, S)
    a, b = np.divmod(np.arange(p*p), p); q = np.arange(p)
    Sr = ((E1[a] + E2[b])**2) @ W2.T
    pred = 3*sum(np.cos(2*np.pi*k*(a[:, None] + b[:, None] - q[None, :])/p) for k in S)
    dev = np.abs(Sr - pred).max()
    g = gap(p, S); B = 24*len(S)/g
    Mup = int(np.ceil(B)) if abs(B - round(B)) > 1e-9 else int(round(B)) + 1   # smallest integer M with 24|S| < M g
    up = check_int(p, S, Mup, E1, E2, W2); dn = check_int(p, S, Mup-1, E1, E2, W2)
    smallest = None
    for M in range(1, 41):
        w, t, mg, _ = check_int(p, S, M, E1, E2, W2)
        if w == 0 and t == 0: smallest = M; break
    r127 = check_int(p, S, 127, E1, E2, W2)
    Sname = "all" if spec == "all" else str(S)
    print(f"{p} | {Sname} | {len(S)} | {6*len(S)} | {dev:.2e} | {g:.6g} | {B:.6g} | M={Mup}: {up[:3]} | M={Mup-1}: {dn[:3]} | {smallest} | {r127}")
print("note: M=ceil(B) is the smallest integer with 24|S| < M g; 'smallest M' is the first M in 1..40 with no wrong answer and no tie (None: none in 1..40).")
