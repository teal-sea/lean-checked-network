"""How the network adds, measured, and turned into a cheap proof that it adds correctly.

The network (see train.py) scores each candidate answer c for the input pair (a, b) as

    N(a, b, c) = sum over neurons h of  W2[c, h] * (E1[a, h] + E2[b, h])^2

and answers with the c of highest score. Everything below is about the frozen integer
weights, the same object the Lean files are about.

Part 1 measures the mechanism: each neuron's three weight columns are close to waves on a
circle, cos(2 pi k x / p + phase), with one frequency k per neuron.

Part 2 turns that into a certificate, in exact integer arithmetic. The circle is a table of
Gaussian integers Z_k(x) ~ M * exp(2 pi i k x / p). Each weight column is written as an
exact circle wave plus an exact remainder. The angle-addition rule, applied to the circle
table with its rounding error tracked exactly, turns the network's score into
  * one wave in (a + b - c), which peaks exactly at the right answer,
  * other waves and tables that can only blur that peak by a bounded amount,
  * remainders with explicit bounds.
If the peak's margin beats the sum of the blurs for a pair (a, b), the network's answer for
that pair is provably (a + b) mod p. The certificate costs about p * p * H operations for all
pairs together, where checking every score directly costs p * p * p * H.

Part 3 checks the certificate against the real scores on random samples. It must never claim
more margin than the network really has.

Usage: python3 mechanism.py RUN.npz [--harmonics 1,3] [--diag]
"""
import sys
import numpy as np

run = np.load(sys.argv[1])
p, H = int(run["p"]), int(run["H"])
E1, E2, W2 = (run[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"])  # p x H; W2 row = answer c
O = object

# ---------------------------------------------------------------- Part 1: measure
F = [np.fft.fft(Mx, axis=0) for Mx in (E1, E2, W2)]
half = (p - 1) // 2
alive = [h for h in range(H) if any(np.any(Mx[:, h] != 0) for Mx in (E1, E2, W2))]
freq, share = {}, {}
for h in alive:
    tot, allp = np.zeros(half), 0.0
    for Fx in F:
        P = np.abs(Fx[:, h]) ** 2
        tot += P[1:half + 1] + P[p - 1:p - half - 1:-1]
        allp += P.sum()
    k = int(np.argmax(tot)) + 1
    freq[h] = k
    share[h] = tot[k - 1] / allp   # energy of the three columns at k, over their total energy
ks = sorted(set(freq.values()))
print(f"p={p}, H={H}: {len(alive)} live neurons using {len(ks)} distinct frequencies")
sh = np.array(list(share.values()))
print(f"share of each neuron's weight energy in its own frequency: median {np.median(sh):.3f}, min {sh.min():.3f}")

# ---------------------------------------------------------------- Part 2: certificate
HARM = (1, 3)
if "--harmonics" in sys.argv:
    HARM = tuple(int(x) for x in sys.argv[sys.argv.index("--harmonics") + 1].split(","))
M = 1 << 20        # radius of the integer circle
SIG = 1 << 30      # weights are scaled by SIG before being compared with circle waves
inv = lambda x: pow(x % p, -1, p)

def circle(k):
    t = 2 * np.pi * k * np.arange(p) / p
    re = np.array([int(round(M * np.cos(x))) for x in t], dtype=O)
    im = np.array([int(round(M * np.sin(x))) for x in t], dtype=O)
    return re, im
Z = {k: circle(k) for k in ks}
neg = (-np.arange(p)) % p
for k in ks:   # rounding is symmetric, so conj(Z(x)) = Z(-x) exactly; the argument uses this
    assert all(Z[k][0][neg] == Z[k][0]) and all(Z[k][1][neg] == -Z[k][1])
mul_idx = {m: (m * np.arange(p)) % p for m in range(-3 * max(HARM), 3 * max(HARM) + 1) if m % p}

def gmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])
def gconj(x):
    return (x[0], -x[1])
def gadd(x, y):
    return (x[0] + y[0], x[1] + y[1])
def l1(x):
    return abs(x[0]) + abs(x[1])

def wave(g, k, m=1):
    """Re(g * Z_k(m x)) for all x: a circle wave of frequency m*k."""
    i = mul_idx[m]
    return g[0] * Z[k][0][i] - g[1] * Z[k][1][i]

def fit(Fx, h, k, m):
    """Gaussian integer with Re(eps * Z_k(m x)) ~ SIG * (that column's component at frequency m*k)."""
    c = 2 * Fx[(m * k) % p, h] / p * SIG / M
    return (int(round(c.real)), int(round(c.imag)))

# each weight column = sum over harmonics m of a circle wave, plus an exact remainder
eps = {(h, m): fit(F[0], h, freq[h], m) for h in alive for m in HARM}
phi = {(h, m): fit(F[1], h, freq[h], m) for h in alive for m in HARM}
psi = {(h, m): fit(F[2], h, freq[h], m) for h in alive for m in HARM}
eh = {h: sum(wave(eps[h, m], freq[h], m) for m in HARM) for h in alive}
fh = {h: sum(wave(phi[h, m], freq[h], m) for m in HARM) for h in alive}
wh = {h: sum(wave(psi[h, m], freq[h], m) for m in HARM) for h in alive}
re_ = {h: SIG * E1[:, h].astype(O) - eh[h] for h in alive}
rf_ = {h: SIG * E2[:, h].astype(O) - fh[h] for h in alive}
rw_ = {h: SIG * W2[:, h].astype(O) - wh[h] for h in alive}
rms = lambda v: float(np.sqrt(np.mean([float(x) ** 2 for x in v])))
rr = [rms(r[h]) / rms(w[h]) for (r, w) in [(re_, eh), (rf_, fh), (rw_, wh)] for h in alive]
print(f"harmonics {HARM}: remainder size / wave size, median {np.median(rr):.3f}, worst {max(rr):.3f}")

# angle-addition defect on the integer circle: Z(x)Z(y) = M Z(x+y) + Def(x, y), all x, y
dmax = {}
for k in ks:
    zr, zi = Z[k]
    pr = np.multiply.outer(zr, zr) - np.multiply.outer(zi, zi)
    pi = np.multiply.outer(zr, zi) + np.multiply.outer(zi, zr)
    idx = np.add.outer(np.arange(p), np.arange(p)) % p
    dmax[k] = max(max(abs(v) for v in (pr - M * zr[idx]).ravel()), max(abs(v) for v in (pi - M * zi[idx]).ravel()))
tri = {k: M * dmax[k] + 2 * dmax[k] * M for k in ks}

SIGNS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def pick(g, sgn):
    return g if sgn > 0 else gconj(g)

# main term. 4 w^ e^ f^ = sum over harmonics (m1, m2, m3) and signs (s2, s3) of
#   Re[ e f w * Z(m1 a) Z(s2 m2 b) Z(s3 m3 c) ],  and Z(x)Z(y)Z(w) = M^2 Z(x+y+w) + defect.
# The form m1 a + s2 m2 b + s3 m3 c is rescaled so c has coefficient 1: u = A a + B b + c.
main = {}      # (A, B) -> {(k, gamma): G}
mdef = {}      # (k, m1, s2 m2, s3 m3) -> G   (same defect function, so G's add before bounding)
for h in alive:
    k = freq[h]
    for m1 in HARM:
        for m2 in HARM:
            for m3 in HARM:
                for s2, s3 in SIGNS:
                    G = gmul(gmul(eps[h, m1], pick(phi[h, m2], s2)), pick(psi[h, m3], s3))
                    gam = s3 * m3
                    key = (m1 * inv(gam) % p, s2 * m2 * inv(gam) % p)
                    d = main.setdefault(key, {})
                    d[k, gam] = gadd(d.get((k, gam), (0, 0)), G)
                    mdef[k, m1, s2 * m2, gam] = gadd(mdef.get((k, m1, s2 * m2, gam), (0, 0)), G)
Tmain = {key: sum(wave(G, k, gam) for (k, gam), G in d.items()) * (M * M) for key, d in main.items()}
DB = sum(l1(G) * tri[k] for (k, *_), G in mdef.items())
PEAK = ((-1) % p, (-1) % p)      # u = c - a - b: the wave that peaks at the right answer

# first-order remainders through the angle-addition rule (one remainder, two waves):
#   L1 = sum_h rw_h(c) e^_h(a) f^_h(b):  2 e^ f^ -> waves in m1 a + s m2 b = m1 (a + K b)
#   L2 = sum_h w^_h(c) re_h(a) f^_h(b):  2 w^ f^ -> waves in m3 c + s m2 b = m3 (c + K b)
#   L3 = sum_h w^_h(c) e^_h(a) rf_h(b):  2 w^ e^ -> waves in m3 c + s m1 a = m3 (c + K a)
def first_order(rem, g_first, g_second):
    """Tables keyed by K: T_K[i, x] = M * sum Re[(sum_h rem_h(i) * G_h) * Z_k(m x)], plus a defect bound."""
    acc = {}       # (K, k, m) -> (Yre, Yim) over i
    dsum = 0
    for h in alive:
        k = freq[h]
        R = max(abs(v) for v in rem[h])
        for m in HARM:
            for m_ in HARM:
                for sgn in (1, -1):
                    G = gmul(g_first[h, m], pick(g_second[h, m_], sgn))
                    K = sgn * m_ * inv(m) % p
                    yr, yi = acc.get((K, k, m), (np.zeros(p, dtype=O), np.zeros(p, dtype=O)))
                    acc[K, k, m] = (yr + rem[h] * G[0], yi + rem[h] * G[1])
                    dsum += R * l1(G) * dmax[k]
    tabs = {}
    for (K, k, m), (yr, yi) in acc.items():
        i = mul_idx[m]
        t = np.multiply.outer(yr, Z[k][0][i]) - np.multiply.outer(yi, Z[k][1][i])
        tabs[K] = tabs.get(K, 0) + t
    return {K: t * M for K, t in tabs.items()}, dsum
W1, d1 = first_order(rw_, eps, phi)    # W1[K][c, a + K b]
W2t, d2 = first_order(re_, psi, phi)   # W2t[K][a, c + K b]
W3, d3 = first_order(rf_, psi, eps)    # W3[K][b, c + K a]

# second-order remainders: Q2(a,b,c) = sum_h rw_h(c) g_h(a,b) + sum_h w^_h(c) q_h(a,b), with
#   g_h(a,b) = SIG^2 E1[a,h] E2[b,h] - e^_h(a) f^_h(b)   and   q_h(a,b) = re_h(a) rf_h(b)  (exact),
# bounded per (a, b) uniformly in c by Cauchy-Schwarz over the neurons:
#   |Q2| <= max_c |rw(c)| * |g(a,b)| + max_c |w^(c)| * |q(a,b)|     (|.| = Euclidean length)
from math import isqrt
def sqrt_up(n):
    r = isqrt(n)
    return r if r * r == n else r + 1
rw_len = sqrt_up(max(sum(int(rw_[h][c]) ** 2 for h in alive) for c in range(p)))
wh_len = sqrt_up(max(sum(int(wh[h][c]) ** 2 for h in alive) for c in range(p)))
g2 = np.zeros((p, p), dtype=O)
q2 = np.zeros((p, p), dtype=O)
for h in alive:
    g = SIG * SIG * np.multiply.outer(E1[:, h].astype(O), E2[:, h].astype(O)) - np.multiply.outer(eh[h], fh[h])
    q = np.multiply.outer(re_[h], rf_[h])
    g2 += g * g
    q2 += q * q
QB = np.array([[rw_len * sqrt_up(int(g2[a, b])) + wh_len * sqrt_up(int(q2[a, b])) for b in range(p)]
               for a in range(p)], dtype=O)

# exact tables for the parts of the score that ignore b or ignore a
U = W2.astype(O) @ (E1.astype(O) ** 2).T      # U[c, a]
V = W2.astype(O) @ (E2.astype(O) ** 2).T      # V[c, b]
S3 = SIG ** 3

def top2(vals):
    o = sorted(range(len(vals)), key=lambda n: vals[n], reverse=True)
    return o[0], o[1]
def drop(vals, i, t2):
    """vals[i] minus the largest other entry, given the indices of the top two."""
    return vals[i] - vals[t2[1] if t2[0] == i else t2[0]]

t2U = [top2(list(U[:, a])) for a in range(p)]
t2V = [top2(list(V[:, b])) for b in range(p)]
t2M = {key: top2(list(t)) for key, t in Tmain.items()}
t2W1 = {K: [top2(list(t[:, x])) for x in range(p)] for K, t in W1.items()}
t2W2 = {K: [top2(list(t[a, :])) for a in range(p)] for K, t in W2t.items()}
t2W3 = {K: [top2(list(t[b, :])) for b in range(p)] for K, t in W3.items()}
ERR = 2 * 2 * DB + 4 * 2 * (d1 + d2 + d3)

def lower_bound(a, b, parts=False):
    """Certified lower bound on 4 SIG^3 (N(a,b,s) - max_{c != s} N(a,b,c)), s = (a+b) mod p."""
    s = (a + b) % p
    terms = {"U(a,c)": 4 * S3 * drop(U[:, a], s, t2U[a]),
             "V(b,c)": 4 * S3 * drop(V[:, b], s, t2V[b])}
    peak, other = 0, 0
    for (A, B), t in Tmain.items():
        u = (A * a + B * b + s) % p
        v = 2 * drop(t, u, t2M[A, B])
        if (A, B) == PEAK: peak += v
        else: other += v
    terms["peak wave"] = peak
    terms["other waves"] = other
    terms["W2 remainder"] = sum(4 * drop(t[:, (a + K * b) % p], s, t2W1[K][(a + K * b) % p]) for K, t in W1.items())
    terms["E1 remainder"] = sum(4 * drop(t[a, :], (s + K * b) % p, t2W2[K][a]) for K, t in W2t.items())
    terms["E2 remainder"] = sum(4 * drop(t[b, :], (s + K * a) % p, t2W3[K][b]) for K, t in W3.items())
    terms["rounding"] = -ERR
    terms["2nd order"] = -8 * 2 * QB[a, b]
    lb = sum(terms.values())
    return (lb, terms) if parts else lb

LB = np.array([[lower_bound(a, b) for b in range(p)] for a in range(p)], dtype=O)
ref = 2 * drop(Tmain[PEAK], 0, t2M[PEAK])
cert = int(sum(1 for v in LB.ravel() if v > 0))
print(f"certified by the circle argument: {cert} of {p * p} input pairs")
ratio = np.array([float(v) / float(ref) for v in LB.ravel()])
print(f"certified gap / peak-wave margin: min {ratio.min():.3f}, median {np.median(ratio):.3f}")

if "--diag" in sys.argv:
    rows = [lower_bound(a, b, True)[1] for a in range(0, p, 7) for b in range(0, p, 7)]
    for name in rows[0]:
        v = np.array([float(r[name]) / float(ref) for r in rows])
        print(f"  {name:13s} median {np.median(v):+.4f}  worst {v.min():+.4f}")

# ---------------------------------------------------------------- Part 3: soundness checks
rng = np.random.default_rng(1)
def scores(a, b):
    z = E1[a].astype(O) + E2[b].astype(O)
    return [int(v) for v in W2.astype(O) @ (z * z)]
ok = True
# (i) the exact decomposition reproduces the real score up to the stated error bounds
worst = 0.0
for _ in range(300):
    a, b, c = (int(x) for x in rng.integers(0, p, 3))
    real = 4 * S3 * scores(a, b)[c]
    model = (4 * S3 * U[c, a] + 4 * S3 * V[c, b]
             + 2 * sum(t[(A * a + B * b + c) % p] for (A, B), t in Tmain.items())
             + 4 * sum(t[c, (a + K * b) % p] for K, t in W1.items())
             + 4 * sum(t[a, (c + K * b) % p] for K, t in W2t.items())
             + 4 * sum(t[b, (c + K * a) % p] for K, t in W3.items()))
    allowed = 2 * DB + 4 * (d1 + d2 + d3) + 8 * QB[a, b]
    worst = max(worst, abs(real - model) / allowed)
print(f"(i) |real score - decomposition| / allowed error, worst of 300 samples: {worst:.3f} ({'ok' if worst <= 1 else 'FAIL'})")
ok &= worst <= 1
# (ii) the certified bound never exceeds the true gap
bad = 0
for _ in range(200):
    a, b = (int(x) for x in rng.integers(0, p, 2))
    s = (a + b) % p
    sc = scores(a, b)
    gap = sc[s] - max(v for n, v in enumerate(sc) if n != s)
    bad += LB[a, b] > 4 * S3 * gap
print(f"(ii) certified bound above the true gap in {bad} of 200 samples ({'ok' if bad == 0 else 'FAIL'})")
ok &= bad == 0
sys.exit(0 if ok else 1)
