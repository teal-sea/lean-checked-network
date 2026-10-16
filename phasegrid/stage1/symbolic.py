"""Claim C as a symbolic identity: with ca = cos ta, sa = sin ta, cb, sb, cc, sc as six independent
variables, the grid sum over phi1 in {0, pi/2, pi, 3pi/2}, phi2 in {0, pi/2} of
   cos(tc + phi1 + phi2) (cos(ta + phi1) + cos(tb + phi2))^2
equals 4 (cc (ca cb - sa sb) + sc (ca sb + sa cb)) as POLYNOMIALS (every coefficient compared), using
only cos(x + j pi/2) in {cos x, -sin x, -cos x, sin x}. No sin^2 + cos^2 = 1 is used, no sampling.
Polynomials are dicts {monomial exponent tuple: Fraction}; this is exact arithmetic."""
from fractions import Fraction as F
from itertools import product
VARS = ["ca", "sa", "cb", "sb", "cc", "sc"]
def var(i):
    e = [0]*6; e[i] = 1; return {tuple(e): F(1)}
def add(p, q):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, F(0)) + c
    return {m: c for m, c in r.items() if c != 0}
def neg(p): return {m: -c for m, c in p.items()}
def mul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2)); r[m] = r.get(m, F(0)) + c1*c2
    return {m: c for m, c in r.items() if c != 0}
def scal(k, p): return {m: k*c for m, c in p.items()}
ca, sa, cb, sb, cc, sc = (var(i) for i in range(6))
def rot(c, s, j):   # cos(x + j pi/2) as a polynomial in (c, s) = (cos x, sin x)
    return [c, neg(s), neg(c), s][j % 4]
total = {}
for j, l in product(range(4), range(2)):
    e = add(rot(ca, sa, j), rot(cb, sb, l))
    total = add(total, mul(rot(cc, sc, j + l), mul(e, e)))
want = scal(F(4), add(mul(cc, add(mul(ca, cb), neg(mul(sa, sb)))), mul(sc, add(mul(ca, sb), mul(sa, cb)))))
diff = add(total, neg(want))
print("grid sum as a polynomial:", {"".join(f"{v}^{e}" if e > 1 else v for v, e in zip(VARS, m) if e): str(c) for m, c in sorted(total.items())})
print("target 4(cc(ca cb - sa sb) + sc(ca sb + sa cb)):", {"".join(f"{v}^{e}" if e > 1 else v for v, e in zip(VARS, m) if e): str(c) for m, c in sorted(want.items())})
print("difference as a polynomial:", diff, "-> identity holds exactly:", diff == {})
# control: a wrong grid (phi2 over {0, pi}) must not cancel
bad = {}
for j, l in product(range(4), range(2)):
    e = add(rot(ca, sa, j), rot(cb, sb, 2*l))
    bad = add(bad, mul(rot(cc, sc, j + 2*l), mul(e, e)))
print("control, phi2 in {0, pi}: difference has", len(add(bad, neg(want))), "nonzero coefficients (must be > 0)")
