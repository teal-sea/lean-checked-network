"""Exact rational interval bounds for cos and sin at 2 pi r / 7, r = 1, 2, 3, built the way the Lean
file P7Link.lean will build them: y = pi/28 with pi in (3.141592, 3.141593); Real.cos_bound and
Real.sin_bound at y (degree-4 Taylor, |x| <= 1); then three angle doublings
cos 2y = 1 - 2 sin^2 y, sin 2y = 2 sin y cos y, and the step 4 pi/7 from 2 pi/7 the same way.
Prints the rational bounds and checks every P7Full table entry is within 1/2 of 25 * the bound box."""
from fractions import Fraction as F
import numpy as np
PI_LO, PI_HI = F(3141592, 10**6), F(3141593, 10**6)
def interval_mul(a, b):
    lo1, hi1 = a; lo2, hi2 = b
    c = [lo1*lo2, lo1*hi2, hi1*lo2, hi1*hi2]
    return (min(c), max(c))
def sq(a):   # a = (lo, hi) with 0 <= lo
    assert a[0] >= 0
    return (a[0]**2, a[1]**2)
def rnd(x, digits=12):   # round outward to a fixed decimal grid so the Lean file stays readable
    q = 10**digits
    return x
y = (PI_LO/28, PI_HI/28)            # 0.11219971 .. 0.11219975
assert y[1] <= 1
# cos_bound: |cos y - (1 - y^2/2)| <= |y|^4 * 5/96 ; sin_bound: |sin y - (y - y^3/6)| <= |y|^5/100
y2 = sq(y); y3 = interval_mul(y2, y); y4 = sq(y2); y5 = interval_mul(y4, y)
ec = y4[1]*F(5,96); es = y5[1]/100
cos_y = (1 - y2[1]/2 - ec, 1 - y2[0]/2 + ec)
sin_y = (y[0] - y3[1]/6 - es, y[1] - y3[0]/6 + es)
def double(c, s):
    # cos 2t = 1 - 2 s^2 ; sin 2t = 2 s c  (s, c >= 0)
    s2 = sq(s); sc = interval_mul(s, c)
    return (1 - 2*s2[1], 1 - 2*s2[0]), (2*sc[0], 2*sc[1])
c, s = cos_y, sin_y                 # pi/28
steps = {"pi/28": (c, s)}
for name in ("pi/14", "pi/7", "2pi/7"):
    c, s = double(c, s); steps[name] = (c, s)
c4, s4 = double(*steps["2pi/7"]); steps["4pi/7"] = (c4, s4)     # cos 4pi/7 = 1 - 2 sin^2(2pi/7) (negative), sin = 2 s c
c1, s1 = steps["2pi/7"]; c2, s2 = steps["4pi/7"]; c3, s3 = ((-steps["pi/7"][0][1], -steps["pi/7"][0][0]), steps["pi/7"][1])  # 6pi/7 = pi - pi/7
bounds = {1: (c1, s1), 2: (c2, s2), 3: (c3, s3)}
for r, (cc, ss) in bounds.items():
    tc, ts = np.cos(2*np.pi*r/7), np.sin(2*np.pi*r/7)
    print(f"r={r}: cos in [{float(cc[0]):.9f}, {float(cc[1]):.9f}] width {float(cc[1]-cc[0]):.2e} (true {tc:.9f} inside: {cc[0] <= F(tc) <= cc[1]});"
          f" sin in [{float(ss[0]):.9f}, {float(ss[1]):.9f}] width {float(ss[1]-ss[0]):.2e} (true {ts:.9f} inside: {ss[0] <= F(ts) <= ss[1]})")
for name, (cc, ss) in steps.items():
    print(f"  {name}: cos [{float(cc[0]):.10f},{float(cc[1]):.10f}] sin [{float(ss[0]):.10f},{float(ss[1]):.10f}]")
# check every table entry of P7Full: value = 25 * (+-cos or +-sin of 2 pi r/7), r = k x mod 7, quarter turns j
M = 25; p = 7; S = [1, 2, 3]
def quarter(j, cb, sb):
    j %= 4
    neg = lambda a: (-a[1], -a[0])
    return [cb, neg(sb), neg(cb), sb][j]
def val(r, j):
    r %= 7
    if r == 0: cb, sb = (F(1), F(1)), (F(0), F(0))
    elif r <= 3: cb, sb = bounds[r]
    else: cb, sb = bounds[7 - r][0], (-bounds[7 - r][1][1], -bounds[7 - r][1][0])
    return quarter(j, cb, sb)
worst = F(0); n = 0
for k in S:
    for j in range(4):
        for l in range(2):
            for x in range(p):
                for ph in (j, l, j + l):
                    lo, hi = val(k*x, ph)
                    t = int(np.floor(M*np.cos(2*np.pi*k*x/p + ph*np.pi/2) + 0.5))
                    d = max(abs(t - M*lo), abs(t - M*hi))
                    worst = max(worst, d); n += 1
                    assert d <= F(1, 2), (k, j, l, x, ph, t, float(lo), float(hi))
print(f"{n} table entries checked against the rational boxes: worst |t - 25 v| over the box = {float(worst):.6f} <= 1/2")
# print the bounds as exact rationals for the Lean file (as decimal strings with enough digits, rounded outward)
def outward(x, lo):
    d = 10**10
    import math
    return F(math.floor(x*d), d) if lo else F(math.ceil(x*d), d)
print("Lean constants (outward-rounded to 1e-10):")
for name, (cc, ss) in steps.items():
    print(f"  {name}: cos [{outward(cc[0],True)}, {outward(cc[1],False)}]  sin [{outward(ss[0],True)}, {outward(ss[1],False)}]")
print("  y = pi/28 in [", PI_LO/28, ",", PI_HI/28, "]")
