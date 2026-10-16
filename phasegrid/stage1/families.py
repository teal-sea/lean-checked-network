"""Stage 1a. The wave families of one Gromov neuron and their cancellation over the phase grid.

One neuron at frequency k with phases (phi1, phi2):
  E1[a] = cos(ta + phi1), E2[b] = cos(tb + phi2), W2[c] = cos(tc + phi1 + phi2),
  ta = 2 pi k a / p, etc.  Its score term is W2[c] (E1[a] + E2[b])^2.

Claim A (nine terms): W (E1 + E2)^2 equals the sum of the nine cosines listed in FAMILIES below,
one of which (the (0,0) family, coefficient 1/2) is cos(ta + tb - tc) and the other eight carry
a phase combination alpha*phi1 + beta*phi2 with (alpha, beta) != (0, 0).
Claim B (grid cancellation): summed over phi1 in {0, pi/2, pi, 3pi/2} and phi2 in {0, pi/2},
each of the eight unwanted families sums to 0 identically in (ta, tb, tc), and the wanted one
sums to 4 cos(ta + tb - tc).
Claim C (polynomial form): with ca = cos ta, sa = sin ta, ..., the grid sum equals
  4 (cc (ca cb - sa sb) + sc (ca sb + sa cb)), a polynomial identity that needs no sin^2 + cos^2 = 1.
Checked at random real angles (Claims A, B) and at random rationals (Claim C, exact).
"""
import numpy as np
from fractions import Fraction
import random

# (coefficient, [coeff of ta, tb, tc], alpha, beta): term = coefficient * cos(x.ta + y.tb + z.tc + alpha phi1 + beta phi2)
FAMILIES = [
    (0.5,  (1, 1, -1), 0,  0),   # the wanted wave, a + b - c
    (1.0,  (0, 0,  1), 1,  1),   # W times the constant 1 from the squares
    (0.25, (2, 0,  1), 3,  1),
    (0.25, (2, 0, -1), 1, -1),
    (0.25, (0, 2,  1), 1,  3),
    (0.25, (0, 2, -1), -1, 1),
    (0.5,  (1, 1,  1), 2,  2),
    (0.5,  (1, -1, 1), 2,  0),
    (0.5,  (1, -1, -1), 0, -2),
]

def neuron(ta, tb, tc, f1, f2):
    return np.cos(tc + f1 + f2) * (np.cos(ta + f1) + np.cos(tb + f2)) ** 2

def families(ta, tb, tc, f1, f2):
    return sum(co * np.cos(x*ta + y*tb + z*tc + al*f1 + be*f2) for co, (x, y, z), al, be in FAMILIES)

rng = np.random.default_rng(1)
N = 20000
ta, tb, tc, f1, f2 = (rng.uniform(-10, 10, N) for _ in range(5))
devA = np.abs(neuron(ta, tb, tc, f1, f2) - families(ta, tb, tc, f1, f2)).max()
print(f"Claim A (nine-term expansion), {N} random angle 5-tuples: max deviation {devA:.2e}")

GRID = [(j*np.pi/2, l*np.pi/2) for j in range(4) for l in range(2)]
print("Claim B (grid sums of each family), %d random angle triples:" % N)
for co, (x, y, z), al, be in FAMILIES:
    tot = sum(co * np.cos(x*ta + y*tb + z*tc + al*g1 + be*g2) for g1, g2 in GRID)
    if (al, be) == (0, 0):
        dev = np.abs(tot - 4*np.cos(ta + tb - tc)).max()
        print(f"  family (alpha,beta)=({al},{be}) wave {x,y,z}: grid sum - 4cos(ta+tb-tc), max |dev| = {dev:.2e}  (wanted)")
    else:
        dev = np.abs(tot).max()
        print(f"  family (alpha,beta)=({al},{be}) wave {x,y,z}: grid sum, max |.| = {dev:.2e}")
total = sum(neuron(ta, tb, tc, g1, g2) for g1, g2 in GRID)
print(f"  whole neuron octet: max |sum - 4 cos(ta+tb-tc)| = {np.abs(total - 4*np.cos(ta+tb-tc)).max():.2e}")

# Claim C, exact over rationals: the eight shifted cosines are +-ca, +-sa, etc.
def grid_poly(ca, sa, cb, sb, cc, sc):
    A = [ca, -sa, -ca, sa]            # cos(ta + j pi/2), j = 0..3
    B = [cb, -sb]                      # cos(tb + l pi/2), l = 0..1
    C = [cc, -sc, -cc, sc, cc]         # cos(tc + m pi/2), m = 0..4
    return sum(C[j + l] * (A[j] + B[l]) ** 2 for j in range(4) for l in range(2))
random.seed(2)
worst = 0
for _ in range(2000):
    v = [Fraction(random.randint(-10**6, 10**6), random.randint(1, 10**6)) for _ in range(6)]
    lhs = grid_poly(*v)
    ca, sa, cb, sb, cc, sc = v
    rhs = 4 * (cc * (ca*cb - sa*sb) + sc * (ca*sb + sa*cb))
    worst = max(worst, abs(lhs - rhs))
print(f"Claim C (polynomial identity), 2000 random rational points, exact arithmetic: max |lhs - rhs| = {worst}")
print("Counting: 9 cosine terms per neuron, 1 wanted + 8 unwanted (the proposal says 'eight families ... the other seven').")
