"""Find a planted fault: one entry of the unembedding U changed so that the pair with the smallest
margin, (96, 73), gets a wrong answer in the integer program. Prints the change and which pairs flip.

Usage: python3 transformer/find_fault.py transformer/runs/best.npz
"""
import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import int_transformer as it  # noqa: E402

W = it.load_weights(sys.argv[1])
q, f, n, m, R = 8, 32, 16, 5, 24
t = 4 * q
params = it.expfix_params(t, f, n, m, R)
ef = lambda x: it.expfix(x, t, f, n, m, R, params)
a, b = 96, 73
right = (a + b) % it.P
Wq = it.quantise(W, q)
T = it.build_tables(Wq)
L, D = it.int_logits_tables(Wq, T, a, b, ef)
order = sorted(range(it.P), key=lambda c: -int(L[c]))
print(f"pair ({a},{b}): right {right}, argmax {it.argmax_first(L)}, runner-up {order[1]}, margin {it.margin_of(L, right)}")
# fin = S^2 r + o (the final residual, 128 entries) is not returned; use the sign of U's effect:
# changing U[k][right] by d changes L[right] by d * fin_k. Find k with the largest |fin_k| by probing.
probe = []
for k in range(it.D_MODEL):
    Wk = {kk: (v.copy() if isinstance(v, np.ndarray) else v) for kk, v in Wq.items()}
    Wk["U"] = Wq["U"].copy(); Wk["U"][k][right] = Wk["U"][k][right] + 1
    Tk = it.build_tables(Wk)
    Lk, _ = it.int_logits_tables(Wk, Tk, a, b, ef)
    probe.append(int(Lk[right] - L[right]))
k = max(range(it.D_MODEL), key=lambda i: abs(probe[i]))
fin_k = probe[k]
print(f"largest |fin_k| at k = {k}: fin_k = {fin_k}")
need = int(L[right] - L[order[1]])
delta = -(need // abs(fin_k) + 1) * (1 if fin_k > 0 else -1)
# round up to a power of two in magnitude for a clean statement
mag = 1 << (abs(delta)).bit_length()
delta = mag if delta > 0 else -mag
Wk = dict(Wq); Wk["U"] = Wq["U"].copy(); Wk["U"][k][right] = Wk["U"][k][right] + delta
Tk = it.build_tables(Wk)
Lk, _ = it.int_logits_tables(Wk, Tk, a, b, ef)
print(f"U[{k}][{right}]: {int(Wq['U'][k][right])} -> {int(Wk['U'][k][right])} (delta {delta}); pair ({a},{b}) now answers {it.argmax_first(Lk)}, margin {it.margin_of(Lk, right)}")
# all pairs
wrong = []
for aa in range(it.P):
    for bb in range(it.P):
        Lp, _ = it.int_logits_tables(Wk, Tk, aa, bb, ef)
        if it.argmax_first(Lp) != (aa + bb) % it.P:
            wrong.append((aa, bb))
print(f"pairs wrong with the fault: {len(wrong)}; rows affected: {sorted(set(x for x, _ in wrong))}")
print(f"first ten: {wrong[:10]}")
