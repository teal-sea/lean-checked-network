"""Transformer reduction search, second family (rules fixed 2026-11-01 before running it on any
checkpoint). Question: at a checkpoint where the trained transformer is still wrong on many pairs
(before or during grokking), is some reduction of it to its key Fourier frequencies an exact adder
on all 12,769 pairs? Held-out pairs are included, so exactness cannot come from memorized labels.

Per checkpoint, with k(n) and K_r from reduce.py (neuron frequencies ranked by neuron count):
  M_m      (a weight set) mean-ablate every MLP neuron whose k(n) is not in the top m of K_r: its
           Wout row is set to 0 and its mean output over all pairs (mean activation times its Wout
           row) is added to bout.
  MA_m     (a weight set) M_m, then A_m of reduce.py (token embeddings and unembedding projected
           onto the constant plus the top-m waves).
  T        (a table model) attention replaced by its mean over all pairs, per head and position,
           so the MLP input is additive in a and b, as in the x^2 MLP; nothing else changes.
  TC_m     (a table model) T with M_m's neuron ablation (at the mean under mean attention), then
           each kept neuron's 8 input tables projected onto the constant plus its own wave and its
           readout row onto its own wave (head-to-logit tables unchanged), plus C's baseline bias.
  m in M_LIST. Controls: M_m and MA_m with m random frequencies (3 draws, seeded by m).

Win rule, fixed before results: a checkpoint where the trained net is wrong on at least 1,000
pairs and some reduction above is wrong on 0 pairs, while its random-frequency control at the
same m is wrong on more than half the pairs. A weight-set win (M_m, MA_m) can be sealed with the
existing transformer theorem shape; a table-model win needs the table route (Compose.lean).

Usage: python3 reduce2.py CKPT.npz [...]   (one JSON line per checkpoint; run on a box)"""
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reduce import (AA, BB, H, KEYS, NM, P, Y, attention, basis, fwd, neuron_freqs,  # noqa: E402
                    rand_K, reduce_A, score)

M_LIST = [3, 4, 5, 6, 8]


def mean_ablate(W, keep):
    """Wout rows of neurons outside `keep` set to 0, their mean output folded into bout."""
    _, act = fwd(W, want_act=True)
    drop = ~keep
    W1 = dict(W)
    Wout = W["Wout"].copy()
    W1["bout"] = W["bout"] + act[:, drop].mean(0) @ W["Wout"][drop]
    Wout[drop] = 0
    W1["Wout"] = Wout
    return W1


def tables(W):
    att, x2 = attention(W)
    E = W["tok"][:P]
    TI = [[(E + W["pos"][j]) @ W["WV"][h] @ W["WO"][h] @ W["Win"] for j in range(2)] for h in range(H)]
    TU = [[(E + W["pos"][j]) @ W["WV"][h] @ W["WO"][h] @ W["U"] for j in range(2)] for h in range(H)]
    TI2 = [x2 @ W["WV"][h] @ W["WO"][h] @ W["Win"] for h in range(H)]
    TU2 = [x2 @ W["WV"][h] @ W["WO"][h] @ W["U"] for h in range(H)]
    CI = x2 @ W["Win"] + W["bin"]; CU = x2 @ W["U"] + W["bout"] @ W["U"]
    return att, TI, TU, TI2, TU2, CI, CU, W["Wout"] @ W["U"]


def run_tables(att, TI, TU, TI2, TU2, CI, CU, G):
    pre = CI + sum(att[:, h, 0, None] * TI[h][0][AA] + att[:, h, 1, None] * TI[h][1][BB]
                   + att[:, h, 2, None] * TI2[h] for h in range(H))
    act = np.maximum(pre, 0)
    L = CU + sum(att[:, h, 0, None] * TU[h][0][AA] + att[:, h, 1, None] * TU[h][1][BB]
                 + att[:, h, 2, None] * TU2[h] for h in range(H)) + act @ G
    return L, act


def reduce_T(W, keep=None, kn=None):
    att, TI, TU, TI2, TU2, CI, CU, G = tables(W)
    attm = np.broadcast_to(att.mean(0), att.shape)
    L0, act0 = run_tables(attm, TI, TU, TI2, TU2, CI, CU, G)
    if keep is None:
        return score(L0)
    # ablate neurons outside keep at their mean (under mean attention), then one wave per kept neuron
    G1 = G.copy(); CU1 = CU + act0[:, ~keep].mean(0) @ G[~keep]; G1[~keep] = 0
    TIp = [[TI[h][j].copy() for j in range(2)] for h in range(H)]
    Gp = np.zeros_like(G1)
    for n in np.nonzero(keep)[0]:
        Bk = basis([kn[n]])
        for h in range(H):
            for j in range(2):
                TIp[h][j][:, n] = Bk @ (Bk.T @ TI[h][j][:, n])
        b = basis([kn[n]], dc=False); Gp[n] = (G1[n] @ b) @ b.T
    L1, act1 = run_tables(attm, TIp, TU, TI2, TU2, CI, CU1, Gp)
    beta = act1.mean(0) @ (G1 - Gp)
    L2, _ = run_tables(attm, TIp, TU, TI2, TU2, CI, CU1 + beta, Gp)
    return score(L1), score(L2)


def analyse(path):
    t0 = time.time()
    z = np.load(path)
    W = {k: np.asarray(z[k], dtype=np.float64) for k in KEYS}
    res = {"file": os.path.basename(path), "epoch": int(z["epoch"]) if "epoch" in z.files else None, "net": score(fwd(W))}
    kn, Kr, cnt, _ = neuron_freqs(W)
    res["K_r"] = Kr[:8]
    res["T"] = reduce_T(W)
    res["M"], res["MA"], res["TC"], res["M_rand"], res["MA_rand"] = {}, {}, {}, {}, {}
    for m in M_LIST:
        keep = np.isin(kn, Kr[:m])
        Wm = mean_ablate(W, keep)
        res["M"][m] = score(fwd(Wm)) + [int(keep.sum())]
        res["MA"][m] = score(fwd(reduce_A(Wm, Kr[:m])[0]))
        clock, biased = reduce_T(W, keep, kn)
        res["TC"][m] = {"clock": clock, "bias": biased}
        rM, rMA = [], []
        for d in range(3):
            Kx = rand_K(m, d); kx = np.isin(kn, Kx)
            Wx = mean_ablate(W, kx)
            rM.append(score(fwd(Wx))[0]); rMA.append(score(fwd(reduce_A(Wx, Kx)[0]))[0])
        res["M_rand"][m] = rM; res["MA_rand"][m] = rMA
    res["secs"] = round(time.time() - t0, 1)
    return res


if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(json.dumps(analyse(p)), flush=True)
