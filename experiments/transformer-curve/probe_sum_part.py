"""Post-hoc check after reduce.py's kill rule fired (2026-11-01): is there an adder anywhere in a
memorizing transformer's logit table, whatever the frequencies?

For each checkpoint: R(s, c) = mean over the 113 pairs with a + b = s (mod 113) of the logit
L(a, b, c), the part of the logit table that depends on (a, b) only through a + b (it equals
Nanda et al.'s restricted logits with every frequency kept). Reported: the number of sums s whose
argmax_c R(s, c) is not s (an adder has 0), the smallest gap R(s, s) - max_{c != s} R(s, c), the
share of the logit table's variance R carries, and Nanda-restricted wrong pairs with the top m
frequencies ranked by their energy in R itself (the most favourable choice) for m in M_LIST.

Usage: python3 probe_sum_part.py CKPT.npz [...]   (one JSON line each; seconds per checkpoint)"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reduce import KEYS, P, T, Y, fwd  # noqa: E402

M_LIST = [1, 2, 4, 8, 16, 32, 56]
S = (T[:, None] + T[None, :]) % P


def probe(path):
    z = np.load(path)
    W = {k: np.asarray(z[k], dtype=np.float64) for k in KEYS}
    L = fwd(W).reshape(P, P, P)
    R = np.stack([L[T, (s - T) % P].mean(0) for s in range(P)])          # (s, c)
    gap = R[T, T] - np.where(np.eye(P, dtype=bool), -np.inf, R).max(1)
    Lc = L - L.mean((0, 1), keepdims=True); Rc = R - R.mean(0, keepdims=True)
    share = float((Rc ** 2).sum() * P / (Lc ** 2).sum())
    F = np.fft.rfft(Rc, axis=0)                                            # along s
    energy = (np.abs(F[1:57]) ** 2).sum(1)
    rank = list(np.argsort(-energy) + 1)
    # the same average restricted to held-out pairs, and to training pairs: memorizing the training
    # pairs (whose label is their sum) pushes the all-pairs average toward an adder by itself
    tr = np.zeros(P * P, bool); tr[np.asarray(z["train_idx"])] = True; tr = tr.reshape(P, P)
    split = {}
    for name, mask in (("heldout", ~tr), ("train", tr)):
        Rx = np.full((P, P), np.nan); n_min = P
        for s in range(P):
            a = T[mask[T, (s - T) % P]]
            n_min = min(n_min, len(a))
            if len(a): Rx[s] = L[a, (s - a) % P].mean(0)
        ok = ~np.isnan(Rx[:, 0])
        gx = Rx[T, T] - np.where(np.eye(P, dtype=bool), -np.inf, Rx).max(1)
        split[name] = {"wrong_sums": int((Rx[ok].argmax(1) != T[ok]).sum()), "sums_with_pairs": int(ok.sum()),
                       "min_pairs_per_sum": int(n_min), "min_gap": round(float(np.nanmin(gx)), 5)}
    out = {"file": os.path.basename(path), "epoch": int(z["epoch"]), "net_wrong": int((L.reshape(-1, P).argmax(1) != Y).sum()),
           "split": split,
           "sum_part_wrong_sums": int((R.argmax(1) != T).sum()), "sum_part_min_gap": round(float(gap.min()), 5),
           "sum_part_share": round(share, 5), "K_from_R": [int(k) for k in rank[:8]], "N_oracle": {}}
    for m in M_LIST:
        Rm = np.broadcast_to(R.mean(0), R.shape).copy()
        for k in rank[:m]:
            for wave in (np.cos(2 * np.pi * k * T / P), np.sin(2 * np.pi * k * T / P)):
                Rm += np.outer(wave, wave @ Rc) / (wave @ wave)
        out["N_oracle"][m] = int(P * (Rm.argmax(1) != T).sum())          # wrong pairs: 113 per wrong sum
    return out


if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(json.dumps(probe(p)), flush=True)
