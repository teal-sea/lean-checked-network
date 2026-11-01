"""Where is the projection right? (seventh batch.) For every checkpoint of a train_act.py run: the integer
pure clock (each neuron's dominant wave, rounded: what seal_cell.py --pure-clock checks), and the frozen
net, scored against (a + b) mod p on four groups of pairs: pairs with a held-out token, pairs whose sum is
a held-out sum, the training pairs, and the other pairs never trained on.

Usage: python3 holdout_eval.py OUTDIR  -> OUTDIR/curve_holdout.csv, one line per checkpoint on stdout."""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int_even import clock  # noqa: E402


def wrong_mask(E1, E2, W2, p):
    a, b = np.divmod(np.arange(p * p), p)
    S = (E1[a] + E2[b]) ** 2 @ W2.T
    return S.argmax(1) != (a + b) % p


outdir = sys.argv[1]
files = sorted(glob.glob(os.path.join(outdir, "ckpt_step*.npz")), key=lambda f: int(f.split("step")[-1].split(".")[0]))
rows = []
for f in files:
    d = np.load(f)
    assert str(d["act"]) == "sq"
    p, step = int(d["p"]), int(d["steps"])
    a, b = np.divmod(np.arange(p * p), p)
    ht, hs = d["hold_tokens"], d["hold_sums"]
    groups = {"tok": np.isin(a, ht) | np.isin(b, ht), "sum": np.isin((a + b) % p, hs)}
    trm = np.zeros(p * p, bool); trm[d["train_idx"]] = True
    groups["train"] = trm
    groups["other"] = ~(trm | groups["tok"] | groups["sum"])
    cols = [d[k].astype(np.int64) for k in ("E1q", "E2q", "W2q")]
    wn, wc = wrong_mask(*cols, p), wrong_mask(*clock(cols, p), p)
    r = dict(step=step, n_hold_tokens=len(ht), n_hold_sums=len(hs), clock_wrong=int(wc.sum()), net_wrong=int(wn.sum()))
    for g, msk in groups.items():
        r[f"pairs_{g}"] = int(msk.sum()); r[f"clock_wrong_{g}"] = int((wc & msk).sum()); r[f"net_wrong_{g}"] = int((wn & msk).sum())
    rows.append(r)
    print(f"step {step:5d} | clock wrong {r['clock_wrong']:5d} (held-out tokens {r['clock_wrong_tok']}/{r['pairs_tok']}, sums {r['clock_wrong_sum']}/{r['pairs_sum']}) "
          f"| net wrong {r['net_wrong']:5d} (tokens {r['net_wrong_tok']}, sums {r['net_wrong_sum']}, train {r['net_wrong_train']}/{r['pairs_train']})", flush=True)
with open(os.path.join(outdir, "curve_holdout.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
