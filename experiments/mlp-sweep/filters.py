"""Liu & Lu's frequency filtration against the projection of the seals (eleventh batch, 2026-11-02).

Liu & Lu 2026 (arXiv 2605.18022, Sec. 4 and App. D.1) reduce each neuron m to one frequency: the DFT row k
with the largest |w_m hat| over all k (DC included), kept in the neuron's input and output weights,
P_G u = Re(F^H F_G u), in float. The seals take the arg max over k = 1..(p-1)/2 of the spectral energy summed
over the neuron's three columns (E1, E2, W2), keep k and p - k, and round, on the frozen 8-bit tables
(int_even.clock). Every checkpoint is read six ways on all p^2 pairs, with the activation it was trained with:

  net         the frozen network itself
  ll          Liu & Lu as published: float weights, W2's largest |DFT| row (DC included), real part, no rounding
  ll_nodc     the same with k = 0 excluded (a neuron sent to DC is constant in c and drops out of the arg max)
  ll_int      Liu & Lu's frequency on the frozen tables, components k and p - k, rounded
  ours_float  the seals' frequency on float weights, components k and p - k, no rounding
  ours        the seals' projection (int_even.clock)

and two probes of whether the choice matters at all, both float, components k and p - k, no rounding:

  rand        each neuron's frequency drawn uniformly from 1..(p-1)/2 (generator 1000 + the run's seed, so the
              same draw at every checkpoint of a run)
  min         the frequency with the least spectral energy summed over the three columns

plus the share of neurons where ll and ours pick the same frequency (k or p - k: agree_q on the frozen
tables, agree_f on float weights) and how many neurons ll sends to DC. Integer tables are evaluated in float64,
which is exact here (every partial sum is an integer below 2^53; asserted).

Usage: python3 filters.py INDIR [OUTCSV]  -> OUTCSV (default INDIR/curve_filters.csv), one line per checkpoint
on stdout. INDIR holds the ckpt_step*.npz and final.npz of train_act.py, or any *.npz with E1q/E2q/W2q (files
without float weights get only the integer readings). FILTER_ACT=sq|relu|abs overrides the activation; a file
named *readsq* is read with z^2, as its seal was. SEAL_REF=FILE@STEP compares the frozen tables at STEP with
those of FILE (a seal input; a relative path is taken from this script's directory), column seal_match.
"""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int_even import clock  # noqa: E402  the seals' projection (rounded)

ACTS = {'sq': lambda z: z * z, 'relu': lambda z: np.maximum(z, 0), 'abs': np.abs}


def wrong(E1, E2, W2, p, f, exact_int=False):
    a, b = np.divmod(np.arange(p * p), p)
    E1, E2, W2 = (np.asarray(x, dtype=np.float64) for x in (E1, E2, W2))
    if exact_int:  # |f(z)| <= f(|z|) for all three activations, so this bounds every partial sum
        zmax = np.abs(E1).max(0) + np.abs(E2).max(0)
        assert float((f(zmax) * np.abs(W2).max(0)).sum()) < 2.0 ** 53
    S = f(E1[a] + E2[b]) @ W2.T
    top2 = np.sort(S, 1)[:, -2:]
    return int((S.argmax(1) != (a + b) % p).sum()), int((top2[:, 0] == top2[:, 1]).sum())


def ll_filter(cols, p, dc=True, two_sided=False, do_round=False):
    """Per neuron, k = arg max over k of |DFT(W2 column)| (k >= 1 when dc is False). two_sided False is the
    paper's P_G: row k alone, real part (half the wave of k and p - k together, the same shape); two_sided True
    keeps k and p - k, the seals' convention, so rounded tables are on the seals' scale. Returns the filtered
    columns and each neuron's frequency as 0..(p-1)/2."""
    F = [np.fft.fft(np.asarray(c, dtype=np.float64), axis=0) for c in cols]
    mag = np.abs(F[2])
    if not dc:
        mag[0] = -1.0
    k = mag.argmax(0)
    n = np.arange(cols[0].shape[1]); x = np.arange(p)
    kk = np.minimum(k, p - k)
    out = []
    for Fc in F:
        if two_sided:
            G = np.zeros_like(Fc); G[kk, n] = Fc[kk, n]; G[(p - kk) % p, n] = Fc[(p - kk) % p, n]
            w = np.fft.ifft(G, axis=0).real
        else:
            w = (Fc[k, n][None, :] * np.exp(2j * np.pi * np.outer(x, k) / p) / p).real
        out.append(np.round(w).astype(np.int64) if do_round else w)
    return out, kk


def energy(cols, p):
    """Spectral energy summed over the three columns at k = 1..(p-1)/2, (p-1)/2 x H."""
    half = (p - 1) // 2
    return sum(np.abs(np.fft.fft(np.asarray(c, dtype=np.float64), axis=0)) ** 2 for c in cols)[1:half + 1]


def ours_freq(cols, p):
    return energy(cols, p).argmax(0) + 1


def one_freq(cols, p, k):
    """Each neuron's columns reduced to components k and p - k (k in 1..(p-1)/2 per neuron), float."""
    n = np.arange(cols[0].shape[1])
    out = []
    for c in cols:
        Fc = np.fft.fft(np.asarray(c, dtype=np.float64), axis=0)
        G = np.zeros_like(Fc); G[k, n] = Fc[k, n]; G[p - k, n] = Fc[p - k, n]
        out.append(np.fft.ifft(G, axis=0).real)
    return out


def files_in(indir):
    """(files sorted by step, whether INDIR is one run's checkpoints)."""
    ck = glob.glob(os.path.join(indir, "ckpt_step*.npz"))
    fs = ck + glob.glob(os.path.join(indir, "final.npz")) if ck else glob.glob(os.path.join(indir, "*.npz"))
    return sorted(fs, key=lambda f: (int(np.load(f)["steps"]), f)), bool(ck)


def act_of(f, d):
    name = os.environ.get("FILTER_ACT") or ("sq" if "readsq" in os.path.basename(f) else str(d["act"]) if "act" in d.files else "sq")
    return name if name in ACTS else None


def main():
    indir = sys.argv[1]
    outcsv = sys.argv[2] if len(sys.argv) > 2 else os.path.join(indir, "curve_filters.csv")
    ref = os.environ.get("SEAL_REF")
    ref_file, ref_step = (ref.rsplit("@", 1)[0], int(ref.rsplit("@", 1)[1])) if ref else (None, None)
    if ref_file and not os.path.isabs(ref_file):
        ref_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), ref_file)  # relative to this script
    rows, seen = [], set()
    files, one_run = files_in(indir)
    for f in files:
        d = np.load(f)
        p, step = int(d["p"]), int(d["steps"])
        if one_run and step in seen:
            continue  # final.npz repeats the last checkpoint
        seen.add(step)
        name = act_of(f, d)
        if name is None:
            print(f"{os.path.basename(f)}: activation {d['act']} not readable here, skipped", flush=True)
            continue
        g = ACTS[name]
        q = [d[k].astype(np.int64) for k in ("E1q", "E2q", "W2q")]
        r = dict(file=os.path.basename(f), step=step, act=name, H=int(d["H"]), seed=int(d["seed"]), lr=float(d["lr"]),
                 frac=float(d["frac"]), noise_frac=float(d["noise_frac"]) if "noise_frac" in d.files else 0.0,
                 hold_tokens=len(d["hold_tokens"]) if "hold_tokens" in d.files else 0,
                 hold_sums=len(d["hold_sums"]) if "hold_sums" in d.files else 0)
        r["net_wrong"], _ = wrong(*q, p, g, exact_int=True)
        llq, kk_q = ll_filter(q, p, two_sided=True, do_round=True)
        r["ll_int_wrong"], r["ll_int_ties"] = wrong(*llq, p, g, exact_int=True)
        oq = clock(q, p)
        k_q = ours_freq(q, p)
        r["ours_wrong"], r["ours_ties"] = wrong(*oq, p, g, exact_int=True)
        r["agree_q"] = round(float((kk_q == k_q).mean()), 4)
        if "E1" in d.files:
            fl = [d[k] for k in ("E1", "E2", "W2")]
            llf, kk_f = ll_filter(fl, p)
            r["ll_wrong"], _ = wrong(*llf, p, g)
            r["ll_dc"] = int((kk_f == 0).sum())
            r["ll_nodc_wrong"], _ = wrong(*ll_filter(fl, p, dc=False)[0], p, g)
            k_f = ours_freq(fl, p)
            r["ours_float_wrong"], _ = wrong(*one_freq(fl, p, k_f), p, g)
            r["agree_f"] = round(float((kk_f == k_f).mean()), 4)
            half, H = (p - 1) // 2, fl[0].shape[1]
            k_rand = np.random.default_rng(1000 + int(d["seed"])).integers(1, half + 1, H)
            r["rand_wrong"], _ = wrong(*one_freq(fl, p, k_rand), p, g)
            r["min_wrong"], _ = wrong(*one_freq(fl, p, energy(fl, p).argmin(0) + 1), p, g)
        else:
            r.update(ll_wrong="", ll_dc="", ll_nodc_wrong="", ours_float_wrong="", agree_f="", rand_wrong="", min_wrong="")
        r["seal_match"] = ""
        if ref_file and step == ref_step:
            e = np.load(ref_file)
            r["seal_match"] = int(all(np.array_equal(d[k], e[k]) for k in ("E1q", "E2q", "W2q")))
        rows.append(r)
        print(f"step {step:6d} {name} | net {r['net_wrong']:5d} | ll {r['ll_wrong']!s:>5} (DC {r['ll_dc']!s:>4}) nodc {r['ll_nodc_wrong']!s:>5} "
              f"| ll_int {r['ll_int_wrong']:5d} | ours_float {r['ours_float_wrong']!s:>5} | ours {r['ours_wrong']:5d} "
              f"| rand {r['rand_wrong']!s:>5} min {r['min_wrong']!s:>5} "
              f"| agree q {r['agree_q']:.3f} f {r['agree_f']!s:>6} {'| seal tables ' + ('reproduced' if r['seal_match'] else 'DIFFER') if r['seal_match'] != '' else ''}",
              flush=True)
    keys = list(rows[0].keys())
    with open(outcsv, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=keys); w.writeheader(); w.writerows(rows)


if __name__ == "__main__":
    main()
