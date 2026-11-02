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
on stdout. INDIR holds the ckpt_step*.npz and final.npz of one train_act.py run (any other *.npz there is listed
and ignored), or else any set of *.npz with p and E1q/E2q/W2q, such as the seal inputs (steps, H, seed, lr and
frac are read when present; files without float weights get only the integer readings). FILTER_ACT=sq|relu|abs
overrides the activation; a file named *readsq* is read with z^2, as its seal was. SEAL_REF=FILE@STEP compares
the frozen tables at STEP with those of FILE (a seal input; a relative path is taken from this script's
directory), column seal_match. The script writes the CSV and then exits 1 if STEP is not one of the checkpoints
read, if the tables differ, or if no checkpoint could be read, so a sweep job fails instead of passing silently.
"""
import csv
import glob
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int_even import clock, wrong as int_wrong  # noqa: E402  the seals' projection (rounded) and wrong-pair count

ACTS = {'sq': lambda z: z * z, 'relu': lambda z: np.maximum(z, 0), 'abs': np.abs}
TABLES, FLOATS = ("E1q", "E2q", "W2q"), ("E1", "E2", "W2")


def wrong(E1, E2, W2, p, f, exact_int=False):
    """int_even.wrong on contiguous float64 copies, so the product runs on BLAS. For integer tables (exact_int)
    that is exact: every partial sum is an integer below 2^53, asserted here."""
    E1, E2, W2 = (np.ascontiguousarray(x, dtype=np.float64) for x in (E1, E2, W2))
    if exact_int:  # |f(z)| <= f(|z|) for all three activations, so this bounds every partial sum
        zmax = np.abs(E1).max(0) + np.abs(E2).max(0)
        assert float((f(zmax) * np.abs(W2).max(0)).sum()) < 2.0 ** 53
    return int_wrong(E1, E2, W2, p, f)


def spectra(cols):
    """The DFT of every column of each table along the token axis, computed once per table."""
    return [np.fft.fft(np.asarray(c, dtype=np.float64), axis=0) for c in cols]


def keep(F, p, k, do_round=False):
    """Each neuron's columns reduced to DFT rows k and p - k (k in 0..(p-1)/2 per neuron; k = 0 keeps DC once),
    from the spectra F of its three tables; rounded to integers when do_round."""
    n = np.arange(F[0].shape[1]); kc = (p - k) % p
    out = []
    for Fc in F:
        G = np.zeros_like(Fc); G[k, n] = Fc[k, n]; G[kc, n] = Fc[kc, n]
        w = np.fft.ifft(G, axis=0).real
        out.append(np.round(w).astype(np.int64) if do_round else np.ascontiguousarray(w))
    return out


def ll_freq(F, p, dc=True):
    """Liu & Lu's choice per neuron: the arg max over all p DFT rows of |W2 hat| (k = 0 excluded when dc is
    False). Returns the row (0..p-1) and its representative min(k, p - k)."""
    mag = np.abs(F[2])
    if not dc:
        mag = mag.copy(); mag[0] = -1.0
    k = mag.argmax(0)
    return k, np.minimum(k, p - k)


def ll_one_row(F, p, k):
    """The paper's P_G u = Re(F^H F_G u): DFT row k alone, real part. For odd p (every run here) and k >= 1 this is
    half the wave of rows k and p - k together, a factor common to every neuron, so on these bias-free, positively
    homogeneous nets it reads out exactly as keep() does. For even p the row k = p/2 is its own partner and is not
    halved, so the two can differ."""
    n = np.arange(F[0].shape[1]); x = np.arange(p)
    return [np.ascontiguousarray((Fc[k, n][None, :] * np.exp(2j * np.pi * np.outer(x, k) / p) / p).real) for Fc in F]


def energy(F, p):
    """Spectral energy summed over the three tables at k = 1..(p-1)/2, (p-1)/2 x H."""
    return sum(np.abs(Fc) ** 2 for Fc in F)[1:(p - 1) // 2 + 1]


def step_of(f):
    with np.load(f) as d:
        return int(d["steps"]) if "steps" in d.files else 0


def files_in(indir):
    """(files sorted by step, whether INDIR is one run's checkpoints)."""
    every = glob.glob(os.path.join(indir, "*.npz"))
    ck = glob.glob(os.path.join(indir, "ckpt_step*.npz"))
    fs = ck + glob.glob(os.path.join(indir, "final.npz")) if ck else every
    ignored = sorted(set(every) - set(fs))
    if ignored:
        print(f"ignored, not a checkpoint of this run: {', '.join(os.path.basename(f) for f in ignored)}", flush=True)
    return sorted(fs, key=lambda f: (step_of(f), f)), bool(ck)


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
    rows, seen, ref_hit = [], set(), False
    files, one_run = files_in(indir)
    for f in files:
        d = np.load(f)
        p, step = int(d["p"]), int(d["steps"]) if "steps" in d.files else 0
        if one_run and step in seen:
            continue  # final.npz repeats the last checkpoint
        seen.add(step)
        name = act_of(f, d)
        if name is None:
            print(f"{os.path.basename(f)}: activation {d['act'] if 'act' in d.files else os.environ.get('FILTER_ACT')} "
                  f"not readable here, skipped", flush=True)
            continue
        g = ACTS[name]
        q = [d[k].astype(np.int64) for k in TABLES]
        r = dict(file=os.path.basename(f), step=step, act=name, H=q[0].shape[1],
                 seed=int(d["seed"]) if "seed" in d.files else "", lr=float(d["lr"]) if "lr" in d.files else "",
                 frac=float(d["frac"]) if "frac" in d.files else "",
                 noise_frac=float(d["noise_frac"]) if "noise_frac" in d.files else 0.0,
                 hold_tokens=len(d["hold_tokens"]) if "hold_tokens" in d.files else 0,
                 hold_sums=len(d["hold_sums"]) if "hold_sums" in d.files else 0)
        r["net_wrong"], _ = wrong(*q, p, g, exact_int=True)
        Fq = spectra(q)
        _, kk_q = ll_freq(Fq, p)
        r["ll_int_wrong"], r["ll_int_ties"] = wrong(*keep(Fq, p, kk_q, do_round=True), p, g, exact_int=True)
        oq = clock(q, p)
        k_q = energy(Fq, p).argmax(0) + 1
        assert all(np.array_equal(a, b) for a, b in zip(oq, keep(Fq, p, k_q, do_round=True))), \
            "the vectorized projection differs from int_even.clock, so k_q is not the seals' frequency"
        r["ours_wrong"], r["ours_ties"] = wrong(*oq, p, g, exact_int=True)
        r["agree_q"] = round(float((kk_q == k_q).mean()), 4)
        if "E1" in d.files:
            F = spectra([d[k] for k in FLOATS])
            k_ll, kk_f = ll_freq(F, p)
            r["ll_wrong"], _ = wrong(*ll_one_row(F, p, k_ll), p, g)
            r["ll_dc"] = int((kk_f == 0).sum())
            r["ll_nodc_wrong"], _ = wrong(*ll_one_row(F, p, ll_freq(F, p, dc=False)[0]), p, g)
            e = energy(F, p)
            k_f = e.argmax(0) + 1
            r["ours_float_wrong"], _ = wrong(*keep(F, p, k_f), p, g)
            r["agree_f"] = round(float((kk_f == k_f).mean()), 4)
            k_rand = np.random.default_rng(1000 + int(d["seed"])).integers(1, (p - 1) // 2 + 1, r["H"])
            r["rand_wrong"], _ = wrong(*keep(F, p, k_rand), p, g)
            r["min_wrong"], _ = wrong(*keep(F, p, e.argmin(0) + 1), p, g)
        else:
            r.update(ll_wrong="", ll_dc="", ll_nodc_wrong="", ours_float_wrong="", agree_f="", rand_wrong="", min_wrong="")
        r["seal_match"] = ""
        if ref_file and step == ref_step:
            ref_hit = True
            with np.load(ref_file) as e_ref:
                r["seal_match"] = int(all(np.array_equal(d[k], e_ref[k]) for k in TABLES))
        rows.append(r)
        print(f"step {step:6d} {name} | net {r['net_wrong']:5d} | ll {r['ll_wrong']!s:>5} (DC {r['ll_dc']!s:>4}) nodc {r['ll_nodc_wrong']!s:>5} "
              f"| ll_int {r['ll_int_wrong']:5d} | ours_float {r['ours_float_wrong']!s:>5} | ours {r['ours_wrong']:5d} "
              f"| rand {r['rand_wrong']!s:>5} min {r['min_wrong']!s:>5} "
              f"| agree q {r['agree_q']:.3f} f {r['agree_f']!s:>6} {'| seal tables ' + ('reproduced' if r['seal_match'] else 'DIFFER') if r['seal_match'] != '' else ''}",
              flush=True)
    if not rows:
        print(f"PROBLEM: no checkpoint in {indir} could be read", file=sys.stderr, flush=True)
        sys.exit(1)
    with open(outcsv, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    problems = []
    if ref_file and not ref_hit:
        problems.append(f"SEAL_REF step {ref_step} is not among the checkpoints read, so nothing was compared")
    if any(r["seal_match"] == 0 for r in rows):
        problems.append(f"the frozen tables differ from {os.path.basename(ref_file)}")
    if problems:
        print("PROBLEM: " + "; ".join(problems), file=sys.stderr, flush=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
