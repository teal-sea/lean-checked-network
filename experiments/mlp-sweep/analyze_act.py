"""experiments/circle-curve/analyze_curve.py with the activation read from each checkpoint's `act`
field (sq when absent) and one more column: circle_bias_wrong, the one-wave projection plus the
baseline-cancelling class bias of experiments/circle-curve (bias[c] = sum_n (W2 - W2_wave)[c, n] *
mean over all pairs of act(E1_wave[a] + E2_wave[b])[n], added to every logit of class c, in float).

Usage: python3 analyze_act.py OUTDIR  -> OUTDIR/curve.csv
"""
import csv
import glob
import os
import sys
import numpy as np

outdir = sys.argv[1]


ACT = 'sq'


def act(z):
    return z * z if ACT == 'sq' else np.maximum(z, 0)


def wrong_count(E1, E2, W2, p, bias=None):
    pairs = np.array([(a, b) for a in range(p) for b in range(p)])
    z = E1[pairs[:, 0]] + E2[pairs[:, 1]]
    S = act(z) @ W2.T
    if bias is not None:
        S = S + bias
    pred = S.argmax(1)
    lab = pairs.sum(1) % p
    top2 = np.sort(S, 1)[:, -2:]
    return int((pred != lab).sum()), int((top2[:, 1] - top2[:, 0]).min()), int((top2[:, 0] == top2[:, 1]).sum())


def circle_only(cols, p, H, do_round=True):
    """circle_only.py, verbatim in its choices: dominant k from summed spectral energy over the three
    columns; each column replaced by its wave at k; rounded unless do_round is False."""
    half = (p - 1) // 2
    out = [np.zeros(c.shape, dtype=np.int64 if do_round else float) for c in cols]
    stats = []
    x = np.arange(p)
    for h in range(H):
        if not any(np.any(c[:, h]) for c in cols):
            continue
        tot = np.zeros(half)
        per = []
        for c in cols:
            P = np.abs(np.fft.fft(c[:, h])) ** 2
            pk = P[1:half + 1] + P[p - 1:p - half - 1:-1]
            per.append(pk)
            tot += pk
        k = int(np.argmax(tot)) + 1
        share = float(tot[k - 1] / tot.sum()) if tot.sum() > 0 else 0.0
        # energy share at the dominant k including the DC term and the rest: fraction of total energy
        total_energy = sum(float((np.abs(np.fft.fft(c[:, h])) ** 2).sum()) for c in cols)
        share_all = float(tot[k - 1] / total_energy) if total_energy > 0 else 0.0
        srt = np.sort(tot)[::-1]
        second = float(srt[1] / srt[0]) if srt[0] > 0 else 0.0
        phases = []
        for c, o in zip(cols, out):
            F = np.fft.fft(c[:, h])
            amp = 2 * F[k] / p
            wave = (amp * np.exp(2j * np.pi * k * x / p)).real
            o[:, h] = np.round(wave).astype(np.int64) if do_round else wave
            phases.append(np.angle(F[k]))
        # mechanism alignment: cos(θa+φ1)·cos(θb+φ2)·cos(θc+ψ) peaks at c=a+b iff φ1+φ2-ψ ≡ 0 (mod 2π)
        # F[k] of cos(θx+φ) has angle φ (up to sign convention, consistent across the three columns)
        err = (phases[0] + phases[1] - phases[2] + np.pi) % (2 * np.pi) - np.pi
        stats.append((k, share, share_all, second, abs(float(err))))
    return out, stats


rows = []
files = sorted(glob.glob(os.path.join(outdir, "ckpt_step*.npz")), key=lambda f: int(f.split("step")[-1].split(".")[0]))
files.append(os.path.join(outdir, "final.npz"))
for f in files:
    if not os.path.exists(f):
        continue
    d = np.load(f)
    ACT = str(d['act']) if 'act' in d.files else 'sq'
    p, H, step = int(d["p"]), int(d["H"]), int(d["steps"])
    cols = [d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"]]
    tw, tg, tt = wrong_count(*cols, p)
    outr, stats = circle_only(cols, p, H, do_round=True)
    cw, cg, ct = wrong_count(*outr, p)
    zz = outr[0][np.array([a for a in range(p) for b in range(p)])] + outr[1][np.array([b for a in range(p) for b in range(p)])]
    bias = (cols[2] - outr[2]).astype(float) @ act(zz).astype(float).mean(0)
    cbw, _, _ = wrong_count(*outr, p, bias=bias)
    outf, _ = circle_only(cols, p, H, do_round=False)
    fw, _, _ = wrong_count(*outf, p)
    # same reduction on the FLOAT weights (before 8-bit freezing), then rounded at the same 127 scale
    colsf = [d[k] for k in ["E1", "E2", "W2"]]
    colsf_q = [np.round(c * (127 / np.abs(c).max())).astype(np.int64) for c in colsf]
    outff, _ = circle_only(colsf_q, p, H, do_round=True)
    ffw, _, _ = wrong_count(*outff, p)
    live = len(stats)
    ks = sorted(set(s[0] for s in stats))
    med_share = float(np.median([s[1] for s in stats])) if stats else 0.0
    med_share_all = float(np.median([s[2] for s in stats])) if stats else 0.0
    multi = float(np.mean([s[3] > 0.25 for s in stats])) if stats else 0.0
    med_phase_err = float(np.median([s[4] for s in stats])) if stats else 0.0
    frac_aligned = float(np.mean([s[4] < 0.3 for s in stats])) if stats else 0.0
    rows.append(dict(step=step, train_acc=float(d["train_acc"]), heldout_acc=float(d["heldout_acc"]),
                     net_wrong=tw, net_gap=tg, net_ties=tt,
                     circle_wrong=cw, circle_gap=cg, circle_ties=ct, circle_bias_wrong=cbw, circle_float_wrong=fw, circle_of_float_wrong=ffw,
                     live=live, n_freqs=len(ks), freqs=" ".join(map(str, ks)),
                     med_dom_share_ac=round(med_share, 4), med_dom_share_all=round(med_share_all, 4),
                     frac_multi_freq=round(multi, 3), med_phase_err=round(med_phase_err, 4), frac_phase_aligned=round(frac_aligned, 3),
                     max_abs_w=max(float(np.abs(c).max()) for c in colsf)))
    print(f"step {step:6d} {ACT} net wrong {tw:5d} | circle wrong {cw:5d} bias {cbw:5d} (float {fw:5d}, of-float {ffw:5d}) | live {live:3d} freqs {len(ks):2d} "
          f"dom-share {med_share:.3f} multi {multi:.2f} phase-err {med_phase_err:.3f} aligned {frac_aligned:.2f} | acc tr {float(d['train_acc']):.3f} te {float(d['heldout_acc']):.3f}",
          flush=True)

with open(os.path.join(outdir, "curve.csv"), "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
    w.writeheader()
    w.writerows(rows)
print("wrote", os.path.join(outdir, "curve.csv"))
