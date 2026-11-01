"""Second pass of the unmasking test, with the bias split out: logits = clock + bias + mask, where
bias[c] = (W2 - W2_wave)[c] . mean squared one-wave activation (a per-class constant) and mask is the rest.
Per checkpoint, on held-out pairs: the clock+bias margin against the mask's advantage for its best wrong
class; the step where the clock+bias first beats the mask on half the held-out pairs, versus the step
where held-out accuracy first reaches 0.5.  Usage: python3 unmask2.py GRID_DIR OUT_DIR [--procs N]"""
import sys, os, glob, csv, re, numpy as np
from multiprocessing import Pool
from unmask import onewave, margin

def one_ckpt(path):
    d = np.load(path); p, H = int(d['p']), int(d['H'])
    cols = [d[k].astype(np.int64) for k in ['E1q', 'E2q', 'W2q']]
    one, ks = onewave(cols, p, H)
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p); c = (a + b) % p
    act1 = (one[0][a] + one[1][b]) ** 2
    S = ((cols[0][a] + cols[1][b]) ** 2) @ cols[2].T
    S1 = act1 @ one[2].T
    bias = (cols[2] - one[2]) @ act1.mean(0)
    S1b = S1 + np.round(bias).astype(np.int64)[None, :]
    mask = S - S1b
    tr = np.zeros(p * p, bool); tr[d['train_idx']] = True
    m1b = margin(S1b, c); mM = -margin(mask, c); mS = margin(S, c); m1 = margin(S1, c)
    return dict(step=int(d['steps']), train_acc=float(d['train_acc']), heldout_acc=float(d['heldout_acc']),
                net_wrong=int((mS <= 0).sum()), clock_wrong=int((m1 <= 0).sum()), clockbias_wrong=int((m1b <= 0).sum()),
                clockbias_wrong_heldout=int((m1b[~tr] <= 0).sum()),
                clockbias_margin_heldout_med=float(np.median(m1b[~tr])), mask_adv_heldout_med=float(np.median(mM[~tr])),
                mask_adv_train_med=float(np.median(mM[tr])),
                frac_heldout_clockbias_beats_mask=float((m1b[~tr] > mM[~tr]).mean()),
                frac_train_clockbias_beats_mask=float((m1b[tr] > mM[tr]).mean()),
                mask_norm_over_clockbias=float(np.linalg.norm(mask - mask.mean(1, keepdims=True)) / max(1.0, np.linalg.norm(S1b - S1b.mean(1, keepdims=True)))))

def one_run(args):
    run, out_dir = args
    try:
        files = sorted(glob.glob(os.path.join(run, 'ckpt_step*.npz')), key=lambda s: int(re.search(r'step(\d+)', s).group(1)))
        rows = [one_ckpt(fp) for fp in files]
        name = os.path.basename(run.rstrip('/'))
        with open(os.path.join(out_dir, name + '.csv'), 'w') as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
        return name, rows
    except Exception as e:
        return os.path.basename(run.rstrip('/')), str(e)

if __name__ == '__main__':
    grid, out_dir = sys.argv[1], sys.argv[2]; os.makedirs(out_dir, exist_ok=True)
    procs = int(sys.argv[sys.argv.index('--procs') + 1]) if '--procs' in sys.argv else 8
    runs = sorted(d for d in glob.glob(os.path.join(grid, '*/')) if os.path.exists(os.path.join(d, 'final.npz')))
    summ = []
    with Pool(procs) as pool:
        for name, rows in pool.imap_unordered(one_run, [(r, out_dir) for r in runs]):
            if isinstance(rows, str): print('FAIL', name, rows, flush=True); continue
            first = lambda cond: next((r['step'] for r in rows if r['step'] > 0 and cond(r)), None)
            at = lambda s, k: next((r[k] for r in rows if r['step'] == s), None)
            s = dict(run=name, grok_step=first(lambda r: r['heldout_acc'] >= 0.5), grok90_step=first(lambda r: r['heldout_acc'] >= 0.9),
                     cross50_step=first(lambda r: r['frac_heldout_clockbias_beats_mask'] >= 0.5),
                     cross90_step=first(lambda r: r['frac_heldout_clockbias_beats_mask'] >= 0.9),
                     clockbias_wrong_100=at(100, 'clockbias_wrong'), clockbias_wrong_500=at(500, 'clockbias_wrong'), clockbias_wrong_final=rows[-1]['clockbias_wrong'],
                     clock_wrong_100=at(100, 'clock_wrong'), net_wrong_final=rows[-1]['net_wrong'], heldout_final=rows[-1]['heldout_acc'],
                     mask_ratio_100=at(100, 'mask_norm_over_clockbias'), mask_ratio_final=rows[-1]['mask_norm_over_clockbias'],
                     beats_mask_heldout_final=rows[-1]['frac_heldout_clockbias_beats_mask'], beats_mask_train_final=rows[-1]['frac_train_clockbias_beats_mask'])
            summ.append(s); print(name, {k: v for k, v in s.items() if k != 'run'}, flush=True)
    summ.sort(key=lambda s: s['run'])
    with open(os.path.join(out_dir, 'summary.csv'), 'w') as fh:
        w = csv.DictWriter(fh, fieldnames=list(summ[0].keys())); w.writeheader(); w.writerows(summ)
    print('done', len(summ), 'runs')
