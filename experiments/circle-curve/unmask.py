"""Grokking as unmasking? Over every checkpoint of every run: is each neuron's dominant frequency
already its final one; how the clock's margin and the rest of the logits (the mask) evolve on
held-out pairs; when the clock's margin first exceeds the mask versus when held-out accuracy jumps.

Usage: python3 unmask.py GRID_DIR OUT_DIR [--procs N]
Per run: OUT_DIR/<run>.csv (one row per checkpoint). Then OUT_DIR/summary.csv (one row per run)."""
import sys, os, glob, csv, re, numpy as np
from multiprocessing import Pool

def onewave(cols, p, H):
    half = (p - 1) // 2
    out = [np.zeros(c.shape, dtype=np.int64) for c in cols]; ks = np.full(H, -1)
    for h in range(H):
        if not any(np.any(c[:, h]) for c in cols): continue
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1; ks[h] = k
        for F, o in zip(Fs, out):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    return out, ks

def margin(M, c):
    idx = np.arange(len(c)); t = M[idx, c].copy(); M2 = M.copy(); M2[idx, c] = np.iinfo(np.int64).min
    return t - M2.max(1)

def one_ckpt(path, kfinal):
    d = np.load(path); p, H = int(d['p']), int(d['H'])
    cols = [d[k].astype(np.int64) for k in ['E1q', 'E2q', 'W2q']]
    one, ks = onewave(cols, p, H)
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p); c = (a + b) % p
    S = ((cols[0][a] + cols[1][b]) ** 2) @ cols[2].T
    S1 = ((one[0][a] + one[1][b]) ** 2) @ one[2].T
    R = S - S1
    tr = np.zeros(p * p, bool); tr[d['train_idx']] = True
    m1 = margin(S1, c); mS = margin(S, c); mR = -margin(R, c)   # mR > 0: the rest of the logits favour a wrong class
    live = ks >= 0
    same = float((ks[live] == kfinal[live]).mean()) if live.any() else float('nan')
    return dict(step=int(d['steps']), train_acc=float(d['train_acc']), heldout_acc=float(d['heldout_acc']),
                net_wrong=int((mS <= 0).sum()), clock_wrong=int((m1 <= 0).sum()), clock_wrong_heldout=int((m1[~tr] <= 0).sum()),
                clock_margin_heldout_med=float(np.median(m1[~tr])), mask_adv_heldout_med=float(np.median(mR[~tr])),
                mask_adv_train_med=float(np.median(mR[tr])), mask_abs_heldout_med=float(np.median(np.abs(mR[~tr]))),
                frac_heldout_clock_beats_mask=float((m1[~tr] > mR[~tr]).mean()),
                R_norm_over_S1=float(np.linalg.norm(R) / max(1.0, np.linalg.norm(S1))),
                frac_same_freq_as_final=same, live=int(live.sum()), n_freqs=int(len(set(ks[live].tolist()))))

def one_run(args):
    run, out_dir = args
    try:
        f = np.load(os.path.join(run, 'final.npz')); p, H = int(f['p']), int(f['H'])
        _, kfinal = onewave([f[k].astype(np.int64) for k in ['E1q', 'E2q', 'W2q']], p, H)
        files = sorted(glob.glob(os.path.join(run, 'ckpt_step*.npz')), key=lambda s: int(re.search(r'step(\d+)', s).group(1)))
        rows = [one_ckpt(fp, kfinal) for fp in files]
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
            def first(cond):
                return next((r['step'] for r in rows if cond(r)), None)
            s = dict(run=name, grok_step=first(lambda r: r['heldout_acc'] >= 0.5), grok90_step=first(lambda r: r['heldout_acc'] >= 0.9),
                     cross_step=first(lambda r: r['step'] > 0 and r['clock_margin_heldout_med'] > r['mask_adv_heldout_med']),
                     cross50_step=first(lambda r: r['step'] > 0 and r['frac_heldout_clock_beats_mask'] >= 0.5),
                     clock_wrong_100=next((r['clock_wrong'] for r in rows if r['step'] == 100), None),
                     clock_wrong_500=next((r['clock_wrong'] for r in rows if r['step'] == 500), None),
                     clock_wrong_final=rows[-1]['clock_wrong'], net_wrong_final=rows[-1]['net_wrong'], heldout_final=rows[-1]['heldout_acc'],
                     same_freq_100=next((r['frac_same_freq_as_final'] for r in rows if r['step'] == 100), None),
                     same_freq_500=next((r['frac_same_freq_as_final'] for r in rows if r['step'] == 500), None),
                     same_freq_2000=next((r['frac_same_freq_as_final'] for r in rows if r['step'] == 2000), None),
                     R_over_S1_100=next((r['R_norm_over_S1'] for r in rows if r['step'] == 100), None), R_over_S1_final=rows[-1]['R_norm_over_S1'])
            summ.append(s); print(name, {k: v for k, v in s.items() if k != 'run'}, flush=True)
    summ.sort(key=lambda s: s['run'])
    with open(os.path.join(out_dir, 'summary.csv'), 'w') as fh:
        w = csv.DictWriter(fh, fieldnames=list(summ[0].keys())); w.writeheader(); w.writerows(summ)
    print('done', len(summ), 'runs')
