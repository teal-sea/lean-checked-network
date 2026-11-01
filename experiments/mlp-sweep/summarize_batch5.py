"""Score the fifth batch against RULES.md (written before the runs; this script after them, before
reading any result). Usage: python3 summarize_batch5.py DIR (run directories at any depth, each with
the curve.csv of analyze_act.py)."""
import csv
import glob
import os
import re
import sys

root = sys.argv[1]
runs = {os.path.basename(os.path.dirname(f)): list(csv.DictReader(open(f)))
        for f in glob.glob(os.path.join(root, '**', 'curve.csv'), recursive=True)}


def tstar(rows):
    seq = sorted((int(r['step']), int(r['circle_wrong'])) for r in rows)
    for i, (st, v) in enumerate(seq):
        if st >= 1 and all(w == 0 for _, w in seq[i:]):
            return st, seq
    return None, seq


print('## A. Wrong labels (x^2, frac 0.3, 500 steps): t*[circle_wrong at step 1]; predicted t* = ceil(10 / ((1 - noise) lr H))')
cells = {}
for name, rows in runs.items():
    m = re.match(r'x2_n([\d.]+)_H(\d+)_s(\d+)$', name)
    if m:
        cells[(float(m.group(1)), int(m.group(2)), int(m.group(3)))] = rows
for eta in sorted({k[0] for k in cells}):
    for H in sorted({k[1] for k in cells}):
        out = []
        for s in range(3):
            rows = cells.get((eta, H, s))
            if not rows:
                out.append('?'); continue
            t, seq = tstar(rows)
            d = dict(seq)
            fin = rows[-1]
            # the noise really is there: at step 500 the net fits its noisy training labels, so it is
            # wrong (against a + b) on the noisy training pairs as well as on held-out pairs
            out.append(f"{t if t else '-(' + str(min(w for st, w in seq if st >= 1)) + ')'}[{d.get(1)}] net {fin['net_wrong']} tr {float(fin['train_acc']):.3f}")
        pred = -(-10 // ((1 - eta) * 0.01 * H))
        print(f"noise {eta:<5} H {H:5d} predicted t* {int(pred):3d} | " + ' | '.join(out))
print('  sanity: a clean frac-0.3 memorizer is wrong on about 6,560; noise f adds about f x 2,823 wrong training pairs')

print('\n## B. Width and modulus (x^2, frac 0.3, steps 1-5): t* per seed [circle_wrong at step 1]; predicted t* 4, 3, 2, 2 for H 256, 384, 512, 768')
cells = {}
for name, rows in runs.items():
    m = re.match(r'x2_p(\d+)_H(\d+)_s(\d+)$', name)
    if m:
        cells[(int(m.group(1)), int(m.group(2)), int(m.group(3)))] = rows
Hs = sorted({k[1] for k in cells})
print('p     ' + ' | '.join(f'H {H}' + ' ' * 26 for H in Hs))
for p in sorted({k[0] for k in cells}):
    row = []
    for H in Hs:
        v = []
        for s in range(5):
            rows = cells.get((p, H, s))
            if not rows:
                v.append('?'); continue
            t, seq = tstar(rows)
            v.append(f"{t if t else '-'}[{dict(seq).get(1)}]")
        row.append(' '.join(v))
    print(f"{p:<5} " + ' | '.join(f'{c:31s}' for c in row))
print('\nnet wrong at step 1 (min-max over seeds) and chance (p^2 - p) per p:')
for p in sorted({k[0] for k in cells}):
    nw = [int(next(r for r in rows if int(r['step']) == 1)['net_wrong']) for (pp, H, s), rows in cells.items() if pp == p]
    print(f"  p {p}: {min(nw)}-{max(nw)} (chance about {p * p - p})")
