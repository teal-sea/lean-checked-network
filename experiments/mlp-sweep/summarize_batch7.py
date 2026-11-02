"""Score the seventh batch against RULES.md (fixed before the runs; this script after them, before
reading any result). Usage: python3 summarize_batch7.py DIR (run directories with curve_holdout.csv)."""
import csv
import glob
import os
import re
import sys

root = sys.argv[1]
runs = {os.path.basename(os.path.dirname(f)): sorted(csv.DictReader(open(f)), key=lambda r: int(r['step']))
        for f in glob.glob(os.path.join(root, '**', 'curve_holdout.csv'), recursive=True)}
cells = {}
for name, rows in runs.items():
    m = re.match(r'x2_h([ts])(\d+)_H(\d+)_s(\d+)$', name)
    if m:
        cells[(m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)))] = rows


def tstar(rows, key='clock_wrong'):
    seq = [(int(r['step']), int(r[key])) for r in rows]
    return next((st for i, (st, v) in enumerate(seq) if st >= 1 and all(w == 0 for _, w in seq[i:])), None)


for kind, label, g in (('t', 'held-out TOKENS', 'tok'), ('s', 'held-out SUMS', 'sum')):
    print(f'## {label}: t* (all 9,409 pairs) per seed | at step 500: clock wrong on held-out pairs / net wrong on them (of n pairs) | training pairs')
    for H in (1024, 2048):
        for k in (1, 3, 10, 30):
            out = []
            for s in range(3):
                rows = cells.get((kind, k, H, s))
                if not rows:
                    out.append('?'); continue
                last = rows[-1]
                t = tstar(rows)
                out.append(f"t* {t if t else '-(' + str(min(int(r['clock_wrong']) for r in rows if int(r['step']) >= 1)) + ')'} | "
                           f"{last[f'clock_wrong_{g}']}/{last[f'net_wrong_{g}']} of {last[f'pairs_{g}']}")
            ntr = cells.get((kind, k, H, 0), [{}])[-1].get('pairs_train')
            print(f"  H {H} k {k:2d} (train {ntr}): " + '  ||  '.join(out))
