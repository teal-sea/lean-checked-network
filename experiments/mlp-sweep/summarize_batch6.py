"""Score the sixth batch against RULES.md (fixed before the runs; this script written after them,
before reading any result). Usage: python3 summarize_batch6.py DIR (run directories at any depth,
each with curve_even.csv)."""
import csv
import glob
import os
import re
import sys

root = sys.argv[1]
# r and predicted t* exactly as fixed in RULES.md (sixth batch table)
PRED = {('sqlin', '0.25', 1024): (0.222, 4.0), ('sqlin', '0.5', 1024): (0.111, 7.9), ('sqlin', '1', 1024): (0.0554, 15.9),
        ('sqlin', '2', 1024): (0.0277, 31.7), ('sqlin', '4', 1024): (0.0138, 63.5), ('sqlin', '8', 1024): (0.0069, 126.9),
        ('tanhsq', '0.5', 1024): (0.0277, 31.7), ('tanhsq', '1', 1024): (0.0555, 15.8), ('tanhsq', '2', 1024): (0.111, 7.9),
        ('tanhsq', '4', 1024): (0.222, 4.0), ('tanhsq', '10', 1024): (0.555, 1.6),
        ('gelu', '', 512): (0.0624, 28.2), ('gelu', '', 2048): (0.0312, 14.1), ('gelu', '', 4096): (0.0221, 9.9)}
runs = {os.path.basename(os.path.dirname(f)): sorted(csv.DictReader(open(f)), key=lambda r: int(r['step']))
        for f in glob.glob(os.path.join(root, '**', 'curve_even.csv'), recursive=True)}


def tstar(rows, key):
    seq = [(int(r['step']), int(r[key])) for r in rows]
    t = next((st for i, (st, v) in enumerate(seq) if st >= 1 and all(w == 0 for _, w in seq[i:])), None)
    prev = max((st for st, v in seq if t is not None and st < t), default=0)
    return t, prev, seq


ok1 = []
print(f"{'run':22s} {'r':>7s} {'pred t*':>8s} {'t* (z^2)':>9s} {'prev ckpt':>9s} {'ratio':>6s} | own readout at 300 | net at 300 (own)")
for name in sorted(runs):
    m = re.match(r'(sqlin|tanhsq)([\d.]+)_H(\d+)_s(\d+)$', name) or re.match(r'(gelu)()_H(\d+)_s(\d+)$', name) or re.match(r'(tanh)()_H(\d+)_s(\d+)$', name)
    if not m:
        print('skip', name); continue
    act, c, H, seed = m.group(1), m.group(2), int(m.group(3)), int(m.group(4))
    rows = runs[name]
    t, prev, seq = tstar(rows, 'proj_sq')
    last = rows[-1]
    key = (act, c, H)
    if key in PRED:
        r, pt = PRED[key]
        ratio = (t / pt) if t else float('inf')
        covered = r <= 0.15
        verdict = ('within 2x' if t and 0.5 <= ratio <= 2 else 'OUTSIDE 2x') if covered else ('t* <= pred' if t and t <= pt else 'ABOVE pred')
        if covered and seed == 0:
            ok1.append(verdict == 'within 2x')
        print(f"{name:22s} {r:7.4f} {pt:8.1f} {str(t):>9s} {prev:9d} {ratio:6.2f} | {last['proj_own']:>5s} | {last['net_own']:>5s}  {verdict}")
    else:
        print(f"{name:22s} {'-':>7s} {'-':>8s} {str(t):>9s} {prev:9d} {'':6s} | {last['proj_own']:>5s} | {last['net_own']:>5s}  control (z^2 readout min {min(v for st, v in seq if st >= 1)})")
print(f"\nprediction (1) on the seed-0 runs with r <= 0.15: {sum(ok1)} of {len(ok1)} within a factor 2 (win: at least 9 of 11)")
