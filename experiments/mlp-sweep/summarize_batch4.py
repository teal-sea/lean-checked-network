"""Score the fourth batch against RULES.md (written before the runs; this script after, but before
reading any result). Usage: python3 summarize_batch4.py DIR, where DIR holds the run directories
(any depth), each with curve.csv (analyze_act.py), curve_gen.csv and/or curve_even.csv."""
import csv
import glob
import math
import os
import re
import sys
from collections import defaultdict

root = sys.argv[1]
runs = {}
for f in glob.glob(os.path.join(root, '**', 'curve*.csv'), recursive=True):
    runs.setdefault(os.path.basename(os.path.dirname(f)), {})[os.path.basename(f)] = [
        {k: v for k, v in r.items()} for r in csv.DictReader(open(f))]


def ints(rows, key):
    return [(int(r['step']), int(r[key])) for r in rows]


print('## A. |x| (integer projection circle_wrong, analyze_act.py; float projection from curve_gen.csv)')
for name in sorted(n for n in runs if n.startswith('abs_')):
    c = runs[name].get('curve.csv')
    if not c:
        print(name, 'missing curve.csv'); continue
    late = [r for r in c if int(r['step']) >= 100]
    cw = [int(r['circle_wrong']) for r in late]
    early = {int(r['step']): int(r['circle_wrong']) for r in c if int(r['step']) <= 5}
    ho = max(float(r['heldout_acc']) for r in late)
    fin = c[-1]
    print(f"{name:20s} ckpts>=100 {len(late)} circle_wrong all 0: {all(x == 0 for x in cw)} (min {min(cw)}, max {max(cw)}, final {fin['circle_wrong']}) "
          f"| bias final {fin['circle_bias_wrong']} | net final {fin['net_wrong']} | held-out max {ho:.4f} | steps 0-5: {[early.get(s) for s in range(6)]}")

print('\n## B. f(s z)/s at H 1024 (float projection; even/odd evaluation)')
R = {('gelus', 1): 0.044, ('gelus', 3): 0.131, ('gelus', 10): 0.404, ('gelus', 30): 0.798, ('gelus', 100): 0.975,
     ('silus', 1): 0.028, ('silus', 3): 0.083, ('silus', 10): 0.265, ('silus', 30): 0.620, ('silus', 100): 0.928,
     ('tanhs', 1): 0.0, ('tanhs', 10): 0.0, ('tanhs', 100): 0.0}
pts = []
for name in sorted(n for n in runs if re.match(r'(gelus|silus|tanhs)\d+_H1024_s\d+$', n)):
    m = re.match(r'(gelus|silus|tanhs)(\d+)_H1024_s(\d+)$', name)
    act, s, seed = m.group(1), int(m.group(2)), int(m.group(3))
    g = runs[name].get('curve_gen.csv'); e = runs[name].get('curve_even.csv')
    if not g:
        print(name, 'missing curve_gen.csv'); continue
    pw = dict(ints(g, 'proj_wrong'))
    first0 = next((st for st, v in sorted(pw.items()) if v == 0), None)
    ev = {int(r['step']): r for r in e} if e else {}
    e2 = ev.get(2000, {})
    pts.append((R[(act, s)], act, s, seed, pw.get(1000), pw.get(2000)))
    print(f"{name:20s} r {R[(act, s)]:.3f} | proj at 1: {pw.get(1)} 5: {pw.get(5)} 50: {pw.get(50)} 100: {pw.get(100)} 1000: {pw.get(1000)} 2000: {pw.get(2000)} | first exact {first0} "
          f"| at 2000 even {e2.get('proj_even')} odd {e2.get('proj_odd')} sq {e2.get('proj_sq')} abs {e2.get('proj_abs')} | net {g[-1]['net_wrong']} ho {float(g[-1]['heldout_acc']):.4f}")
print('\nprediction 1 (wrong count at 1,000 and 2,000 falls as r rises, GELU and SiLU on one curve):')
gs = sorted((p for p in pts if p[1] != 'tanhs'), key=lambda p: p[0])
for p in gs:
    print(f"  r {p[0]:.3f} {p[1]} s {p[2]} seed {p[3]}: {p[4]} at 1000, {p[5]} at 2000")


def spearman(xs, ys):
    def rank(v):
        o = sorted(range(len(v)), key=lambda i: v[i]); rk = [0] * len(v)
        i = 0
        while i < len(o):
            j = i
            while j + 1 < len(o) and v[o[j + 1]] == v[o[i]]:
                j += 1
            for k in range(i, j + 1):
                rk[o[k]] = (i + j) / 2
            i = j + 1
        return rk
    a, b = rank(xs), rank(ys); n = len(a); ma, mb = sum(a) / n, sum(b) / n
    cov = sum((x - ma) * (y - mb) for x, y in zip(a, b))
    return cov / math.sqrt(sum((x - ma) ** 2 for x in a) * sum((y - mb) ** 2 for y in b))


for col, lab in ((4, 1000), (5, 2000)):
    xs = [p[0] for p in gs if p[col] is not None]; ys = [p[col] for p in gs if p[col] is not None]
    if len(xs) > 2:
        print(f"  Spearman(r, wrong at {lab}) = {spearman(xs, ys):.3f} over {len(xs)} runs")
for name in sorted(n for n in runs if n.endswith('_20k') and n.startswith('gelus')):
    e = runs[name].get('curve_even.csv')
    if e:
        print(f"\n{name}: step, proj own / even / odd / sq / abs, net own / even / odd")
        for r in e:
            if int(r['step']) in (0, 1, 5, 100, 1000, 5000, 10000, 20000):
                print(f"  {r['step']:>6s} proj {r['proj_own']:>5s} {r['proj_even']:>5s} {r['proj_odd']:>5s} {r['proj_sq']:>5s} {r['proj_abs']:>5s} | net {r['net_own']:>5s} {r['net_even']:>5s} {r['net_odd']:>5s}")

print('\n## C. x^2 data fraction: t* = first checkpoint from which circle_wrong stays 0 to step 500')
tstar = {}
for name in sorted(n for n in runs if n.startswith('x2_f')):
    m = re.match(r'x2_f([\d.]+)_H(\d+)_s(\d+)$', name)
    f, H, seed = float(m.group(1)), int(m.group(2)), int(m.group(3))
    c = runs[name].get('curve.csv')
    if not c:
        print(name, 'missing'); continue
    seq = sorted(ints(c, 'circle_wrong'))
    t = None
    for i, (st, v) in enumerate(seq):
        if st >= 1 and all(w == 0 for _, w in seq[i:]):
            t = st; break
    tstar[(f, H, seed)] = (t, dict(seq).get(1), dict(seq).get(500), min(w for st, w in seq if st >= 1), c[-1]['heldout_acc'])
fs = sorted({k[0] for k in tstar}); Hs = sorted({k[1] for k in tstar})
print('t* per seed (circle_wrong at step 1 in brackets; - = never settles at 0 by 500, with the smallest count)')
print('frac   ' + ' | '.join(f'H {H:>4d}' + ' ' * 22 for H in Hs))
for f in fs:
    cells = []
    for H in Hs:
        v = [tstar.get((f, H, s)) for s in range(3)]
        cells.append(', '.join((f"{x[0]}[{x[1]}]" if x[0] is not None else f"-({x[3]})") if x else '?' for x in v))
    print(f"{f:<6} " + ' | '.join(f'{c:28s}' for c in cells))
print('\nwork t* x lr x H where t* >= 2 (t* = 1 only bounds the work from above):')
for f in fs:
    w = [tstar[(f, H, s)][0] * 0.01 * H for H in Hs for s in range(3) if (f, H, s) in tstar and tstar[(f, H, s)][0] and tstar[(f, H, s)][0] >= 2]
    up = [0.01 * H for H in Hs for s in range(3) if (f, H, s) in tstar and tstar[(f, H, s)][0] == 1]
    med = sorted(w)[len(w) // 2] if w else None
    print(f"  frac {f}: unsaturated works {sorted(round(x, 2) for x in w)} median {med}; t* = 1 at lr x H in {sorted(set(up))}")
