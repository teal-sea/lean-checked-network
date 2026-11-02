"""Score the eleventh batch against RULES.md (fixed before the runs; this script after them, before reading
any result). Usage: python3 summarize_batch11.py DIR (run directories with curve_filters.csv, and
seal_inputs/curve_filters.csv from the filt job). Fixed after an independent review and before any result was
read: readings are looked up as their CSV columns (ours -> ours_wrong, ...), and guesses 2 and 3 cover every
run the RULES wording covers (2: every lr 0.01 run at H >= 1024, two-sided; 3: every lr 0.01 run at H >= 2048,
checkpoints to step 100). Fixed after a code review, once the results were known (the verdicts these fixes change
are reported as such in FINDINGS): the runs found are checked against sweeps/batch11.txt (missing, unexpected and
duplicate runs, and seal checks asked for but absent, make the script exit 1); a missing column is an error, not
"never exact"; guess 4 is also scored as its title reads; guess 6 is scored with one constant per reading across
widths, learning rates and seeds, leaving out t* = 1, which is only a floor."""
import csv
import glob
import os
import re
import sys

READ = ('ours', 'ours_float', 'll', 'll_nodc', 'll_int', 'rand', 'min', 'net')
root = sys.argv[1]
BATCH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sweeps', 'batch11.txt')
expected, seal_asked = set(), set()
for line in open(BATCH):
    parts = line.split()
    if len(parts) >= 2 and not parts[0].startswith('#'):
        expected.add(parts[1])
        if 'SEAL_REF=' in line:
            seal_asked.add(parts[1])
runs, seal_rows, dupes = {}, [], []
for f in sorted(glob.glob(os.path.join(root, '**', 'curve_filters.csv'), recursive=True)):
    name = os.path.basename(os.path.dirname(f))
    if name in runs or (name == 'seal_inputs' and seal_rows):
        dupes.append(os.path.relpath(f, root)); continue  # the first one found is kept
    rows = list(csv.DictReader(open(f)))
    if name == 'seal_inputs':
        seal_rows = rows
    else:
        runs[name] = sorted(rows, key=lambda r: int(r['step']))
found = set(runs) | ({'seal_inputs'} if seal_rows else set())
missing, unexpected = sorted(expected - found), sorted(found - expected)
print(f"## runs: {len(found & expected)} of the {len(expected)} in sweeps/batch11.txt found; missing: {missing or 'none'};"
      f" not in the batch: {unexpected or 'none'}; duplicates ignored: {dupes or 'none'}\n")


def val(r, k):
    c = f'{k}_wrong' if k in READ else k
    v = r[c]  # a missing column is an error, never read as "not exact"
    return None if v == '' else int(v)


def tstar(rows, k):
    """First checkpoint >= 1 from which the reading is exact to the last checkpoint."""
    seq = [(int(r['step']), val(r, k)) for r in rows if int(r['step']) >= 1]
    return next((st for i, (st, v) in enumerate(seq) if all(w == 0 for _, w in seq[i:])), None)


def at(rows, step, k):
    r = next((r for r in rows if int(r['step']) == step), None)
    return None if r is None else val(r, k)


def ever(rows, k, last=None):
    return any(val(r, k) == 0 for r in rows if int(r['step']) >= 1 and (last is None or int(r['step']) <= last))


def lr_H(n):
    return float(runs[n][-1]['lr']), int(runs[n][-1]['H'])


def le(a, b):  # t* comparison with None as never
    return (b is None) or (a is not None and a <= b)


def name_of(H, lr, s):
    return f'x2_H{H}_lr{lr}_s{s}'


def fmt(t):
    return '-' if t is None else str(t)


# ---------------------------------------------------------------- tables
groups = {}
for n in runs:
    groups.setdefault(re.sub(r'_s\d+$', '', n), []).append(n)
print('## t* per reading (seeds in order) | wrong at step 1 (seed 0)')
print('group | ' + ' | '.join(READ[:-1]) + ' | step 1 wrong (s0): ' + ' '.join(READ))
for g in sorted(groups):
    names = sorted(groups[g], key=lambda n: int(n.rsplit('_s', 1)[1]))
    cells = [','.join(fmt(tstar(runs[n], k)) for n in names) for k in READ[:-1]]
    s0 = runs[names[0]]
    print(f'{g} | ' + ' | '.join(cells) + ' | ' + ' '.join(fmt(at(s0, 1, k)) for k in READ))

print('\n## agreement of the two rules (agree_q, frozen tables) and neurons sent to DC by ll, at step 1 and at the last checkpoint')
for g in sorted(groups):
    names = sorted(groups[g], key=lambda n: int(n.rsplit('_s', 1)[1]))
    out = []
    for n in names:
        rows = runs[n]
        r1 = next((r for r in rows if int(r['step']) == 1), rows[0]); rl = rows[-1]
        out.append(f"{float(r1['agree_q']):.2f}/{float(rl['agree_q']):.2f} DC {r1['ll_dc']}/{rl['ll_dc']} of {rl['H']}")
    print(f'{g}: ' + ' ; '.join(out))

print('\n## seal reproduction (frozen tables of the rerun equal to the seal input at its step)')
unchecked = []
for n in sorted(seal_asked):
    m = [r['seal_match'] for r in runs.get(n, []) if r.get('seal_match', '') != '']
    if not m:
        unchecked.append(n)
    print(f"{n}: {('reproduced' if all(x == '1' for x in m) else 'DIFFERENT') if m else 'NOT CHECKED'}")

if seal_rows:
    print('\n## the seal inputs themselves (frozen tables): wrong pairs, ll_int against ours, agreement')
    for r in seal_rows:
        print(f"{r['file']}: ll_int {r['ll_int_wrong']} (ties {r['ll_int_ties']}) | ours {r['ours_wrong']} (ties {r['ours_ties']}) | agree {r['agree_q']} | net {r['net_wrong']}")

# ---------------------------------------------------------------- guesses
print('\n## guesses (RULES.md, eleventh batch)')
pairs = (('ours', 'll'), ('ll', 'rand'), ('rand', 'min'))
for a, b in pairs:
    both = [n for n in runs if tstar(runs[n], a) is not None and tstar(runs[n], b) is not None]
    held = [n for n in both if tstar(runs[n], a) <= tstar(runs[n], b)]
    only_b = [n for n in runs if tstar(runs[n], a) is None and tstar(runs[n], b) is not None]
    print(f"1. t*({a}) <= t*({b}): {len(held)} of {len(both)} runs where both are finite"
          f" ({'held' if both and len(held) >= 0.9 * len(both) else 'FAILED' if both else 'no runs'}); {b} finite where {a} is not: {len(only_b)}"
          + (f" {sorted(only_b)}" if only_b else ''))

ok2a = []
for H in (2048, 4096):
    n1 = sum(at(runs.get(name_of(H, '1e-2', s), []), 1, 'll') == 0 for s in range(5))
    ok2a.append(n1 >= 3)
    print(f"2a. ll exact at step 1, H {H}, lr 0.01: {n1} of 5 seeds")
bad2b, na2b = [], []
for n in sorted(runs):
    lr, H = lr_H(n)
    if lr != 0.01 or H < 1024:
        continue
    tl, to = tstar(runs[n], 'll'), tstar(runs[n], 'ours')
    if tl is None and to is None:
        na2b.append(n)
    elif tl is None or to is None or abs(tl - to) > 2:
        bad2b.append(f'{n} (ll {fmt(tl)}, ours {fmt(to)})')
print(f"2. {'held' if all(ok2a) and not bad2b else 'FAILED'} (lr 0.01 runs at H >= 1024 where t*(ll) and t*(ours) differ by more than 2 steps: "
      f"{bad2b or 'none'}; neither finite: {na2b or 'none'})")

r3 = [n for n in runs if lr_H(n)[0] == 0.01 and lr_H(n)[1] >= 2048 and ever(runs[n], 'rand', last=100)]
small = [n for n in runs if int(runs[n][-1]['H']) <= 1024]
m3 = [n for n in small if ever(runs[n], 'min')]
print(f"3. rand exact at some checkpoint (H >= 2048, lr 0.01): {sorted(r3) or 'none'}; min ever exact at H <= 1024: {sorted(m3) or 'none'}"
      f" -> {'held' if r3 and not m3 else 'FAILED'}")

bad4 = [n for n in runs if not le(tstar(runs[n], 'ours_float'), tstar(runs[n], 'ours'))]
bad4b = [n for n in runs if not le(tstar(runs[n], 'll'), tstar(runs[n], 'll_int'))]
print(f"4. as written, t*(ours_float) <= t*(ours) fails in {sorted(bad4) or 'none'}; t*(ll) <= t*(ll_int) fails in {sorted(bad4b) or 'none'}"
      f" -> {'held' if not bad4 and not bad4b else 'FAILED'}")
lose4 = [n for n in runs if not le(tstar(runs[n], 'ours'), tstar(runs[n], 'ours_float'))]
lose4b = [n for n in runs if not le(tstar(runs[n], 'll_int'), tstar(runs[n], 'll'))]
print(f"4. as its title reads (the frozen reading no later than the float one): t*(ours) <= t*(ours_float) fails in "
      f"{len(lose4)} runs {sorted(lose4)}; t*(ll_int) <= t*(ll) fails in {len(lose4b)} runs {sorted(lose4b)}"
      f" -> {'held' if not lose4 and not lose4b else 'FAILED'}")
print("   (the frozen tables are each scaled to 127 and rounded; the float and frozen readings differ by both, and this"
      " batch cannot separate them)")

mem = [f'x2_mem_H512_s{s}' for s in range(5) if f'x2_mem_H512_s{s}' in runs]
ok5 = True
for n in mem:
    rows = runs[n]
    late = [r for r in rows if int(r['step']) >= 100]
    all_exact = all(val(r, 'll') == 0 for r in late)
    worst = max(val(r, 'll') for r in late)
    ag = float(rows[-1]['agree_q']); agf = float(rows[-1]['agree_f'])
    dc = max(int(r['ll_dc']) / int(r['H']) for r in rows)
    ok5 &= all_exact and 0.4 <= ag <= 0.8 and dc < 0.1
    print(f"5. {n}: ll exact at every checkpoint from 100: {all_exact} (worst {worst}); agree_q at 20k {ag:.3f} (agree_f {agf:.3f}); max DC share {dc:.3f}")
print(f"5. {'held' if ok5 and len(mem) == 5 else 'FAILED'}")

print('6. t* x lr x H at lr 0.01, 0.005 and 0.0025, H 1024 and 2048, seeds 0-4, one constant per reading (all values'
      ' within a factor 2?); t* = 1 is a floor and is left out, a reading never exact fails the law')
held6 = {}
for k in ('ours', 'll', 'rand'):
    vals, never, floor, show = [], [], 0, []
    for H in (1024, 2048):
        for lr_s, lr in (('1e-2', 1e-2), ('5e-3', 5e-3), ('2.5e-3', 2.5e-3)):
            for s in range(5):
                n = name_of(H, lr_s, s)
                if n not in runs:
                    continue  # reported as missing above
                t = tstar(runs[n], k)
                if t is None:
                    never.append(n)
                elif t == 1:
                    floor += 1
                else:
                    vals.append(t * lr * H)
    lo, hi = (min(vals), max(vals)) if vals else (float('nan'), float('nan'))
    held6[k] = bool(vals) and not never and hi <= 2 * lo
    print(f"   {k}: {len(vals)} values from {lo:.1f} to {hi:.1f} (factor {hi / lo:.1f}); {floor} at the t* = 1 floor;"
          f" never exact in {len(never)} -> {'held' if held6[k] else 'FAILED'}")
print(f"6. {'held' if held6['ll'] and held6['rand'] else 'FAILED'} (the guess names ll and rand; ours is shown for reference)")

# ---------------------------------------------------------------- win conditions
print('\n## win conditions')
for H in (512, 1024, 2048, 4096):
    n1 = sum(at(runs.get(name_of(H, '1e-2', s), []), 1, 'll') == 0 for s in range(5))
    o1 = sum(at(runs.get(name_of(H, '1e-2', s), []), 1, 'ours') == 0 for s in range(5))
    print(f"H {H}, lr 0.01, step 1 exact: ll {n1} of 5, ours {o1} of 5")
print(f"rand exact anywhere: {sorted(n for n in runs if ever(runs[n], 'rand')) or 'none'}")

problems = ([f'missing runs {missing}'] if missing else []) + ([f'duplicate runs {dupes}'] if dupes else []) \
    + ([f'seal checks asked for but absent {unchecked}'] if unchecked else [])
if problems:
    print('\nINCOMPLETE: ' + '; '.join(problems) + ' (verdicts above may be wrong)')
    sys.exit(1)
