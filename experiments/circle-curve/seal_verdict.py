"""Re-derive each seal's verdict from its logs (build.log, leanchecker.*.log, axioms.log, the generated
sources): the same checks seal_cell.py makes, with the axiom report parsed across wrapped lines."""
import json, re, sys, glob, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'sweep'))
from run_one import STANDARD_AXIOMS, FORBIDDEN
for out in sorted(glob.glob(os.path.join(sys.argv[1], '*/'))):
    if not os.path.exists(out + 'build.log'): continue   # e.g. the negative-control directory
    d = json.load(open(out + 'result.json'))
    build = open(out + 'build.log').read()
    build_ok = 'Build completed successfully' in build and not re.search(r"declaration uses [`']sorry", build)
    replays = {f: open(f).read() for f in glob.glob(out + 'leanchecker.*.log')}
    mods = d['stages']['gen']['modules']
    per_mod = d['stages']['replay'].get('modules', {})
    replay_ok = all(os.path.exists(out + f'leanchecker.{m}.log') and os.path.getsize(out + f'leanchecker.{m}.log') == 0 for m in mods) \
        and d['stages']['replay']['ok'] == len(mods) and all(per_mod[m]['exit'] == 0 for m in per_mod)
    # leanchecker prints a message and exits non-zero on any problem, so an empty log plus exit 0 is the pass condition
    log = re.sub(r",\s*\n\s*", ", ", open(out + 'axioms.log').read())
    ax = {}
    for line in log.splitlines():
        mm = re.match(r"'(.+)' depends on axioms: \[(.*)\]", line)
        if mm: ax[mm.group(1)] = [x.strip() for x in mm.group(2).split(',') if x.strip()]
        elif 'does not depend on any axioms' in line: ax[line.split("'")[1]] = []
    expected = [t for ts in d['stages']['gen']['main_theorems'].values() for t in ts]
    missing = [t for t in expected if t not in ax]
    bad = [t for t in expected if t in ax and not set(ax[t]) <= set(STANDARD_AXIOMS)]
    hits = []
    for f in glob.glob(out + 'lean/**/*.lean', recursive=True):
        txt = open(f).read()
        hits += [f"{f}: {w}" for w in FORBIDDEN if w in txt]
    ok = build_ok and replay_ok and not missing and not bad and not hits
    d.setdefault('first_run_ok', d.get('ok')); d['ok'] = ok   # the first run's own verdict is kept as a record
    d['verdict'] = {'ok': ok, 'build_ok': build_ok, 'replay_ok': replay_ok, 'axioms': ax, 'missing_axiom_reports': missing, 'nonstandard_axioms': bad, 'forbidden_hits': hits}
    json.dump(d, open(out + 'result.json', 'w'), indent=1)
    print(os.path.basename(out.rstrip('/')), '| OK' if ok else '| FAIL', '| build', build_ok, '| replay', replay_ok, f"{d['stages']['replay']['ok']}/{len(mods)}", '| axioms', len(expected), 'theorems, missing', missing, 'nonstandard', bad, '| forbidden', hits, '| wrong', {k: v['wrong_count'] for k, v in d['networks'].items()})
