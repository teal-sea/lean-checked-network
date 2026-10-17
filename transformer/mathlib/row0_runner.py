#!/usr/bin/env python3
"""Real stable ROW0/113 runner. Invoke only on free public standard Actions.

Every Lean/Lake call is serial in this package. A successful Python/mock test is
not kernel evidence. No original rc2 build, no cache restore, no other input row.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import time

import row0_prefix
from row0_receipt import check_axioms, generator, sha, validate_codegen
from row0_source import ANALYTIC, BASE_AXIOMS, check_branches, selected
import sync_core

HERE = Path(__file__).resolve().parent
OUT = HERE / 'row0-out'
STEPS = {}
RUNNER_SOURCES = [
    'row0.sh', 'row0_runner.py', 'row0_receipt.py', 'row0_source.py', 'row0_prefix.py',
    'test_row0.py', 'test_row0_harness.py', 'sync_core.py', 'sync_core.sh', 'check_bounds_audit.py',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    '../lean/gen_cached.py', '../lean/test_cached.py', '../lean/cached-inputs.sha256',
    '../lean/scan_sources.sh', '../../.github/workflows/transformer.yml',
]


# Exact warning headers observed in accepted stable4.35.0 bounds support logs.
BASELINE_WARNINGS = ('TransformerCore/Equiv.lean:42:69: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:161:15: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:166:15: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:226:30: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:245:28: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:245:28: This simp argument is unused:', 'TransformerCore/Equiv.lean:255:28: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:280:68: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:281:36: This simp argument is unused:', 'TransformerCore/Equiv.lean:321:64: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:322:31: This simp argument is unused:', 'TransformerCore/Equiv.lean:330:15: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:335:17: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'TransformerCore/Equiv.lean:386:13: `Int.ofNat_eq_coe` has been deprecated: Use `Int.ofNat_eq_natCast` instead', 'Transformer/ExpFix.lean: imports `Mathlib` from package `mathlib`, which is designed for use with the module system; consider adding `module` to the start of this file', 'TransformerBridge/Bridge.lean:41:79: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice', 'TransformerBridge/Bridge.lean:41:79: Unused tactic linter: `<;>` should be replaced with `;` or be removed.', 'TransformerBridge/Bridge.lean:48:23: this tactic is never executed', 'TransformerBridge/Bridge.lean:48:43: this tactic is never executed', 'TransformerBridge/Bridge.lean:48:23: Unused tactic linter: `(push_cast; ring)` does nothing.', 'TransformerBridge/Bridge.lean:48:43: Unused tactic linter: `simp` does nothing.', 'TransformerBridge/Bridge.lean:182:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice', 'TransformerBridge/Bridge.lean:182:76: Unused tactic linter: `<;>` should be replaced with `;` or be removed.', 'TransformerBridge/Bridge.lean:249:53: `if_false` has been deprecated: Use `ite_false` instead')
BASELINE_SOURCES = {'TransformerCore/Equiv.lean': ('../lean/Transformer/Equiv.lean', 'fc4d563a67ed0c1a3a1f6f80f63ec377a8e2ba14af972e1b2848e29388ad46ec'), 'Transformer/ExpFix.lean': ('Transformer/ExpFix.lean', 'd35e25e7c19737b7475b8da5a8173727460aea4c302be0caa6101720d89dfd89'), 'TransformerBridge/Bridge.lean': ('TransformerBridge/Bridge.lean', '2d6d65c4b1bbfaacb2147055ca3be29ccee1250edb011df8589250d715103538')}

# Exact headers captured from the successful Raw producer in run 39015147067.
BASELINE_WARNINGS += (
    "Transformer/Raw.lean:173:0: automatically included section variable(s) unused in theorem `Transformer.Weights.rsoftmax_eq`:",
    "Transformer/Raw.lean:181:0: automatically included section variable(s) unused in theorem `Transformer.Weights.resid_dot`:",
)
BASELINE_SOURCES['Transformer/Raw.lean'] = (
    'Transformer/Raw.lean', 'e664331db89a2da6c140dfa4771721eff4b8d6f677149d861b3c8dcfc717ef11')

# Generic cache support and all seven edge fixtures; no frozen numeric declarations.
CACHED_SUPPORT_NAMES = [n for n in BASE_AXIOMS if n.startswith('TransformerCore.')
                        and not n.startswith('TransformerCore.Net.')]


def inherited_warnings(text):
    """Reject every unattributed/unknown warning; bind exceptions to immutable bytes."""
    accepted = []
    for line in text.splitlines():
        if not re.search(r'\bwarning:', line):
            continue
        # Lake prefixes warnings; direct Lean puts the source position first.
        header = line.removeprefix('warning: ')
        if ': warning: ' in header:
            header = header.replace(': warning: ', ': ', 1)
        if header not in BASELINE_WARNINGS:
            raise ValueError(f'unrecognized warning: {line}')
        source = next(path for path in BASELINE_SOURCES if header.startswith(path + ':'))
        original, digest = BASELINE_SOURCES[source]
        data = (HERE / original).read_bytes()
        if sha(HERE / original) != digest:
            raise ValueError(f'warning baseline source changed: {original}')
        expected = re.sub(rb'\bTransformer\b', b'TransformerCore', data) if source.startswith('TransformerCore/') else data
        if (HERE / source).read_bytes() != expected:
            raise ValueError(f'warning baseline mirror changed: {source}')
        accepted.append({'diagnostic': line, 'source': source, 'baseline_source': original,
                         'baseline_sha256': digest, 'source_sha256': sha(HERE / source)})
    return accepted


def run(name, args, seconds=900, negative=False):
    print(f'{name} start', flush=True)
    started = time.monotonic()
    with (OUT / (name + '.out')).open('w') as output:
        proc = subprocess.run(['/usr/bin/time', '-v', '-o', str(OUT / (name + '.time')),
                               'timeout', '-s', 'TERM', '-k', '20', str(seconds), *args],
                              cwd=HERE, stdout=output, stderr=subprocess.STDOUT, check=False)
    elapsed = time.monotonic() - started
    text = (OUT / (name + '.out')).read_text()
    item = {'command': args, 'seconds': elapsed, 'exit': proc.returncode}
    warnings = inherited_warnings(text)
    item['inherited_warnings'] = warnings
    with (OUT / (name + '-warnings.json')).open('w') as receipt:
        json.dump(warnings, receipt, indent=2, sort_keys=True)
        receipt.write('\n')
    with (OUT / 'steps.jsonl').open('a') as trace:
        trace.write(json.dumps({'name': name, **item}, sort_keys=True) + '\n')
    if negative:
        if proc.returncode != 1 or 'decide' not in text or 'false' not in text:
            raise ValueError(f'negative kernel control failed: {name}: {proc.returncode}\n{text}')
    elif proc.returncode:
        raise ValueError(f'{name} failed: {proc.returncode}\n{text}')
    STEPS[name] = item
    print(f'{name} status=OK seconds={elapsed:.3f}', flush=True)
    return text


def build_replay(module):
    run('build_' + module, ['lake', 'build', module])
    run('replay_' + module, ['lake', 'env', 'leanchecker', module])


def scan(name, paths):
    run(name, ['../lean/scan_sources.sh', *map(str, paths)], 60)


def audit(label, imports, names):
    if any(n.startswith('TransformerCore.CachedFixture.') for n in names) and \
            'TransformerCore.CachedFixture' not in imports:
        raise ValueError('fixture axiom audit requires explicit TransformerCore.CachedFixture import')
    if len(names) != len(set(names)):
        raise ValueError('duplicate audit selection')
    path = OUT / (label + '-axioms.lean')
    path.write_text(''.join('import ' + m + '\n' for m in imports) +
                    ''.join('#print axioms ' + n + '\n' for n in names))
    (OUT / (label + '-axioms.expected.json')).write_text(json.dumps(names, indent=2) + '\n')
    text = run(label + '-axioms', ['lake', 'env', 'lean', str(path)], 600)
    count = check_axioms(text, names)
    print(f'{label} exact selected-declarations={count}/{count} status=OK', flush=True)
    return count


def provenance():
    # Checksums only: this does not parse or pack any large vector.
    g = generator()
    g.verify_inputs(HERE.parent / 'lean', HERE.parent / 'lean/cached-inputs.sha256')
    check_branches(HERE / 'TransformerBridge/Row0Checks.lean')
    if (HERE / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0':
        raise ValueError('wrong stable compiler pin')


def snapshot_sources():
    paths = set(RUNNER_SOURCES)
    paths.update('../lean/' + rel for rel in generator().verify_inputs(
        HERE.parent / 'lean', HERE.parent / 'lean/cached-inputs.sha256'))
    paths.update('../lean/' + str(r[1].relative_to(sync_core.BASE)) for r in sync_core.inventory(True))
    paths.update(['../lean/Transformer/Cached.lean', '../lean/Transformer/CachedFixture.lean'])
    paths.update(m.replace('.', '/') + '.lean' for m in ANALYTIC)
    paths.update('TransformerBridge/' + name + '.lean' for name in
                 ('Bridge', 'Bounds', 'FrozenBounds', 'Pointwise', 'Row0Compat', 'Row0Checks', 'Row0', 'Row0Real'))
    return {name: sha(HERE / name) for name in sorted(paths)}


def main(real=False):
    OUT.mkdir(exist_ok=True)
    if (OUT / 'steps.jsonl').exists():
        raise ValueError('refusing to mix receipts with an earlier row0 run')
    provenance()
    immutable = snapshot_sources()
    (OUT / 'source-receipt.json').write_text(json.dumps({
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=HERE, text=True).strip(),
        'scope': 'stable TransformerCore ROW0/113', 'sources': immutable,
    }, indent=2, sort_keys=True) + '\n')
    if list((HERE / '.lake/build/lib/lean/TransformerCore').rglob('*.olean')):
        raise ValueError('unexpected preexisting TransformerCore artifacts; no untrusted restore')
    # Symbolic support must pass before emission/compilation of frozen cache data.
    run('support_sync', ['./sync_core.sh', '--cached-support-only', '--manifest', 'row0-out/support.tsv'], 60)
    run('support_sync_check', ['./sync_core.sh', '--cached-support-only', '--check'], 60)
    support = sync_core.inventory(cached_support=True)
    if len(support) != 6:
        raise ValueError('wrong shared support inventory')
    scan('support_scan', [row[2] for row in support] +
         ['TransformerBridge/Bridge.lean', 'TransformerBridge/Pointwise.lean'])
    for module, *_ in support:
        build_replay(module.replace('Transformer', 'TransformerCore', 1))
    for module in [*ANALYTIC, 'TransformerBridge.Bridge', 'TransformerBridge.Pointwise']:
        build_replay(module)
    audit('cached-support', ['TransformerCore.Cached', 'TransformerCore.CachedFixture'],
          CACHED_SUPPORT_NAMES)
    red = OUT / 'altered-packing.lean'
    red.write_text('import TransformerCore.Cached\n'
                   'example : TransformerCore.pkI [3, -2, 1] =\n'
                   '    Int.add 4 (Int.mul (Int.ofNat TransformerCore.B)\n'
                   '      (Int.add (-2) (Int.ofNat TransformerCore.B))) := by decide +kernel\n')
    run('negative_altered_packing', ['lake', 'env', 'lean', str(red)], 60, negative=True)
    run('codegen', ['python3', '../lean/gen_cached.py', '--out', '../lean', '--row0'], 600)
    run('codegen_repro', ['python3', '../lean/gen_cached.py', '--out', '../lean', '--row0', '--check'], 600)
    receipt = validate_codegen(HERE.parent / 'lean')
    if (receipt['vector_count'], receipt['certificate_units']) != (2346, 163):
        raise ValueError('wrong frozen packing dimensions')
    (OUT / 'generation-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    run('row_sync', ['./sync_core.sh', '--row0', '--manifest', 'row0-out/sync.tsv'], 120)
    run('row_sync_check', ['./sync_core.sh', '--row0', '--check'], 120)
    rows = sync_core.inventory(row0=True)
    if len(rows) != 328:
        raise ValueError(f'wrong ROW0 source inventory: {len(rows)}')
    pairs = [f'TransformerCore.Net.CachedPair0_{b}' for b in range(113)]
    stable = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in rows]
    if stable[-113:] != pairs:
        raise ValueError('literal build inventory is not exactly ordered ROW0/113')
    local_proofs = ['TransformerBridge/Row0Checks.lean', 'TransformerBridge/Row0Compat.lean',
                    'TransformerBridge/Row0.lean', 'TransformerBridge/Pointwise.lean',
                    'TransformerBridge/Row0Real.lean']
    scan('row_scan', [r[2] for r in rows] + local_proofs +
         [m.replace('.', '/') + '.lean' for m in ANALYTIC] + ['TransformerBridge/Bridge.lean'])
    already = {m for m in stable if 'build_' + m in STEPS}
    prefix = stable[:-113]
    for module in prefix:
        if module not in already:
            build_replay(module)
    build_replay('TransformerBridge.Row0Compat')
    prefix_names = [n for n in selected(receipt) if n not in
                    ('TransformerBridge.row0_fastCheck', 'TransformerBridge.row0_integer_margin')
                    and '.cached_value_' not in n and '.cached_pilot_' not in n]
    audit('prefix', ['TransformerCore.CachedFixture', 'TransformerCore.Net.Cached', 'TransformerCore.Net.Table', 'TransformerCore.Net.Cols',
                     'TransformerBridge.Row0Compat', 'TransformerBridge.Pointwise'], prefix_names)
    prefix_modules = [*prefix, *ANALYTIC, 'TransformerBridge.Bridge',
                      'TransformerBridge.Pointwise', 'TransformerBridge.Row0Compat']
    source_paths = {r[2] for r in rows[:-113]}
    source_paths.update('../lean/' + str(r[1].relative_to(sync_core.BASE)) for r in rows[:-113])
    source_paths.update(m.replace('.', '/') + '.lean' for m in prefix_modules if not m.startswith('TransformerCore.'))
    source_paths.update(['../lean/gen_cached.py', '../lean/cached-inputs.sha256', 'sync_core.py',
                         'row0_receipt.py', 'row0_source.py', 'row0_prefix.py', 'row0_runner.py',
                         '../lean/ci-out/cache-codegen/manifest.json', *immutable])
    prefix_hash = row0_prefix.save(OUT / 'prefix', prefix_modules, sorted(source_paths), STEPS)
    print('verified-prefix receipt-sha256=' + prefix_hash, flush=True)
    # The first real stable literal is independently compiled AND replayed before any remaining literal.
    build_replay(pairs[0])
    for module in pairs[1:]:
        build_replay(module)
    build_replay('TransformerBridge.Row0Checks')
    build_replay('TransformerBridge.Row0')
    count = audit('row0', ['TransformerCore.CachedFixture', 'TransformerBridge.Row0', 'TransformerBridge.Pointwise'], selected(receipt))
    provenance()
    if snapshot_sources() != immutable:
        raise ValueError('candidate source changed during ROW0 run')
    validate_codegen(HERE.parent / 'lean')
    run('final_sync_check', ['./sync_core.sh', '--row0', '--check'], 120)
    # The integer verdict is complete independently of the optional concrete hB stage.
    throughput = {'scope': 'ROW0/113', 'pairs': 113, 'namespace': 'TransformerCore',
                  'toolchain': (HERE / 'lean-toolchain').read_text().strip(),
                  'selected_axioms': count, 'prefix_receipt_sha256': prefix_hash,
                  'pair_build_seconds': sum(STEPS['build_' + m]['seconds'] for m in pairs),
                  'pair_replay_seconds': sum(STEPS['replay_' + m]['seconds'] for m in pairs),
                  'pair_timings': {m: {'build': STEPS['build_' + m]['seconds'],
                                      'replay': STEPS['replay_' + m]['seconds']} for m in pairs}}
    throughput['pairs_per_second_build'] = 113 / throughput['pair_build_seconds']
    throughput['pairs_per_second_replay'] = 113 / throughput['pair_replay_seconds']
    (OUT / 'throughput.json').write_text(json.dumps(throughput, indent=2, sort_keys=True) + '\n')
    (OUT / 'INTEGER_ACCEPTED.json').write_text(json.dumps(throughput, indent=2, sort_keys=True) + '\n')
    print('ROW0/113 INTEGER status=KERNEL_ACCEPTED literals=113/113 replayed=113/113 universal=YES', flush=True)
    if real:
        # No assumed hB: these exact concrete sources must compile/replay and pass their audit here.
        scan('hb_scan', ['TransformerBridge/Bounds.lean', 'TransformerBridge/FrozenBounds.lean'])
        from check_bounds_audit import EXPECTED
        for module in ['TransformerBridge.Bounds', 'TransformerBridge.FrozenBounds']:
            build_replay(module)
        audit('concrete-hb', ['TransformerBridge.FrozenBounds'], list(EXPECTED))
        build_replay('TransformerBridge.Row0Real')
        count = audit('row0-real', ['TransformerCore.CachedFixture', 'TransformerBridge.Row0Real'], selected(receipt, real=True))
        (OUT / 'MQ_ACCEPTED.json').write_text(json.dumps({'scope': 'ROW0/113 fused quantized mq',
                                                        'selected_axioms': count}, indent=2) + '\n')
        print('ROW0/113 MQ status=KERNEL_ACCEPTED concrete-hB=REPLAYED argmax=YES', flush=True)
    modules = [*prefix_modules, *pairs, 'TransformerBridge.Row0Checks', 'TransformerBridge.Row0']
    if real:
        modules += ['TransformerBridge.Bounds', 'TransformerBridge.FrozenBounds', 'TransformerBridge.Row0Real']
    final = {m: sha(HERE / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')) for m in modules}
    if snapshot_sources() != immutable:
        raise ValueError('candidate source changed during final optional stage')
    (OUT / 'accepted-oleans.json').write_text(json.dumps(final, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-hb', action='store_true', help='also kernel-check concrete hB and unconditional mq')
    args = parser.parse_args()
    main(args.with_hb)
