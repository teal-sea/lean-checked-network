#!/usr/bin/env python3
"""One production-shaped raw TI site; serial, fail-closed, public Actions only."""
import json
import os
from pathlib import Path
import re
import subprocess
import time

from rawpilot_data import (HERE, PREFIX, ROOT, SUPPORT_NAMES, inventory, sha,
                           validate_generated, verify_pins)
from rawpilot_generate import cloud_only
from row0_receipt import check_axioms
from row0_runner import inherited_warnings
import sync_core

OUT = HERE / 'rawpilot-out'
ANALYTIC = ['Transformer.ExpFix', 'Transformer.Program', 'Transformer.Logits',
            'Transformer.Compose', 'Transformer.Raw']
SUPPORT = 'TransformerBridge.RawPilotSupport'
STEPS = {}


def run(name, args, seconds=300, negative=False):
    print(f'{name} start', flush=True)
    started = time.monotonic()
    output = OUT / (name + '.out')
    with output.open('w') as stream:
        proc = subprocess.run(['/usr/bin/time', '-v', '-o', str(OUT / (name + '.time')),
                               'timeout', '-s', 'TERM', '-k', '10', str(seconds), *args],
                              cwd=HERE, stdout=stream, stderr=subprocess.STDOUT, check=False)
    text = output.read_text()
    item = {'command': args, 'seconds': time.monotonic() - started, 'exit': proc.returncode,
            'time_rss_log': name + '.time'}
    # Persist the exit/status before any diagnostic validation can throw.
    with (OUT / 'steps.jsonl').open('a') as trace:
        trace.write(json.dumps({'name': name, **item}, sort_keys=True) + '\n')
    warnings = inherited_warnings(text)
    (OUT / (name + '-warnings.json')).write_text(json.dumps(warnings, indent=2, sort_keys=True) + '\n')
    if negative:
        if proc.returncode != 1 or not re.search(r'decide[\s\S]*false', text):
            raise ValueError(f'changed production literal was not rejected by kernel decide: {name}\n{text}')
    elif proc.returncode != 0:
        raise ValueError(f'producer failed: {name}, exit {proc.returncode}\n{text}')
    STEPS[name] = item
    print(f'{name} status=OK seconds={item["seconds"]:.3f}', flush=True)
    return text


def build_replay(module):
    run('build_' + module, ['lake', 'build', module], 360)
    object_path = HERE / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    record = {'module': module, 'source_sha256': sha(HERE / (module.replace('.', '/') + '.lean')),
              'olean_sha256': sha(object_path)}
    with (OUT / 'compiled.jsonl').open('a') as trace:
        trace.write(json.dumps(record, sort_keys=True) + '\n')
    run('replay_' + module, ['lake', 'env', 'leanchecker', module], 180)
    if sha(object_path) != record['olean_sha256']:
        raise ValueError('compiled artifact changed during replay: ' + module)
    with (OUT / 'replayed.jsonl').open('a') as trace:
        trace.write(json.dumps(record, sort_keys=True) + '\n')


def audit(label, imports, names):
    if len(names) != len(set(names)):
        raise ValueError('duplicate requested raw-pilot audit declaration')
    path = OUT / (label + '-axioms.lean')
    path.write_text(''.join('import ' + m + '\n' for m in imports) +
                    ''.join('#print axioms ' + n + '\n' for n in names))
    (OUT / (label + '-axioms.expected.json')).write_text(json.dumps(names, indent=2) + '\n')
    text = run(label + '-axioms', ['lake', 'env', 'lean', str(path)], 240)
    count = check_axioms(text, names)
    print(f'{label} exact declarations={count}/{len(names)} standard-axioms-only=YES', flush=True)
    return count


def source_snapshot():
    paths = set(verify_pins())
    paths.update('transformer/mathlib/' + p for p in
                 ('rawpilot.sh', 'rawpilot_data.py', 'rawpilot_generate.py', 'rawpilot_runner.py',
                  'test_rawpilot.py', 'RawPilot-pins.json', 'sync_core.py', 'sync_core.sh',
                  'row0_runner.py', 'row0_receipt.py', 'row0_source.py', 'row0_prefix.py',
                  'TransformerBridge/RawPilotSupport.lean'))
    paths.add('.github/workflows/transformer.yml')
    return {p: sha(ROOT / p) for p in sorted(paths)}


def main():
    cloud_only()
    if OUT.exists():
        raise ValueError('refusing existing raw-pilot receipts or data')
    if (HERE / 'TransformerBridge/RawPilot/Generated').exists():
        raise ValueError('refusing preexisting raw coefficients')
    if list((HERE / '.lake/build/lib/lean/TransformerCore').rglob('*.olean')) or list(
            (HERE / '.lake/build/lib/lean/TransformerBridge').glob('RawPilot*.olean')) or list(
            (HERE / '.lake/build/lib/lean/TransformerBridge/RawPilot').rglob('*.olean')):
        raise ValueError('refusing preexisting raw/core compiled artifacts')
    OUT.mkdir()
    immutable = source_snapshot()
    (OUT / 'sources.json').write_text(json.dumps({
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=HERE, text=True).strip(),
        'sources': immutable, 'scope': 'raw quantized TI h0/j0/tk0, 512 components',
    }, indent=2, sort_keys=True) + '\n')
    version = run('compiler-version', ['lake', 'env', 'lean', '--version'], 60)
    if not re.search(r'version 4\.35\.0(?:,|\))', version):
        raise ValueError('not the pinned stable Lean 4.35.0 compiler')
    lake_version = run('lake-version', ['lake', '--version'], 60)
    prefix = Path(run('compiler-prefix', ['lake', 'env', 'lean', '--print-prefix'], 60).strip()).resolve()
    binaries = {}
    for tool in ('lean', 'lake', 'leanchecker'):
        path = (prefix / 'bin' / tool).resolve()
        binaries[tool] = {'path': str(path), 'sha256': sha(path)}
    (OUT / 'compiler.json').write_text(json.dumps({
        'lean': version, 'lake': lake_version, 'binaries': binaries,
        'toolchain_sha256': sha(HERE / 'lean-toolchain'),
        'lake_manifest_sha256': sha(HERE / 'lake-manifest.json'),
        'lake_manifest': json.loads((HERE / 'lake-manifest.json').read_text()),
        'threads': {k: os.environ.get(k) for k in
                    ('LEAN_NUM_THREADS', 'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS')},
    }, indent=2, sort_keys=True) + '\n')
    # Symbolic support first: no frozen numeric mirrors or learned raw data imports yet.
    run('support-sync', ['./sync_core.sh', '--manifest', 'rawpilot-out/support-sync.tsv'], 60)
    run('support-sync-check', ['./sync_core.sh', '--check'], 60)
    core_support = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in sync_core.inventory()]
    if core_support != ['TransformerCore.Model', 'TransformerCore.Fast', 'TransformerCore.Equiv']:
        raise ValueError('unexpected generic core import closure')
    support_modules = [*core_support, *ANALYTIC, 'TransformerBridge.Bridge', SUPPORT]
    support_text = (HERE / 'TransformerBridge/RawPilotSupport.lean').read_text()
    support_names = ['TransformerBridge.RawPilot.' + n for n in
                     re.findall(r'^(?:def|theorem) (\w+)\b', support_text, re.M)]
    if support_names != SUPPORT_NAMES:
        raise ValueError('exact symbolic support declaration inventory differs')
    scan_paths = [m.replace('.', '/') + '.lean' for m in support_modules]
    run('support-scan', ['../lean/scan_sources.sh', *scan_paths], 60)
    for module in support_modules:
        build_replay(module)
    audit('support', [SUPPORT], SUPPORT_NAMES)
    # Now emit the unchanged frozen tab closure, without bounds/caches/pairs.
    run('frozen-sync', ['./sync_core.sh', '--raw-pilot', '--manifest', 'rawpilot-out/frozen-sync.tsv'], 60)
    run('frozen-sync-check', ['./sync_core.sh', '--raw-pilot', '--check'], 60)
    frozen_rows = sync_core.inventory(raw_pilot=True)
    frozen_modules = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in frozen_rows]
    if len(frozen_modules) != 15 or frozen_modules[-1] != 'TransformerCore.Net.Weights':
        raise ValueError('wrong frozen tab closure')
    run('frozen-scan', ['../lean/scan_sources.sh', *(r[2] for r in frozen_rows)], 60)
    for module in frozen_modules:
        if module not in support_modules:
            build_replay(module)
    run('generate', ['python3', '-W', 'error', 'rawpilot_generate.py'], 180)
    run('generate-repro', ['python3', '-W', 'error', 'rawpilot_generate.py', '--check'], 180)
    receipt = validate_generated(OUT)
    modules, names = inventory()
    if (len(modules), len(names), len(receipt['coefficients'])) != (96, 2842, 11):
        raise ValueError('wrong production pilot inventory')
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    run('generated-scan', ['../lean/scan_sources.sh', *paths, 'rawpilot-out/changed-production-literal.lean'], 60)
    for module in modules:
        build_replay(module)
    # Audit every declared new data definition, stage theorem and final theorem, in order.
    count = audit('production', [PREFIX + '.Site'], [*SUPPORT_NAMES, *names])
    run('negative-changed-production-literal',
        ['lake', 'env', 'lean', 'rawpilot-out/changed-production-literal.lean'], 180, negative=True)
    validate_generated(OUT)
    run('final-frozen-sync-check', ['./sync_core.sh', '--raw-pilot', '--check'], 60)
    if source_snapshot() != immutable:
        raise ValueError('source changed during raw-pilot run')
    all_modules = list(dict.fromkeys([*support_modules, *frozen_modules, *modules]))
    oleans = {m: sha(HERE / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')) for m in all_modules}
    compiled = [json.loads(line) for line in (OUT / 'compiled.jsonl').read_text().splitlines()]
    replayed = [json.loads(line) for line in (OUT / 'replayed.jsonl').read_text().splitlines()]
    if compiled != replayed or [record['module'] for record in replayed] != all_modules or any(
            record['olean_sha256'] != oleans[record['module']] or
            record['source_sha256'] != sha(HERE / (record['module'].replace('.', '/') + '.lean'))
            for record in replayed):
        raise ValueError('final exact compiled/replayed source/object hash inventory differs')
    (OUT / 'accepted-oleans.json').write_text(json.dumps(oleans, indent=2, sort_keys=True) + '\n')
    stages = {}
    for stage, entries in (('V', 32), ('O', 128), ('TI', 512)):
        selected = [m for m in modules if re.fullmatch(re.escape(PREFIX + '.' + stage) + r'\d{3}', m)]
        seconds = sum(STEPS['build_' + m]['seconds'] for m in selected)
        replay = sum(STEPS['replay_' + m]['seconds'] for m in selected)
        stages[stage] = {'entries': entries, 'build_seconds': seconds, 'replay_seconds': replay,
                         'entries_per_build_second': entries / seconds}
    accepted = {'kernel_verdict': 'KERNEL_ACCEPTED', 'scope': receipt['scope'], 'stages': stages,
                'new_declarations_audited': count, 'modules_compiled_and_replayed': len(all_modules),
                'negative_changed_production_literal': 'KERNEL_REJECTED',
                'total_measured_command_seconds': sum(item['seconds'] for item in STEPS.values()),
                'raw_data_build_seconds': sum(STEPS['build_' + m]['seconds'] for m in modules[:modules.index(PREFIX + '.V000')]),
                'full_hT': 'NOT_PROVED', 'fanout_authorization': 'REQUIRES_PARENT_THROUGHPUT_ACCEPTANCE'}
    (OUT / 'throughput.json').write_text(json.dumps(stages, indent=2, sort_keys=True) + '\n')
    (OUT / 'ACCEPTED.json').write_text(json.dumps(accepted, indent=2, sort_keys=True) + '\n')
    print('RAW PILOT KERNEL_ACCEPTED TI=512/512 vvec=32/32 ovec=128/128; full hT NOT_PROVED', flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists():
            (OUT / 'FAILURE.json').write_text(json.dumps({'kernel_verdict': 'NOT_ACCEPTED',
                'error': str(error), 'completed_steps': list(STEPS)}, indent=2) + '\n')
        raise
