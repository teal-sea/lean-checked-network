#!/usr/bin/env python3
"""One production-shaped raw TI site; serial, fail-closed, public Actions only."""
import json
import os
from pathlib import Path
import re
import subprocess
import time

from rawpacked_data import (HERE, PREFIX, ROOT, SUPPORT_NAMES, inventory, sha,
                           validate_generated, verify_pins)
from rawpacked_generate import cloud_only
from rawpilot_data import SUPPORT_NAMES as SCALAR_SUPPORT_NAMES
from row0_receipt import check_axioms
from row0_runner import inherited_warnings
import sync_core

OUT = HERE / 'rawpacked-out'
ANALYTIC = ['Transformer.ExpFix', 'Transformer.Program', 'Transformer.Logits',
            'Transformer.Compose', 'Transformer.Raw']
SUPPORT = 'TransformerBridge.RawPackedSupport'
FIXTURE = 'TransformerBridge.RawPackedFixture'
FIXTURE_NAMES = ['TransformerBridge.RawPackedFixture.' + n for n in ('carry_collision', 'signed_transport')]
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
    if proc.returncode != 0 and not (negative and proc.returncode == 1 and re.search(r'decide[\s\S]*false', text)):
        raise ValueError(f'producer failed: {name}, exit {proc.returncode}\n{text}')
    warnings = inherited_warnings(text)
    (OUT / (name + '-warnings.json')).write_text(json.dumps(warnings, indent=2, sort_keys=True) + '\n')
    if negative:
        if proc.returncode != 1 or not re.search(r'decide[\s\S]*false', text):
            raise ValueError(f'changed production literal was not rejected by kernel decide: {name}\n{text}')
    STEPS[name] = item
    print(f'{name} status=OK seconds={item["seconds"]:.3f}', flush=True)
    return text


def build_replay(module):
    run('build_' + module, ['lake', 'build', module], 900)
    object_path = HERE / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    record = {'module': module, 'source_sha256': sha(HERE / (module.replace('.', '/') + '.lean')),
              'olean_sha256': sha(object_path)}
    with (OUT / 'compiled.jsonl').open('a') as trace:
        trace.write(json.dumps(record, sort_keys=True) + '\n')
    run('replay_' + module, ['lake', 'env', 'leanchecker', module], 900)
    if sha(object_path) != record['olean_sha256']:
        raise ValueError('compiled artifact changed during replay: ' + module)
    with (OUT / 'replayed.jsonl').open('a') as trace:
        trace.write(json.dumps(record, sort_keys=True) + '\n')


def audit(label, imports, names):
    if len(names) != len(set(names)):
        raise ValueError('duplicate requested raw-packed-pilot audit declaration')
    path = OUT / (label + '-axioms.lean')
    path.write_text(''.join('import ' + m + '\n' for m in imports) +
                    ''.join('#print axioms ' + n + '\n' for n in names))
    (OUT / (label + '-axioms.expected.json')).write_text(json.dumps(names, indent=2) + '\n')
    text = run(label + '-axioms', ['lake', 'env', 'lean', str(path)], 600)
    count = check_axioms(text, names)
    print(f'{label} exact declarations={count}/{len(names)} standard-axioms-only=YES', flush=True)
    return count


def source_snapshot():
    paths = set(verify_pins())
    paths.update('transformer/mathlib/' + p for p in
                 ('rawpacked.sh', 'rawpacked_data.py', 'rawpacked_generate.py', 'rawpacked_runner.py', 'rawpilot_data.py', 'rawpilot_generate.py',
                  'test_rawpacked.py', 'RawPacked-coefficients.json', 'RawPilot-pins.json', 'rawpilot_runner.py', 'TransformerBridge/RawPilotSupport.lean', 'sync_core.py', 'sync_core.sh',
                  'row0_runner.py', 'row0_receipt.py', 'row0_source.py', 'row0_prefix.py',
                  'TransformerBridge/RawPackedSupport.lean', 'TransformerBridge/RawPackedFixture.lean'))
    paths.add('.github/workflows/transformer.yml')
    return {p: sha(ROOT / p) for p in sorted(paths)}


def main():
    cloud_only()
    if OUT.exists():
        raise ValueError('refusing existing raw-packed-pilot receipts or data')
    if (HERE / 'TransformerBridge/RawPacked/Generated').exists():
        raise ValueError('refusing preexisting raw coefficients')
    for project in ('Transformer', 'TransformerCore', 'TransformerBridge'):
        if list((HERE / '.lake/build/lib/lean' / project).rglob('*.olean')) or (
                HERE / '.lake/build/lib/lean' / (project + '.olean')).exists():
            raise ValueError('refusing preexisting project proof objects: ' + project)
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
    run('support-sync', ['./sync_core.sh', '--manifest', 'rawpacked-out/support-sync.tsv'], 60)
    run('support-sync-check', ['./sync_core.sh', '--check'], 60)
    core_support = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in sync_core.inventory()]
    if core_support != ['TransformerCore.Model', 'TransformerCore.Fast', 'TransformerCore.Equiv']:
        raise ValueError('unexpected generic core import closure')
    support_modules = [*core_support, *ANALYTIC, 'TransformerBridge.Bridge', 'TransformerBridge.RawPilotSupport', SUPPORT, FIXTURE]
    support_text = (HERE / 'TransformerBridge/RawPackedSupport.lean').read_text()
    support_names = ['TransformerBridge.RawPacked.' + n for n in
                     re.findall(r'^(?:def|theorem) (\w+)\b', support_text, re.M)]
    fixture_names = ['TransformerBridge.RawPackedFixture.' + n for n in
        re.findall(r'^(?:def|theorem) (\w+)\b', (HERE / 'TransformerBridge/RawPackedFixture.lean').read_text(), re.M)]
    if fixture_names != FIXTURE_NAMES:
        raise ValueError('exact fixture declaration inventory differs')
    if support_names != SUPPORT_NAMES:
        raise ValueError('exact symbolic support declaration inventory differs')
    scan_paths = [m.replace('.', '/') + '.lean' for m in support_modules]
    run('support-scan', ['../lean/scan_sources.sh', *scan_paths], 60)
    for module in support_modules:
        build_replay(module)
    support_count = audit('support', [FIXTURE], [*SCALAR_SUPPORT_NAMES, *SUPPORT_NAMES, *FIXTURE_NAMES])
    # Now emit the unchanged frozen tab closure, without bounds/caches/pairs.
    run('frozen-sync', ['./sync_core.sh', '--raw-pilot', '--manifest', 'rawpacked-out/frozen-sync.tsv'], 60)
    run('frozen-sync-check', ['./sync_core.sh', '--raw-pilot', '--check'], 60)
    frozen_rows = sync_core.inventory(raw_pilot=True)
    frozen_modules = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in frozen_rows]
    if len(frozen_modules) != 15 or frozen_modules[-1] != 'TransformerCore.Net.Weights':
        raise ValueError('wrong frozen tab closure')
    run('frozen-scan', ['../lean/scan_sources.sh', *(r[2] for r in frozen_rows)], 60)
    for module in frozen_modules:
        if module not in support_modules:
            build_replay(module)
    run('generate', ['python3', '-W', 'error', 'rawpacked_generate.py'], 180)
    run('generate-repro', ['python3', '-W', 'error', 'rawpacked_generate.py', '--check'], 180)
    receipt = validate_generated(OUT)
    modules, names = inventory()
    if (len(modules), len(names), len(receipt['coefficients'])) != (194, 2595, 11):
        raise ValueError('wrong production pilot inventory')
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    run('generated-scan', ['../lean/scan_sources.sh', *paths, 'rawpacked-out/changed-production-literal.lean'], 60)
    for module in modules:
        build_replay(module)
    # Audit every declared new data definition, stage theorem and final theorem, in order.
    count = audit('production', [PREFIX + '.Site'], [*SCALAR_SUPPORT_NAMES, *SUPPORT_NAMES, *names])
    run('negative-changed-production-literal',
        ['lake', 'env', 'lean', 'rawpacked-out/changed-production-literal.lean'], 180, negative=True)
    validate_generated(OUT)
    run('final-frozen-sync-check', ['./sync_core.sh', '--raw-pilot', '--check'], 60)
    if source_snapshot() != immutable:
        raise ValueError('source changed during raw-packed-pilot run')
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
    for tool, item in binaries.items():
        if sha(Path(item['path'])) != item['sha256']:
            raise ValueError('compiler binary changed during run: ' + tool)
    stages = {}
    for stage, entries in (('V', 32), ('O', 128)):
        selected = [m for m in modules if re.fullmatch(re.escape(PREFIX + '.' + stage) + r'\d{3}', m)]
        seconds = sum(STEPS['build_' + m]['seconds'] for m in selected)
        replay = sum(STEPS['replay_' + m]['seconds'] for m in selected)
        stages[stage] = {'entries': entries, 'build_seconds': seconds, 'replay_seconds': replay,
                         'entries_per_build_second': entries / seconds}
    def measure(label, chosen, role):
        logs = [OUT / (kind + '_' + m + '.time') for m in chosen for kind in ('build', 'replay')]
        rss = [int(match.group(1)) for path in logs for match in
               re.finditer(r'Maximum resident set size \(kbytes\): (\d+)', path.read_text())]
        if len(rss) != len(logs):
            raise ValueError('missing measured peak RSS for stage ' + label)
        stages[label] = {'role': role, 'modules': chosen,
            'build_seconds': sum(STEPS['build_' + m]['seconds'] for m in chosen),
            'replay_seconds': sum(STEPS['replay_' + m]['seconds'] for m in chosen),
            'max_command_peak_rss_kib': max(rss)}

    raw_modules = [m for m in modules[:modules.index(PREFIX + '.V000')] if m != PREFIX + '.Vectors']
    matrix_modules = [m for m in modules if re.fullmatch(re.escape(PREFIX) + r'\.(Params|Row\d{3}|RowsAll)', m)]
    site_modules = [m for m in modules if re.fullmatch(re.escape(PREFIX) + r'\.(Vectors|V\d{3}|VAll|O\d{3}|OAll|PackedTI|Site)', m)]
    measure('generic_support', support_modules, 'shared symbolic support; before emission')
    measure('frozen_tables', [m for m in frozen_modules if m not in support_modules], 'shared unchanged frozen tables')
    measure('raw_data', raw_modules, 'shared all eleven raw coefficient fields and unchanged Weights interpretation')
    measure('matrix_preprocessing', matrix_modules, 'shared Win row packings and raw coefficient bounds; independent of Ko')
    measure('site_total', site_modules, 'actual site vector witnesses, V32/O128, packed TI512 and assembly; imports included')
    measure('site_packed_TI', [PREFIX + '.PackedTI', PREFIX + '.Site'], 'actual packed certificate, bounds and final 512-output theorem')
    accepted = {'kernel_verdict': 'KERNEL_ACCEPTED', 'scope': receipt['scope'], 'stages': stages,
                'production_declarations_audited': count, 'support_declarations_audited': support_count, 'modules_compiled_and_replayed': len(all_modules),
                'negative_changed_production_literal': 'KERNEL_REJECTED',
                'total_measured_command_seconds': sum(item['seconds'] for item in STEPS.values()),
                'raw_data_build_seconds': stages['raw_data']['build_seconds'],
                'performance_verdict': 'REQUIRES_PARENT_COMPARISON; NO_FANOUT',
                'full_hT': 'NOT_PROVED', 'fanout_authorization': 'REQUIRES_PARENT_THROUGHPUT_ACCEPTANCE'}
    (OUT / 'throughput.json').write_text(json.dumps(stages, indent=2, sort_keys=True) + '\n')
    (OUT / 'ACCEPTED.json').write_text(json.dumps(accepted, indent=2, sort_keys=True) + '\n')
    print('RAW PACKED PILOT KERNEL_ACCEPTED TI=512/512 vvec=32/32 ovec=128/128; full hT NOT_PROVED', flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists():
            (OUT / 'FAILURE.json').write_text(json.dumps({'kernel_verdict': 'NOT_ACCEPTED',
                'error': str(error), 'completed_steps': list(STEPS)}, indent=2) + '\n')
        raise
