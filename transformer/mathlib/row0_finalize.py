#!/usr/bin/env python3
"""Pinned ROW0 checkpoint finalization, free standard public Actions only.

Restore is an explicitly adjudicated previous compiled/replayed closure, never a
fresh build receipt. Direct Lean compilation prevents Lake from rebuilding old
objects whose analytic Lake traces were not retained. No generation/evaluation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import zipfile

import row0_prefix
import row0_runner as runner
from row0_receipt import check_axioms, sha, validate_codegen
from row0_source import ANALYTIC, check_branches, selected
import sync_core

HERE = Path(__file__).resolve().parent
PIN = HERE / 'row0_checkpoint.json'
PAIRS = [f'TransformerCore.Net.CachedPair0_{b}' for b in range(113)]
FRESH = ['TransformerBridge.Row0Checks', 'TransformerBridge.Row0']
OPTIONAL = ['TransformerBridge.Bounds', 'TransformerBridge.FrozenBounds', 'TransformerBridge.Row0Real']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def stream_sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def archive_index(archive):
    entries = archive.infolist()
    names = [i.filename for i in entries]
    require(len(names) == len(set(names)), 'duplicate archive path')
    for item in entries:
        path = Path(item.filename)
        require(not path.is_absolute() and '..' not in path.parts and '\\' not in item.filename,
                'unsafe archive path')
        require((item.external_attr >> 16) & 0o170000 != 0o120000, 'archive symlink')
    return set(names)


def read_checked(archive, name, expected):
    data = archive.read(name)
    require(digest(data) == expected, 'archive hash mismatch: ' + name)
    return data


def write_new(path, data):
    # Never replace a checkout source or preexisting artifact with different bytes.
    if path.exists():
        require(path.is_file() and path.read_bytes() == data, 'existing path mismatch: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def verify_sources(record, exceptions):
    require(set(exceptions) == {'row0_runner.py', 'row0_source.py', 'test_row0.py',
                                'TransformerBridge/Row0Checks.lean',
                                '../../.github/workflows/transformer.yml'}, 'source exception scope changed')
    for name, old in record['sources'].items():
        expected = old
        if name in exceptions:
            require(exceptions[name]['old_sha256'] == old, 'exception old identity mismatch')
            expected = exceptions[name]['candidate_sha256']
        require(sha(HERE / name) == expected, 'load-bearing/current source mismatch: ' + name)


def verify_steps(text, modules):
    steps = [json.loads(line) for line in text.splitlines()]
    for module in modules:
        for phase, command in [('build_', ['lake', 'build', module]),
                               ('replay_', ['lake', 'env', 'leanchecker', module])]:
            found = [r for r in steps if r.get('name') == phase + module]
            require(bool(found) and all(r.get('exit') == 0 and r.get('command') == command for r in found),
                    'old successful build/replay missing: ' + phase + module)
    failed = [r for r in steps if r.get('name') == 'build_TransformerBridge.Row0Checks']
    require(bool(failed) and all(r.get('exit') == 1 for r in failed),
            'original assembly failure not recorded')


def check_import_closure(modules):
    # Deliberately support only the retained, one-import-per-line source dialect.
    for module in modules:
        source = HERE / (module.replace('.', '/') + '.lean')
        for line in source.read_text().splitlines():
            if re.match(r'^\s*(?:(?:public|private|meta)\s+)?import\b', line):
                require(bool(re.fullmatch(r'import [A-Za-z0-9_.]+', line)),
                        'unsupported retained import syntax: ' + module)
                dep = line[7:]
                require(dep == 'Mathlib' or dep in modules, 'unverified retained import: ' + dep)


def restore(archive_path, metadata_path, pin):
    require(stream_sha(archive_path) == pin['zip_sha256'], 'pinned archive digest mismatch')
    api = json.loads(metadata_path.read_text())
    require(api.get('id') == pin['artifact_id'] and not api.get('expired', True), 'artifact id/expiry mismatch')
    run = api.get('workflow_run', {})
    require(run.get('id') == pin['source_run'] and run.get('head_sha') == pin['source_sha'],
            'artifact source run/commit mismatch')
    require(not list((HERE / '.lake/build/lib/lean/TransformerCore').rglob('*.olean')),
            'preexisting project core objects')
    for root in ('Transformer', 'TransformerBridge'):
        require(not list((HERE / '.lake/build/lib/lean' / root).rglob('*.olean')),
                'preexisting project objects: ' + root)
    with zipfile.ZipFile(archive_path) as archive:
        names = archive_index(archive)
        metadata = {name: read_checked(archive, name, expected)
                    for name, expected in pin['metadata_sha256'].items()}
        record = json.loads(metadata['mathlib/row0-out/prefix/receipt.json'])
        source_record = json.loads(metadata['mathlib/row0-out/source-receipt.json'])
        require(record['source_commit'] == source_record['source_commit'] == pin['source_sha'],
                'retained receipt source commit mismatch')
        require(record['compiler_binary_sha256'] == pin['compiler_binary_sha256'], 'compiler pin mismatch')
        # Strict compiler, manifest, namespace and toolchain checks from existing helper.
        require(all(record.get(k) == v for k, v in row0_prefix.identity().items()),
                'compiler/toolchain/manifest drift')
        core = HERE.parent / 'lean'
        for name in ('manifest.json', 'modules.txt', 'sources.txt', 'axioms.txt'):
            rel = 'lean/ci-out/cache-codegen/' + name
            write_new(core / 'ci-out/cache-codegen' / name, metadata[rel])
        generated = json.loads(metadata['lean/ci-out/cache-codegen/manifest.json'])
        # Recover exact original emitted sources via inverse namespace rename, then
        # validate every original generated hash and all frozen inputs, without emit.
        for rel, expected in generated['outputs'].items():
            require(bool(re.fullmatch(r'Transformer/Net/(?:Cached|CachedPair0_[0-9]+|CachedUnits/[A-Za-z0-9_]+)\.lean', rel)),
                    'out-of-scope generated source path')
            target = rel.replace('Transformer/', 'TransformerCore/', 1)
            data = archive.read('mathlib/' + target)
            original = re.sub(rb'\bTransformerCore\b', b'Transformer', data)
            require(digest(original) == expected, 'original generated source mismatch: ' + rel)
            write_new(core / rel, original)
        receipt = validate_codegen(core)
        require((receipt['vector_count'], receipt['certificate_units']) == (2346, 163), 'packing dimensions changed')
        rows = sync_core.inventory(row0=True)
        require(len(rows) == 328, 'core closure size changed')
        for _, _, dst, _, target in rows:
            require(archive.read('mathlib/' + dst) == target, 'exact core mirror mismatch: ' + dst)
            write_new(HERE / dst, target)
        stable = [m.replace('Transformer', 'TransformerCore', 1) for m, *_ in rows]
        require(stable[-113:] == PAIRS, 'pair closure order mismatch')
        prefix = [*stable[:-113], *ANALYTIC, 'TransformerBridge.Bridge',
                  'TransformerBridge.Pointwise', 'TransformerBridge.Row0Compat']
        require([x['name'] for x in record['modules']] == prefix and len(prefix) == 222,
                'saved prefix module selection changed')
        objects = pin['objects']
        require([x['module'] for x in objects] == prefix + PAIRS, 'pinned object selection changed')
        for item, expected in zip(objects[:222], record['modules']):
            require(item['sha256'] == expected['sha256'] and
                    item['zip_olean'] == 'mathlib/row0-out/prefix/' + expected['olean'],
                    'parent/saved-prefix object mismatch')
        verify_sources(record, pin['source_exceptions'])
        check_branches(HERE / 'TransformerBridge/Row0Checks.lean')
        check_import_closure(set(prefix + PAIRS))
        verify_steps(metadata['mathlib/row0-out/steps.jsonl'].decode(), prefix + PAIRS)
        prefix_names = [n for n in selected(receipt) if n not in
                        ('TransformerBridge.row0_fastCheck', 'TransformerBridge.row0_integer_margin')
                        and '.cached_value_' not in n and '.cached_pilot_' not in n]
        check_axioms(metadata['mathlib/row0-out/prefix-axioms.out'].decode(), prefix_names)
        traces, missing_traces = [], []
        # Stream only explicitly selected objects and their associated Lake outputs.
        # The entire ZIP digest authenticates ancillary traces/hash/ilean bytes.
        for item in objects:
            module = item['module']
            rel = '.lake/build/lib/lean/' + module.replace('.', '/')
            allowed = ('mathlib/row0-out/prefix/' + rel + '.olean'
                       if module in prefix else 'mathlib/' + rel + '.olean')
            require(item['zip_olean'] == allowed, 'pinned object path mismatch: ' + module)
            destination = HERE / (rel + '.olean')
            destination.parent.mkdir(parents=True, exist_ok=True)
            h = hashlib.sha256()
            with archive.open(allowed) as src, destination.open('xb') as dst:
                while chunk := src.read(1024 * 1024):
                    h.update(chunk)
                    dst.write(chunk)
            require(h.hexdigest() == item['sha256'], 'object hash mismatch: ' + module)
            for suffix in ('.trace', '.olean.hash', '.ilean', '.ilean.hash'):
                name = 'mathlib/' + rel + suffix
                if name in names:
                    if suffix == '.trace':
                        traces.append(module)
                    with archive.open(name) as src, (HERE / (rel + suffix)).open('xb') as dst:
                        shutil.copyfileobj(src, dst, 1024 * 1024)
                elif suffix == '.trace':
                    missing_traces.append(module)
        result = {'source_run': pin['source_run'], 'source_sha': pin['source_sha'],
                  'archive_sha256': pin['zip_sha256'], 'prefix_receipt_sha256': pin['prefix_receipt_sha256'],
                  'scope': 'RESTORED_PREVIOUS_COMPILED_REPLAYED; no fresh build claim',
                  'objects': objects, 'restored_traces': traces, 'missing_traces': missing_traces,
                  'source_exceptions': pin['source_exceptions']}
        return result, receipt, record


def fresh_compile(module):
    rel = module.replace('.', '/')
    obj = HERE / '.lake/build/lib/lean' / (rel + '.olean')
    require(not obj.exists(), 'fresh target already compiled: ' + module)
    obj.parent.mkdir(parents=True, exist_ok=True)
    runner.run('fresh_compile_' + module,
               ['lake', 'env', 'lean', '-o', str(obj), rel + '.lean'])
    runner.run('fresh_replay_' + module, ['lake', 'env', 'leanchecker', module])


def main(archive, metadata, real=False):
    require(os.environ.get('GITHUB_ACTIONS') == 'true', 'finalizer runs only in standard public Actions')
    require(os.environ.get('LEAN_NUM_THREADS') in ('1', '2'), 'only 1 or 2 Lean threads')
    pin = json.loads(PIN.read_text())
    runner.OUT = HERE / 'row0-finalize-out'
    require(not runner.OUT.exists(), 'refusing to mix finalizer receipts')
    runner.OUT.mkdir()
    runner.STEPS.clear()
    restored, receipt, record = restore(archive, metadata, pin)
    (runner.OUT / 'restored-previous.json').write_text(json.dumps(restored, indent=2) + '\n')
    (runner.OUT / 'retained-prefix-receipt.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    (runner.OUT / 'generation-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    provenance = {'old_source_commit': pin['source_sha'], 'snapshot_base': pin['snapshot_base'],
                  'new_source_commit': os.environ['GITHUB_SHA'], 'pin_sha256': sha(PIN),
                  'candidate_sources': runner.snapshot_sources(),
                  'finalizer_sha256': sha(Path(__file__))}
    (runner.OUT / 'source-provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    paths = [r[2] for r in sync_core.inventory(row0=True)]
    paths += [m.replace('.', '/') + '.lean' for m in [*ANALYTIC, 'TransformerBridge.Bridge',
              'TransformerBridge.Pointwise', 'TransformerBridge.Row0Compat', *FRESH, *OPTIONAL]]
    runner.scan('finalizer-source-scan', paths)
    red = runner.OUT / 'altered-packing.lean'
    red.write_text('import TransformerCore.Cached\n'
                   'example : TransformerCore.pkI [3, -2, 1] =\n'
                   '    Int.add 4 (Int.mul (Int.ofNat TransformerCore.B)\n'
                   '      (Int.add (-2) (Int.ofNat TransformerCore.B))) := by decide +kernel\n')
    runner.run('negative_altered_packing', ['lake', 'env', 'lean', str(red)], 60, negative=True)
    # Do not replay/rebuild all restored literals: adjudicated old receipt plus exact
    # object hashes authenticate them. Fresh exact full selected audit follows below.
    for module in FRESH:
        fresh_compile(module)
    count = runner.audit('row0-final', ['TransformerCore.CachedFixture', 'TransformerBridge.Row0',
                                     'TransformerBridge.Pointwise'], selected(receipt))
    require(all(f'TransformerCore.Net.Cached.cached_pilot_0_{b}' in selected(receipt)
                and f'TransformerCore.Net.Cached.cached_value_0_{b}' in selected(receipt)
                for b in range(113)), 'final audit omitted a requested pair theorem')
    integer_count = count
    if real:
        from check_bounds_audit import EXPECTED
        for module in OPTIONAL[:2]:
            fresh_compile(module)
        runner.audit('concrete-hb', ['TransformerBridge.FrozenBounds'], list(EXPECTED))
        fresh_compile(OPTIONAL[-1])
        count = runner.audit('row0-final-real', ['TransformerCore.CachedFixture',
                             'TransformerBridge.Row0Real'], selected(receipt, real=True))
    # Acceptance files are written only after all requested stages and final identity checks.
    verify_sources(record, pin['source_exceptions'])
    require(runner.snapshot_sources() == provenance['candidate_sources'], 'source drift during finalization')
    require(all(record.get(k) == v for k, v in row0_prefix.identity().items()), 'final compiler drift')
    validate_codegen(HERE.parent / 'lean')
    require(sha(PIN) == provenance['pin_sha256'] and sha(Path(__file__)) == provenance['finalizer_sha256'],
            'finalizer or checkpoint pin drift')
    for item in restored['objects']:
        require(stream_sha(HERE / '.lake/build/lib/lean' / (item['module'].replace('.', '/') + '.olean'))
                == item['sha256'], 'restored object changed after fresh compile')
    modules = [*FRESH, *(OPTIONAL if real else [])]
    verdict = {'status': 'KERNEL_ACCEPTED', 'scope': 'ROW0/113 integer', 'selected_axioms': integer_count,
               'restored_previous_compiled_replayed': 335, 'fresh_compiled_replayed': modules,
               'fresh_object_sha256': {m: sha(HERE / '.lake/build/lib/lean' /
                                         (m.replace('.', '/') + '.olean')) for m in modules},
               **provenance}
    (runner.OUT / 'INTEGER_ACCEPTED.json').write_text(json.dumps(verdict, indent=2) + '\n')
    if real:
        (runner.OUT / 'MQ_ACCEPTED.json').write_text(json.dumps({**verdict, 'scope': 'ROW0/113 concrete hB/mq', 'selected_axioms': count}, indent=2) + '\n')
    print('ROW0 finalization KERNEL_ACCEPTED; restored previous=335; fresh=' + ','.join(modules), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True, type=Path)
    parser.add_argument('--artifact-metadata', required=True, type=Path)
    parser.add_argument('--with-hb', action='store_true')
    args = parser.parse_args()
    main(args.archive, args.artifact_metadata, args.with_hb)
