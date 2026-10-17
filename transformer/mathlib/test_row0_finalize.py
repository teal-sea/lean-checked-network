"""Tiny fake finalizer controls. No Lean/Lake or frozen packing execution."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
import zipfile

import row0_finalize as f
from row0_receipt import sha
from test_row0_harness import fixture_receipt


def reject(fn):
    try:
        fn()
    except (ValueError, FileNotFoundError, KeyError):
        return
    raise AssertionError('negative fixture accepted')


def source_controls(root):
    root = root / 'policy' / 'mathlib'
    root.mkdir(parents=True)
    paths = {'row0_runner.py', 'row0_source.py', 'test_row0.py', 'TransformerBridge/Row0Checks.lean', '../../.github/workflows/transformer.yml'}
    exceptions = {}
    record = {'sources': {'Model.lean': f.digest(b'-- original theorem source\n')}}
    (root / 'Model.lean').write_bytes(b'-- original theorem source\n')
    for n in paths:
        path = root / n
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b'-- fresh wrapper only\n')
        record['sources'][n] = '0' * 64
        exceptions[n] = {'old_sha256': '0' * 64, 'candidate_sha256': sha(path)}
    with patch.object(f, 'HERE', root):
        f.verify_sources(record, exceptions)
        workflow = '../../.github/workflows/transformer.yml'
        saved = exceptions.pop(workflow)
        reject(lambda: f.verify_sources(record, exceptions))
        exceptions[workflow] = saved
        workflow_path = root / workflow
        workflow_path.write_bytes(b'unknown workflow drift')
        reject(lambda: f.verify_sources(record, exceptions))
        workflow_path.write_bytes(b'-- fresh wrapper only\n')
        (root / 'Model.lean').write_bytes(b'-- changed theorem source\n')
        reject(lambda: f.verify_sources(record, exceptions))
        (root / 'Model.lean').write_bytes(b'-- original theorem source\n')
        exceptions['Model.lean'] = {'old_sha256': record['sources']['Model.lean'], 'candidate_sha256': '0' * 64}
        reject(lambda: f.verify_sources(record, exceptions))


def workflow_controls():
    workflow = (Path(__file__).resolve().parents[2] / '.github/workflows/transformer.yml').read_text()
    assert not (Path(__file__).resolve().parents[2] / '.github/workflows/row0-finalize.yml').exists()
    assert '          - mathlib-row0-finalize' in workflow
    assert "inputs.core_mode == 'mathlib-row0-finalize' && '-mathlib-row0-finalize'" in workflow
    for job in ('mathlib', 'core', 'bridge'):
        route = workflow.split('  ' + job + ':\n', 1)[1].splitlines()[0]
        assert "inputs.core_mode != 'mathlib-row0-finalize'" in route
    restored = workflow.split('\n  row0-finalize:\n', 1)[0].rstrip() + '\n'
    restored = restored.replace('          - mathlib-row0-finalize\n', '')
    restored = restored.replace("inputs.core_mode == 'mathlib-row0-finalize' && '-mathlib-row0-finalize' || ", '')
    restored = restored.replace("inputs.core_mode != 'mathlib-row0-finalize' && ", '')
    assert f.digest(restored.encode()) == 'c5048e0ce8d22b5b418eaec9886709543d4806beb8d0b6702f40189b3ebb558f'
    job = workflow.split('  row0-finalize:\n', 1)[1]
    assert "github.event_name == 'workflow_dispatch' && inputs.core_mode == 'mathlib-row0-finalize' && github.event.repository.private == false" in job
    assert '      contents: read\n      actions: read' in job
    assert job.index('Tiny controls') < job.index('Download exact retained')

workflow_controls()

def archive_controls(root):
    path = root / 'fixture.zip'
    with zipfile.ZipFile(path, 'w') as z:
        z.writestr('mathlib/Test.olean', b'FAKE object')
    with zipfile.ZipFile(path) as z:
        assert f.archive_index(z) == {'mathlib/Test.olean'}
        assert f.read_checked(z, 'mathlib/Test.olean', f.digest(b'FAKE object')) == b'FAKE object'
        reject(lambda: f.read_checked(z, 'mathlib/Test.olean', '0' * 64))
        reject(lambda: f.read_checked(z, 'mathlib/Missing.olean', '0' * 64))
    with zipfile.ZipFile(path, 'w') as z:
        z.writestr('../escape', b'bad')
    with zipfile.ZipFile(path) as z:
        reject(lambda: f.archive_index(z))
    item = zipfile.ZipInfo('symlink')
    item.external_attr = 0o120777 << 16
    with zipfile.ZipFile(path, 'w') as z:
        z.writestr(item, b'target')
    with zipfile.ZipFile(path) as z:
        reject(lambda: f.archive_index(z))
    # Restore must reject archive/source-run/compiler drift BEFORE touching objects.
    pin = {'zip_sha256': '0' * 64}
    reject(lambda: f.restore(path, root / 'missing.json', pin))
    pin = {'zip_sha256': sha(path), 'artifact_id': 7, 'source_run': 8, 'source_sha': 'FAKE'}
    api = root / 'api.json'
    api.write_text(json.dumps({'id': 7, 'expired': False,
                              'workflow_run': {'id': 9, 'head_sha': 'FAKE'}}))
    reject(lambda: f.restore(path, api, pin))


def step_controls():
    module = 'TransformerCore.Fake'
    steps = [{'name': 'build_' + module, 'command': ['lake', 'build', module], 'exit': 0},
             {'name': 'replay_' + module, 'command': ['lake', 'env', 'leanchecker', module], 'exit': 0},
             {'name': 'build_TransformerBridge.Row0Checks', 'exit': 1}]
    encode = lambda: '\n'.join(json.dumps(x) for x in steps)
    f.verify_steps(encode(), [module])
    steps[1]['exit'] = 1
    reject(lambda: f.verify_steps(encode(), [module]))
    steps[1]['exit'] = 0
    steps[1]['command'] = ['echo', 'FAKE successful replay']
    reject(lambda: f.verify_steps(encode(), [module]))
    steps.pop(1)
    reject(lambda: f.verify_steps(encode(), [module]))


def import_controls(root):
    source = root / 'TransformerCore/Fake.lean'
    source.parent.mkdir(exist_ok=True)
    with patch.object(f, 'HERE', root):
        source.write_text('import Mathlib\n')
        f.check_import_closure({'TransformerCore.Fake'})
        for line in ('import TransformerCore.Unverified', ' import Mathlib',
                     'public import Mathlib', 'import Mathlib TransformerCore.Fake'):
            source.write_text(line + '\n')
            reject(lambda: f.check_import_closure({'TransformerCore.Fake'}))


def fresh_controls(root):
    calls = []
    with patch.object(f, 'HERE', root), patch.object(f.runner, 'run', lambda *a, **kw: calls.append((a, kw))):
        f.fresh_compile('TransformerBridge.Row0Checks')
        assert calls[0][0][1][:3] == ['lake', 'env', 'lean']
        assert calls[1][0][1] == ['lake', 'env', 'leanchecker', 'TransformerBridge.Row0Checks']
        assert all('build' not in c[0][1] for c in calls)
        obj = root / '.lake/build/lib/lean/TransformerBridge/Row0Checks.olean'
        obj.write_bytes(b'FAKE preexisting object')
        reject(lambda: f.fresh_compile('TransformerBridge.Row0Checks'))


def main_controls(root, failure='', real=False):
    mathlib = root / ('main-' + (failure or 'green') + str(real))
    mathlib.mkdir()
    pin = mathlib / 'pin.json'
    pin.write_text(json.dumps({'source_sha': 'FAKE_OLD', 'snapshot_base': 'FAKE_BASE', 'source_exceptions': {}}))
    receipt = fixture_receipt()
    restored = {'objects': []}
    record = {'compiler': 'FAKE'}
    events = []
    def fake_run(label, args, *a, **kw):
        events.append(label)
        if failure == label:
            raise ValueError('FAKE failed negative control')
    def fake_compile(module):
        events.append(module)
        if failure == module:
            raise ValueError('FAKE compile/replay failure')
        path = mathlib / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b'FAKE fresh object')
    def fake_audit(label, imports, names):
        events.append(label)
        if failure == label:
            raise ValueError('FAKE incomplete audit')
        assert all(f'TransformerCore.Net.Cached.cached_pilot_0_{b}' in names for b in range(113)) or label == 'concrete-hb'
        return len(names)
    with patch.object(f, 'HERE', mathlib), patch.object(f, 'PIN', pin), \
         patch.dict(f.os.environ, {'GITHUB_ACTIONS': 'true', 'LEAN_NUM_THREADS': '2', 'GITHUB_SHA': 'FAKE_NEW'}), \
         patch.object(f, 'restore', return_value=(restored, receipt, record)), \
         patch.object(f.runner, 'snapshot_sources', return_value={'FAKE': 'HASH'}), \
         patch.object(f.sync_core, 'inventory', return_value=[]), \
         patch.object(f.runner, 'scan'), patch.object(f.runner, 'run', fake_run), \
         patch.object(f, 'fresh_compile', fake_compile), patch.object(f.runner, 'audit', fake_audit), \
         patch.object(f, 'verify_sources'), patch.object(f.row0_prefix, 'identity', return_value=record), \
         patch.object(f, 'validate_codegen'):
        with redirect_stdout(io.StringIO()):
            if failure:
                reject(lambda: f.main(root / 'FAKE.zip', root / 'FAKE.json', real))
            else:
                f.main(root / 'FAKE.zip', root / 'FAKE.json', real)
        out = mathlib / 'row0-finalize-out'
        assert (out / 'INTEGER_ACCEPTED.json').exists() == (not failure)
        assert (out / 'MQ_ACCEPTED.json').exists() == (not failure and real)
        if not failure:
            assert events.index('row0-final') > events.index('TransformerBridge.Row0')
            assert events.index('negative_altered_packing') < events.index('TransformerBridge.Row0Checks')
            verdict = json.loads((out / 'INTEGER_ACCEPTED.json').read_text())
            assert verdict['restored_previous_compiled_replayed'] == 335
            assert verdict['new_source_commit'] == 'FAKE_NEW'
            if real:
                assert events.index('concrete-hb') < events.index('TransformerBridge.Row0Real')


def restore_fixture(parent, fault=''):
    # Full *named* 335-object topology, each object/source just a few fake bytes.
    # Exercises the real restore function; only compiler identity and generator
    # validation are fake. No Lean process or numeric source generation occurs.
    root = parent / ('restore-' + (fault or 'green'))
    mathlib, core = root / 'mathlib', root / 'lean'
    mathlib.mkdir(parents=True)
    core.mkdir()
    template = json.loads(f.PIN.read_text())
    module_names = [x['module'] for x in template['objects']]
    prefix = module_names[:222]
    core_names = [m for m in module_names if m.startswith('TransformerCore.')]
    rows, members, source_hashes = [], {}, {}
    original = b'-- tiny FAKE Transformer source; NO kernel evidence\n'
    target = original.replace(b'Transformer', b'TransformerCore')
    generated = fixture_receipt()
    generated['outputs'] = {}
    for module in core_names:
        rel = module.replace('.', '/') + '.lean'
        oldrel = rel.replace('TransformerCore/', 'Transformer/', 1)
        source = core / oldrel
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(original)
        rows.append((module.replace('TransformerCore', 'Transformer', 1), source, rel, original, target))
        members['mathlib/' + rel] = target
        source_hashes[rel] = f.digest(target)
        source_hashes['../lean/' + oldrel] = f.digest(original)
        if oldrel.startswith('Transformer/Net/Cached'):
            generated['outputs'][oldrel] = f.digest(original)
    for module in prefix:
        if not module.startswith('TransformerCore.'):
            rel = module.replace('.', '/') + '.lean'
            file = mathlib / rel
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(original)
            source_hashes[rel] = f.digest(original)
    exceptions = {}
    for rel in ('row0_runner.py', 'row0_source.py', 'test_row0.py', 'TransformerBridge/Row0Checks.lean', '../../.github/workflows/transformer.yml'):
        path = mathlib / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(original)
        source_hashes[rel] = f.digest(original)
        exceptions[rel] = {'old_sha256': f.digest(original), 'candidate_sha256': f.digest(original)}
    objects, saved = [], []
    for module in module_names:
        rel = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
        name = 'mathlib/row0-out/prefix/' + rel if module in prefix else 'mathlib/' + rel
        data = ('FAKE object: ' + module).encode()
        objects.append({'module': module, 'zip_olean': name, 'sha256': f.digest(data)})
        members[name] = data
        if module in prefix:
            saved.append({'name': module, 'olean': rel, 'sha256': f.digest(data)})
    compiler = {'compiler': 'FAKE stable compiler', 'compiler_binary_sha256': 'FAKE_BINARY'}
    record = {**compiler, 'source_commit': 'FAKE_OLD', 'modules': saved, 'sources': source_hashes}
    steps = []
    for module in module_names:
        steps += [{'name': 'build_' + module, 'command': ['lake', 'build', module], 'exit': 0},
                  {'name': 'replay_' + module, 'command': ['lake', 'env', 'leanchecker', module], 'exit': 0}]
    steps.append({'name': 'build_TransformerBridge.Row0Checks', 'exit': 1})
    names = [n for n in f.selected(generated) if n not in
             ('TransformerBridge.row0_fastCheck', 'TransformerBridge.row0_integer_margin')
             and '.cached_value_' not in n and '.cached_pilot_' not in n]
    metadata = {
        'mathlib/row0-out/prefix/receipt.json': json.dumps(record).encode(),
        'mathlib/row0-out/source-receipt.json': json.dumps({'source_commit': 'FAKE_OLD'}).encode(),
        'mathlib/row0-out/steps.jsonl': '\n'.join(json.dumps(x) for x in steps).encode(),
        'mathlib/row0-out/prefix-axioms.out': ''.join(f"'{n}' does not depend on any axioms\n" for n in names).encode(),
        'lean/ci-out/cache-codegen/manifest.json': json.dumps(generated).encode(),
        **{'lean/ci-out/cache-codegen/' + n: b'FAKE metadata\n' for n in ('modules.txt', 'sources.txt', 'axioms.txt')},
    }
    pin = {'artifact_id': 7, 'source_run': 8, 'source_sha': 'FAKE_OLD',
           'compiler_binary_sha256': 'FAKE_BINARY', 'source_exceptions': exceptions,
           'prefix_receipt_sha256': f.digest(metadata['mathlib/row0-out/prefix/receipt.json']),
           'objects': objects, 'metadata_sha256': {n: f.digest(d) for n, d in metadata.items()}}
    members.update(metadata)
    if fault == 'tampered-object':
        members[objects[278]['zip_olean']] = b'FAKE tampered middle literal'
    if fault == 'missing-object':
        del members[objects[278]['zip_olean']]
    if fault == 'changed-generated-source':
        rel = next(iter(generated['outputs'])).replace('Transformer/', 'TransformerCore/', 1)
        members['mathlib/' + rel] += b'-- changed\n'
    archive = root / 'tiny.zip'
    with zipfile.ZipFile(archive, 'w') as z:
        for name, data in members.items():
            z.writestr(name, data)
    pin['zip_sha256'] = sha(archive)
    api = root / 'api.json'
    api.write_text(json.dumps({'id': 7, 'expired': False, 'workflow_run': {'id': 8, 'head_sha': 'FAKE_OLD'}}))
    if fault == 'compiler-drift':
        compiler = {**compiler, 'compiler': 'FAKE wrong compiler'}
    if fault == 'source-drift':
        (mathlib / 'Transformer/Compose.lean').write_bytes(b'FAKE changed theorem source')
    with patch.object(f, 'HERE', mathlib), patch.object(f.sync_core, 'inventory', return_value=rows), \
         patch.object(f, 'validate_codegen', return_value=generated), \
         patch.object(f.row0_prefix, 'identity', return_value=compiler), \
         patch.object(f, 'check_branches'):
        if fault:
            reject(lambda: f.restore(archive, api, pin))
        else:
            restored, _, _ = f.restore(archive, api, pin)
            assert len(restored['objects']) == 335
            assert restored['scope'].startswith('RESTORED_PREVIOUS')
            assert len(restored['missing_traces']) == 335
            for obj in objects:
                assert sha(mathlib / '.lake/build/lib/lean' /
                           (obj['module'].replace('.', '/') + '.olean')) == obj['sha256']


def main():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for fault in ('', 'tampered-object', 'missing-object', 'changed-generated-source',
                      'compiler-drift', 'source-drift'):
            restore_fixture(root, fault)
        source_controls(root)
        archive_controls(root)
        step_controls()
        import_controls(root)
        fresh_controls(root)
        for failure in ('', 'negative_altered_packing', 'TransformerBridge.Row0Checks',
                        'TransformerBridge.Row0', 'row0-final'):
            main_controls(root, failure)
        main_controls(root, real=True)
        for failure in ('TransformerBridge.Bounds', 'TransformerBridge.FrozenBounds',
                        'concrete-hb', 'TransformerBridge.Row0Real', 'row0-final-real'):
            main_controls(root, failure, real=True)
    print('ok: tiny FAKE finalizer source/archive/import/old-exit/fresh-target controls and '
          '11 acceptance paths; real restore boundary with 335 tiny fake objects and five red cases. NO kernel evidence.')


if __name__ == '__main__':
    main()
