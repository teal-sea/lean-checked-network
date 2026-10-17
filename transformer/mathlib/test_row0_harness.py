"""FAKE runner boundary tests. No Lean/Lake process, no numeric packing or model evaluation."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

import row0_prefix as prefix
import row0_runner as runner
from row0_receipt import generator
import sync_core


def expect_failure(fn):
    try:
        fn()
    except (ValueError, FileNotFoundError):
        return
    raise AssertionError('fake red control passed')


def fixture_receipt():
    # Names/counts only, with no real vector reads or packing/emission.
    g = generator()
    modules, axioms = [], []
    for key, names in [*g.groups().items(), ('Bias', ['CI', 'CU'])]:
        for i in range(0, len(names), g.CHUNK):
            modules.append(f'Transformer.Net.CachedUnits.{key}_{i // g.CHUNK:03d}')
            axioms.extend('Transformer.Net.Cached.eq_' + n for n in names[i:i + g.CHUNK])
        if key != 'Bias':
            modules.append('Transformer.Net.CachedUnits.' + key)
            axioms.append('Transformer.Net.Cached.eq_' + key)
    modules.append('Transformer.Net.Cached')
    axioms.extend('Transformer.Net.Cached.eq_' + n for n in ('TI0', 'TI1', 'TU0', 'TU1'))
    axioms.append('Transformer.Net.Cached.cache_eq')
    for b in range(113):
        axioms.extend((f'Transformer.Net.Cached.cached_value_0_{b}',
                       f'Transformer.Net.Cached.cached_pilot_0_{b}'))
    return {'modules': modules, 'axioms': axioms, 'pairs': [[0, b] for b in range(113)],
            'vector_count': 2346, 'certificate_units': 163}


def exercise(failure='', real=False):
    meta = fixture_receipt()
    old_rows = sync_core.inventory(True)
    support_names = [r[0] for r in sync_core.inventory(cached_support=True)]
    names = [r[0] for r in old_rows] + ['Transformer.Cached', 'Transformer.CachedFixture'] + meta['modules']
    names += [f'Transformer.Net.CachedPair0_{b}' for b in range(113)]
    assert len(names) == 328 and len(set(names)) == 328
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        mathlib, lean = root / 'mathlib', root / 'lean'
        mathlib.mkdir()
        (mathlib / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        lean.mkdir()
        rows = []
        for module in names:
            src = lean / (module.replace('.', '/') + '.lean')
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text('-- FAKE tiny source fixture only\n')
            dst = module.replace('Transformer', 'TransformerCore', 1).replace('.', '/') + '.lean'
            rows.append((module, src, dst, src.read_bytes(), src.read_bytes()))
        support = [next(r for r in rows if r[0] == n) for n in support_names]
        trace, validations = [], []

        def fake_provenance():
            if failure == 'initial-hash' or (failure == 'final-hash' and validations):
                raise ValueError('FAKE provenance control')

        def fake_validate(_):
            validations.append(1)
            if failure == 'missing-middle':
                raise ValueError('FAKE omitted row0_56')
            return meta

        def fake_run(name, args, seconds=900, negative=False):
            trace.append((name, args, negative))
            if name == failure:
                raise ValueError('FAKE failed command')
            if args[0] == 'lake' and args[1] == 'build':
                dest = mathlib / '.lake/build/lib/lean' / (args[2].replace('.', '/') + '.olean')
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(b'FAKE compiled fixture, NOT a Lean object')
            runner.STEPS[name] = {'command': args, 'seconds': 0.001, 'exit': 0}
            if name.endswith('-axioms'):
                expected = json.loads((runner.OUT / (name + '.expected.json')).read_text())
                if failure == 'short-audit' and name == 'row0-axioms':
                    expected = expected[:-1]
                return ''.join(f"'{n}' does not depend on any axioms\n" for n in expected)
            return ''

        def fake_save(dest, modules, sources, steps):
            trace.append(('prefix_saved', modules, False))
            if failure == 'prefix-save':
                raise ValueError('FAKE save failure')
            assert not any('CachedPair' in n for n in modules)
            assert all('build_' + n in steps and 'replay_' + n in steps for n in modules)
            assert sources
            return 'f' * 64

        patches = [patch.object(runner, 'HERE', mathlib), patch.object(runner, 'OUT', mathlib / 'row0-out'),
                   patch.object(runner, 'STEPS', {}), patch.object(runner, 'provenance', fake_provenance),
                   patch.object(runner, 'snapshot_sources', lambda: {'FAKE source': '0' * 64}),
                   patch.object(runner.subprocess, 'check_output', lambda *a, **k: 'FAKE commit\n'),
                   patch.object(runner, 'validate_codegen', fake_validate), patch.object(runner, 'run', fake_run),
                   patch.object(sync_core, 'BASE', lean),
                   patch.object(sync_core, 'inventory', lambda **kw: rows if kw.get('row0') else support),
                   patch.object(prefix, 'save', fake_save)]
        for p in patches:
            p.start()
        try:
            with redirect_stdout(io.StringIO()):
                if failure:
                    expect_failure(lambda: runner.main(real))
                else:
                    runner.main(real)
            labels = [t[0] for t in trace]
            accepted = (runner.OUT / 'INTEGER_ACCEPTED.json').exists()
            assert accepted == (not failure or failure == 'build_TransformerBridge.FrozenBounds'), labels[-5:]
            if not failure:
                points = [f'TransformerCore.Net.CachedPair0_{b}' for b in range(113)]
                builds = [args[2] for _, args, _ in trace if args[:2] == ['lake', 'build']]
                replays = [args[3] for _, args, _ in trace if args[:3] == ['lake', 'env', 'leanchecker']]
                assert [m for m in builds if 'CachedPair' in m] == points
                assert [m for m in replays if 'CachedPair' in m] == points
                first = labels.index('build_' + points[0])
                assert labels.index('replay_' + points[0]) < labels.index('build_' + points[1])
                assert labels.index('prefix_saved') < first
                assert labels.index('build_TransformerBridge.Row0Checks') > labels.index('replay_' + points[-1])
                assert labels.index('build_TransformerBridge.Pointwise') < labels.index('codegen')
                assert labels.index('cached-support-axioms') < labels.index('codegen')
                support_audit = json.loads((runner.OUT / 'cached-support-axioms.expected.json').read_text())
                assert len(support_audit) == 15
                prefix_audit = json.loads((runner.OUT / 'prefix-axioms.expected.json').read_text())
                assert len(prefix_audit) == 2398
                for label in ['cached-support', 'prefix', 'row0', *(['row0-real'] if real else [])]:
                    assert 'import TransformerCore.CachedFixture\n' in (
                        runner.OUT / (label + '-axioms.lean')).read_text()
                for n in support_names:
                    assert labels.index('replay_' + n.replace('Transformer', 'TransformerCore', 1)) < labels.index('codegen')
                assert (runner.OUT / 'MQ_ACCEPTED.json').exists() == real
                if real:
                    assert labels.index('concrete-hb-axioms') < labels.index('build_TransformerBridge.Row0Real')
                evidence = json.loads((runner.OUT / 'throughput.json').read_text())
                assert evidence['pairs'] == 113 and len(evidence['pair_timings']) == 113
                assert set(json.loads((runner.OUT / 'accepted-oleans.json').read_text())) >= set(points)
        finally:
            for p in reversed(patches):
                p.stop()


def command_boundary():
    # Exercise the real run()/audit predicate against FAKE subprocess returns.
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        def invoke(code, text, negative=False):
            def fake_subprocess(args, **kwargs):
                kwargs['stdout'].write(text)
                return subprocess.CompletedProcess(args, code)
            with patch.object(runner, 'OUT', out), patch.object(runner.subprocess, 'run', fake_subprocess):
                return runner.run('fixture', ['FAKE'], negative=negative)
        with redirect_stdout(io.StringIO()):
            invoke(0, 'FAKE success')

            # Real policy, tiny source mirrors, FAKE producer: no Lean invocation.
            baseline = 'TransformerBridge/Bridge.lean'
            original = (runner.HERE / baseline).read_bytes()
            source = out / baseline
            source.parent.mkdir(parents=True)
            source.write_bytes(original)
            warning = next(h for h in runner.BASELINE_WARNINGS if h.startswith(baseline + ':'))
            with patch.object(runner, 'HERE', out):
                invoke(0, 'warning: ' + warning)
                assert json.loads((out / 'fixture-warnings.json').read_text())[0]['source'] == baseline
                invoke(0, warning.replace(': Used ', ': warning: Used ', 1))
                expect_failure(lambda: invoke(1, 'warning: ' + warning))
                expect_failure(lambda: invoke(0, 'warning: TransformerBridge/Row0.lean:1:1: unknown'))
                expect_failure(lambda: invoke(0, 'warning: ' + baseline + ':1:1: new warning'))
                source.write_bytes(original + b'\n')
                expect_failure(lambda: invoke(0, 'warning: ' + warning))

            invoke(1, "error: tactic 'decide' proved false", True)
            for code, text, negative in [(1, 'failed', False), (124, 'timeout', False),
                                         (0, 'warning: fake warning', False), (0, '', True),
                                         (124, 'decide false', True), (1, 'unknown module', True)]:
                expect_failure(lambda: invoke(code, text, negative))


def fixture_import_controls():
    # Real audit policy must reject a missing explicit import before any producer runs.
    with tempfile.TemporaryDirectory() as tmp, patch.object(runner, 'OUT', Path(tmp)):
        name = 'TransformerCore.CachedFixture.empty'
        with patch.object(runner, 'run') as producer:
            expect_failure(lambda: runner.audit('missing-fixture', ['TransformerCore.Cached'], [name]))
            producer.assert_not_called()
        with patch.object(runner, 'run', return_value=f"'{name}' does not depend on any axioms\n"):
            assert runner.audit('explicit-fixture', ['TransformerCore.CachedFixture'], [name]) == 1
            assert (Path(tmp) / 'explicit-fixture-axioms.lean').read_text().startswith(
                'import TransformerCore.CachedFixture\n')


def prefix_controls():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        src = root / 'Source.lean'
        src.write_text('-- fake source\n')
        obj = root / '.lake/build/lib/lean/TransformerCore/Test.olean'
        obj.parent.mkdir(parents=True)
        obj.write_bytes(b'FAKE object')
        ident = {'namespace': 'TransformerCore', 'compiler': 'FAKE stable compiler'}
        with patch.object(prefix, 'HERE', root), patch.object(prefix, 'identity', lambda: ident), \
                patch.object(prefix.subprocess, 'check_output', lambda *a, **k: 'FAKE commit\n'):
            names = ['TransformerCore.Test']
            steps = {'build_TransformerCore.Test': {}, 'replay_TransformerCore.Test': {}}
            dest = root / 'artifact'
            digest = prefix.save(dest, names, ['Source.lean'], steps)
            assert prefix.verify(dest, digest) == 1
            expect_failure(lambda: prefix.verify(dest, '0' * 64))
            src.write_text('-- changed source\n')
            expect_failure(lambda: prefix.verify(dest, digest))
            src.write_text('-- fake source\n')
            target = dest / '.lake/build/lib/lean/TransformerCore/Test.olean'
            target.write_bytes(b'altered')
            expect_failure(lambda: prefix.verify(dest, digest))
            expect_failure(lambda: prefix.save(root / 'missing-replay', names, ['Source.lean'], {}))
            ident['compiler'] = 'FAKE wrong compiler'
            expect_failure(lambda: prefix.verify(dest, digest))


if __name__ == '__main__':
    for failure in ('', 'initial-hash', 'missing-middle', 'build_TransformerCore.Cached',
                    'replay_TransformerCore.CachedFixture', 'cached-support-axioms', 'prefix-axioms', 'prefix-save',
                    'build_TransformerCore.Net.CachedPair0_0', 'replay_TransformerCore.Net.CachedPair0_0',
                    'build_TransformerCore.Net.CachedPair0_56', 'replay_TransformerCore.Net.CachedPair0_56',
                    'build_TransformerBridge.Row0Checks', 'replay_TransformerBridge.Row0Checks',
                    'build_TransformerBridge.Row0', 'row0-axioms', 'short-audit', 'final-hash'):
        exercise(failure)
    exercise(real=True)
    exercise('build_TransformerBridge.FrozenBounds', real=True)
    fixture_import_controls()
    command_boundary()
    prefix_controls()
    print('ok: FAKE ROW0 harness, 20 runner paths plus command/prefix controls; support-first, '
          'first literal build+replay before remaining 112, exact audit, all replays, hB separation, '
          'trusted receipt/source/compiler/olean rejection. NO kernel acceptance evidence.')
