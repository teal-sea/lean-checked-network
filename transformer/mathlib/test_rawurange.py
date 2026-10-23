#!/usr/bin/env python3
"""Source/toy/mock and actual retained metadata checks; never kernel evidence."""
import argparse
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch
import zipfile
import rawurange_generate as gen
import rawurange_restore as cache
import rawurange_runner as runner

PACKED = CI = ROW0 = ROW127 = None


class RangeTests(unittest.TestCase):
    def test_actual_four_archive_metadata_and_strict_reds(self):
        base = cache.base; boundary = cache.boundary
        records, source, _ = base.old.validate_metadata(PACKED, json.loads(base.old.PIN_PATH.read_text()))
        base.verify_sources(source)
        self.assertEqual(len(records), 218)
        ci = base.validate_ci(CI); r0 = boundary.validate_row0(ROW0); r127 = cache.validate_row127(ROW127)
        self.assertEqual(len(records + ci + r0 + r127), 230)
        self.assertEqual(len({r['module'] for r in records + ci + r0 + r127}), 230)
        mutations = [('compiled.jsonl', ROW127['compiled.jsonl'] * 2), ('replayed.jsonl', ''),
                     ('negative-actual-U127-change.out', 'error: unknown identifier'),
                     ('row127-axioms.out', ROW127['row127-axioms.out'].replace('propext', 'sorryAx')),
                     ('complete-U-row127-axioms.out', ROW127['complete-U-row127-axioms.out'] + 'garbage\n')]
        for field, value in [('scope', gen.scope(1, 4)), ('fresh_compiled_replayed', []), ('restored_objects', []),
                             ('compiler_binary_sha256', {}), ('exact_production_audit_names', 2654), ('negative_actual_U127_change', 'EXIT0')]:
            record = json.loads(ROW127['U_ROW127_ACCEPTED.json']); record[field] = value
            mutations.append(('U_ROW127_ACCEPTED.json', json.dumps(record)))
        steps = [json.loads(s) for s in ROW127['steps.jsonl'].splitlines()]
        for kind in ('compile', 'replay', 'audit exit', 'negative exit0', 'negative timeout', 'missing', 'duplicate'):
            bad = copy.deepcopy(steps)
            if kind == 'compile': next(s for s in bad if s['name'].startswith('fresh_compile_'))['command'][2] = 'fake'
            elif kind == 'replay': next(s for s in bad if s['name'].startswith('fresh_replay_'))['exit'] = 1
            elif kind == 'audit exit': next(s for s in bad if s['name'] == 'row127-axioms')['exit'] = 1
            elif kind == 'negative exit0': bad[-1]['exit'] = 0
            elif kind == 'negative timeout': bad[-1]['exit'] = 124
            elif kind == 'missing': bad = bad[:-1]
            else: bad.append(bad[-1])
            mutations.append(('steps.jsonl', '\n'.join(json.dumps(s) for s in bad)))
        for name, value in mutations:
            with self.subTest(name=name):
                data = dict(ROW127); data[name] = value
                with self.assertRaises(ValueError): cache.validate_row127(data)

    def test_bounded_selection_before_production(self):
        self.assertEqual(gen.rows_for(1, 4), [1, 2, 3, 4])
        self.assertEqual(gen.rows_for(123, 4), [123, 124, 125, 126])
        for start, count in [(0, 1), (127, 1), (1, 0), (1, 5), (124, 4), (-1, 1), (True, 1), (1, True), ('1', 4), (1.0, 4)]:
            with self.subTest(start=start, count=count), patch.object(gen, 'cloud_only') as guard:
                with self.assertRaises(ValueError): gen.production_rows(start, count)
                guard.assert_not_called()
            with patch.object(runner, 'cloud_only') as guard, self.assertRaises(ValueError):
                runner.main(None, None, None, None, None, None, None, None, start, count)
            guard.assert_not_called()
        with patch.dict(os.environ, {}, clear=True), self.assertRaises(ValueError): gen.production_rows(1, 4)

    def test_toy_four_rows_one_module_independent_bounds_and_negative(self):
        values = {r: [-r, 2] + [0] * 111 for r in range(1, 5)}  # Toy only, never original U numerics.
        sources, negative = gen.batch_sources(1, 4, values)
        modules, row_names, control_names = gen.inventory(1, 4)
        self.assertEqual(list(sources), modules); self.assertEqual(len(modules), 2)
        self.assertEqual(len(row_names), 12); self.assertEqual(len(control_names), 2)
        text = sources[modules[0]]
        for r in range(1, 5):
            self.assertIn(f'theorem urow_cert_{r:03d} : pack (weights.U {r}) = packedURow_{r:03d} ∧', text)
            self.assertIn(f'∀ k : Fin 113, -(KU_{r:03d} : Int) ≤ weights.U {r} k ∧ weights.U {r} k ≤ KU_{r:03d}', text)
        self.assertEqual(text.count('decide +kernel'), 4)
        self.assertIn('d = 1 ∧ k = 0 then weights.U d k + 1 else weights.U d k', sources[modules[1]])
        self.assertIn('changedWeights_001.U 1 0 = weights.U 1 0 + 1 := by\n  rfl', sources[modules[1]])
        self.assertIn('pack (changedWeights_001.U 1) = packedURow_001 := by\n  decide +kernel', negative)
        self.assertNotIn('if_pos', '\n'.join(sources.values()))
        declarations = [gen.NS + '.' + n for s in sources.values() for n in re.findall(r'^(?:def|theorem) (\w+)', s, re.M)]
        self.assertEqual(declarations, row_names + control_names)
        for bad in ({}, {True: values[1], 2: values[2], 3: values[3], 4: values[4]}, {1: values[1]}, dict(reversed(list(values.items()))), {**values, 5: values[1]}, {1: values[1], 2: values[2], 4: values[4], 5: values[1]}, {**values, 2: [0] * 112}):
            with self.assertRaises(ValueError): gen.batch_sources(1, 4, bad)
        with tempfile.TemporaryDirectory() as tmp:
            here = Path(tmp); out = here / 'out'; out.mkdir()
            with patch.object(gen, 'HERE', here), patch.object(gen, 'cloud_only'), patch.object(gen, 'production_rows', return_value=(values, {})):
                record = gen.emit(out, 1, 4); gen.emit(out, 1, 4, check=True)
                self.assertEqual(record['scope']['U_rows'], [1, 2, 3, 4]); self.assertEqual(record['negative']['coordinate'], [1, 0])
                for field, bad in [('scope', gen.scope(1, 3)), ('modules', modules * 2), ('declarations', row_names[:-1])]:
                    (out / 'generation.json').write_text(json.dumps({**record, field: bad}))
                    with self.assertRaises(ValueError): gen.emit(out, 1, 4, check=True)
                (out / 'generation.json').write_text(json.dumps(record))
                (here / gen.PREFIX.replace('.', '/') / 'Rows005_008.lean').write_text('-- extra mock module')
                with self.assertRaises(ValueError): gen.emit(out, 1, 4, check=True)

    def test_layered_inverses_current_sources_and_policy(self):
        workflow = (cache.ROOT / '.github/workflows/transformer.yml').read_text()
        accepted = cache.inverse_workflow(workflow)
        self.assertEqual(cache.digest(accepted.encode()), cache.boundary.pin()['workflow_projection']['current_sha256'])
        self.assertEqual(cache.digest(cache.boundary.inverse_workflow(workflow).encode()), cache.boundary.pin()['workflow_projection']['accepted_sha256'])
        for bad in (workflow + '# unknown\n', workflow.replace('mathlib-raw-u-range', 'arbitrary', 1)):
            with self.assertRaises(ValueError): cache.inverse_workflow(bad)
        cache.verify_candidate(json.loads(ROW127['U_ROW127_ACCEPTED.json'])['candidate'])
        for path, rule in cache.pin()['nonproof_projections'].items():
            raw = (cache.ROOT / path).read_bytes()
            self.assertEqual(cache.digest(cache.project_current(path, raw)), rule['accepted_sha256'])
            with self.assertRaises(ValueError): cache.project_current(path, raw + b' ')
        policy = json.loads((cache.HERE / 'input_policy.json').read_text())
        for path, expected in policy['sources'].items(): self.assertEqual(cache.sha(cache.HERE / path), expected)
        job = workflow[workflow.index('  raw-u-range:\n'):workflow.index('  raw-u-boundary:\n')]
        self.assertNotIn('matrix:', job); self.assertIn('u_row_start', job); self.assertIn('u_row_count', job)
        for artifact in ('12100029309', '12126011262', '12126625308', '12126766253'): self.assertIn(artifact, job)

    def test_API_import_overlap_object_and_compiler_errors(self):
        lock = cache.pin()['row127']; api = {'id': lock['artifact_id'], 'expired': False, 'workflow_run': {'id': lock['source_run'], 'head_sha': lock['source_sha']}}
        cache.base.api_identity(api, lock)
        for bad in ({**api, 'id': 0}, {**api, 'expired': True}, {**api, 'workflow_run': {}}, {**api, 'workflow_run': {'id': lock['source_run'], 'head_sha': 'wrong'}}):
            with self.assertRaises(ValueError): cache.base.api_identity(bad, lock)
        for source in (b'import Unknown\n', b'public import Mathlib\n', b'import Mathlib; axiom bad : False\n'):
            with self.assertRaises(ValueError): cache.base.check_imports(source, set())
        def archive(value):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, 'w') as z: z.writestr('same', value)
            stream.seek(0); return zipfile.ZipFile(stream)
        with archive(b'a') as a, archive(b'a') as b, archive(b'a') as c, archive(b'bad') as d:
            cache.boundary.check_overlaps([a, b, c])
            with self.assertRaises(ValueError): cache.boundary.check_overlaps([a, b, c, d])
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / 'object'; cache.base.restore_object(a, 'same', path, cache.digest(b'a'))
                with self.assertRaises(ValueError): cache.base.restore_object(d, 'same', Path(tmp) / 'bad', cache.digest(b'a'))
                with self.assertRaises(FileExistsError): cache.base.restore_object(a, 'same', path, cache.digest(b'a'))
        with patch.object(cache, 'cloud_only'), patch.object(cache, 'sha', return_value='drift'), self.assertRaises(ValueError):
            cache.restore(None, None, None, None, None, None, None, None, {})

    def test_strict_audit_full_output_and_nonzero_producer(self):
        common = runner.common; names = ['Mock.a', 'Mock.b']
        good = "'Mock.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Mock.b' does not depend on any axioms\n"
        self.assertEqual(common.check_correspondence_axioms(good, names), 2)
        for bad in ('', good + 'garbage', 'warning: bad\n' + good, good.replace('propext', 'sorryAx'), good.replace(',\n ', ',\n error\n '), good * 2, good + "'truncated' depends on axioms: ["):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(bad, names)
        for wrong in (names[::-1], names * 2, names[:-1]):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(good, wrong)
        with tempfile.TemporaryDirectory() as tmp, patch.object(common, 'OUT', Path(tmp)), patch.object(common.runner, 'run', side_effect=ValueError('producer exit1')):
            with self.assertRaisesRegex(ValueError, 'exit1'): runner.audit('mock', ['Mock'], names)

    def test_mocked_one_batch_orchestrator_non_kernel(self):
        common = runner.common
        for failure in (None, 'compile', 'replay', 'audit', 'negative exit0', 'negative syntax', 'negative timeout'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as tmp, contextlib.ExitStack() as stack:
                here = Path(tmp); out = here / 'rawurange-out'
                stack.enter_context(patch.dict(os.environ, {'GITHUB_REPOSITORY': 'teal-sea/lean-checked-network', 'LEAN_NUM_THREADS': '2'}))
                for module in (runner, common, gen): stack.enter_context(patch.object(module, 'HERE', here))
                stack.enter_context(patch.object(runner, 'OUT', out)); stack.enter_context(patch.object(runner, 'cloud_only'))
                stack.enter_context(patch.object(runner, 'snapshot', return_value={})); stack.enter_context(patch.object(cache, 'restore', return_value={'objects': []}))
                stack.enter_context(patch.object(cache, 'PIN_PATH', here / 'pin.json')); (here / 'pin.json').write_text('FAKE')
                for n in ('lean', 'lake', 'leanchecker'):
                    path = here / 'bin' / n; path.parent.mkdir(exist_ok=True); path.write_bytes(b'FAKE executable never run')
                stack.enter_context(patch.object(cache, 'pin', return_value={'compiler_binary_sha256': {n: cache.sha(here / 'bin' / n) for n in ('lean', 'lake', 'leanchecker')}}))
                values = {r: [0] * 113 for r in range(1, 5)}; sources, negative = gen.batch_sources(1, 4, values)
                def emit(folder, start, count, check=False):
                    self.assertEqual((start, count), (1, 4))
                    for m, text in sources.items():
                        path = here / (m.replace('.', '/') + '.lean'); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
                    (folder / 'changed-U-range.lean').write_text(negative); return {'scope': gen.scope(start, count)}
                stack.enter_context(patch.object(gen, 'emit', side_effect=emit))
                compiled = []
                def run(label, args, seconds=300, negative=False):
                    if label == 'compiler-version': return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                    if label == 'compiler-prefix': return str(here)
                    if failure == 'compile' and label.startswith('fresh_compile_'): raise ValueError('FAKE compile exit1')
                    if failure == 'replay' and label.startswith('fresh_replay_'): raise ValueError('FAKE replay exit1')
                    if failure and failure.startswith('negative') and negative: raise ValueError('FAKE control ' + failure)
                    common.runner.STEPS[label] = {'seconds': 0.01}; (out / (label + '.time')).write_text('Maximum resident set size (kbytes): 12\n')
                    if label.startswith('fresh_compile_'): Path(args[4]).write_bytes(b'FAKE object, not kernel evidence'); compiled.append(label)
                    return ''
                stack.enter_context(patch.object(common.runner, 'run', side_effect=run))
                if failure == 'audit': stack.enter_context(patch.object(runner, 'audit', side_effect=ValueError('FAKE warning')))
                else: stack.enter_context(patch.object(runner, 'audit', side_effect=lambda label, imports, requested: len(requested)))
                if failure is None:
                    runner.main(None, None, None, None, None, None, None, None, 1, 4)
                    accepted = json.loads((out / 'U_RANGE_ACCEPTED.json').read_text())
                    self.assertEqual(accepted['scope'], gen.scope(1, 4)); self.assertEqual(len(compiled), 2)
                    self.assertEqual(accepted['exact_production_audit_names'], 2669)
                else:
                    with self.assertRaises(ValueError): runner.main(None, None, None, None, None, None, None, None, 1, 4)
                    self.assertFalse((out / 'U_RANGE_ACCEPTED.json').exists())
                self.assertFalse((here / gen.PREFIX.replace('.', '/') / 'Rows005_008.lean').exists())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('ci-archive', 'row0-archive', 'row127-archive'): parser.add_argument('--' + name, type=Path, required=True)
    group = parser.add_mutually_exclusive_group(required=True); group.add_argument('--packed-archive', type=Path); group.add_argument('--metadata-dir', type=Path)
    args = parser.parse_args(); packed_pin = json.loads(cache.base.old.PIN_PATH.read_text())
    if args.packed_archive:
        cache.require(cache.stream_sha(args.packed_archive) == packed_pin['zip_sha256'], 'actual packed ZIP SHA')
        with zipfile.ZipFile(args.packed_archive) as z: PACKED = cache.base.old.read_metadata(z, packed_pin)
    else:
        PACKED = {}
        for path, expected in packed_pin['metadata_sha256'].items():
            data = (args.metadata_dir / Path(path).name).read_bytes(); cache.require(cache.digest(data) == expected, 'actual packed metadata SHA'); PACKED[Path(path).name] = data.decode()
    for path, identity in [(args.ci_archive, cache.base.pin()['ci']), (args.row0_archive, cache.boundary.pin()['row0']), (args.row127_archive, cache.pin()['row127'])]:
        cache.require(cache.stream_sha(path) == identity['zip_sha256'], 'actual archived ZIP SHA')
    with zipfile.ZipFile(args.ci_archive) as z: CI = cache.base.read_ci(z)
    with zipfile.ZipFile(args.row0_archive) as z: ROW0 = cache.boundary.read_row0(z)
    with zipfile.ZipFile(args.row127_archive) as z: ROW127 = cache.read_row127(z)
    unittest.main(argv=[__file__], verbosity=2)
