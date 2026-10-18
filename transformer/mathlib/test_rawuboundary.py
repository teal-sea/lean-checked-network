#!/usr/bin/env python3
"""Actual retained receipts plus toy/mocked boundary controls. NO kernel evidence."""
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
import warnings
import zipfile

import rawuboundary_generate as gen
import rawuboundary_restore as cache
import rawuboundary_runner as runner

PACKED = None
CI = None
ROW0 = None


class Boundary(unittest.TestCase):
    def test_actual_three_archive_metadata_non_kernel(self):
        previous = cache.previous
        packed, source, _ = previous.old.validate_metadata(PACKED, json.loads(previous.old.PIN_PATH.read_text()))
        self.assertEqual(len(packed), 218)
        previous.verify_sources(source)
        self.assertEqual(len(previous.validate_ci(CI)), 8)
        records = cache.validate_row0(ROW0)
        self.assertEqual(records, cache.pin()['row0']['objects'])
        self.assertEqual(len(packed + previous.pin()['ci']['objects'] + records), 228)
        mutations = []
        for field, value in [('scope', gen.SCOPE), ('fresh_compiled_replayed', records[::-1]),
                             ('compiler_binary_sha256', {}), ('restored_objects', []),
                             ('exact_production_audit_names', 2649), ('negative_actual_U_change', 'EXIT0')]:
            d = json.loads(ROW0['U_ROW0_ACCEPTED.json']); d[field] = value
            mutations.append(('U_ROW0_ACCEPTED.json', json.dumps(d)))
        steps = [json.loads(s) for s in ROW0['steps.jsonl'].splitlines()]
        for kind in ('exit', 'wrong compiler command', 'wrong replay module', 'missing', 'duplicate', 'negative exit0', 'negative timeout'):
            changed = copy.deepcopy(steps)
            if kind == 'exit': next(s for s in changed if s['name'].startswith('fresh_compile_'))['exit'] = 1
            elif kind == 'wrong compiler command': next(s for s in changed if s['name'].startswith('fresh_compile_'))['command'][2] = 'fake'
            elif kind == 'wrong replay module': next(s for s in changed if s['name'].startswith('fresh_replay_'))['command'][-1] = 'Wrong.Module'
            elif kind == 'missing': changed = changed[:-1]
            elif kind == 'duplicate': changed.append(changed[-1])
            elif kind == 'negative exit0': changed[-1]['exit'] = 0
            else: changed[-1]['exit'] = 124
            mutations.append(('steps.jsonl', '\n'.join(json.dumps(s) for s in changed)))
        mutations += [('compiled.jsonl', ROW0['compiled.jsonl'] * 2), ('replayed.jsonl', ''),
                      ('negative-actual-U-change.out', 'error: unknown identifier'),
                      ('row0-axioms.out', ROW0['row0-axioms.out'].replace('propext', 'sorryAx')),
                      ('complete-U-row0-axioms.out', ROW0['complete-U-row0-axioms.out'] + 'garbage\n')]
        for filename, value in mutations:
            with self.subTest(filename=filename):
                d = dict(ROW0); d[filename] = value
                with self.assertRaises(ValueError): cache.validate_row0(d)

    def test_layered_source_and_workflow_inverses(self):
        workflow = (cache.ROOT / '.github/workflows/transformer.yml').read_text()
        accepted = cache.inverse_workflow(workflow)
        self.assertEqual(cache.digest(accepted.encode()), cache.previous.pin()['workflow_projection']['current_sha256'])
        self.assertEqual(cache.digest(cache.previous.inverse_workflow(workflow).encode()),
                         cache.previous.pin()['workflow_projection']['accepted_sha256'])
        for bad in (workflow + '# drift\n', workflow.replace('mathlib-raw-u-boundary', 'wrong-mode', 1)):
            with self.assertRaises(ValueError): cache.inverse_workflow(bad)
        cache.verify_current_candidate(json.loads(ROW0['U_ROW0_ACCEPTED.json'])['candidate'])
        for rel, rule in cache.pin()['nonproof_projections'].items():
            data = (cache.ROOT / rel).read_bytes()
            self.assertEqual(cache.digest(cache.project_current(rel, data)), rule['accepted_sha256'])
            with self.assertRaises(ValueError): cache.project_current(rel, data + b' ')
        candidate = dict(cache.pin()['row0']['candidate']); candidate['unrecorded'] = '0' * 64
        with self.assertRaises(ValueError): cache.verify_current_candidate(candidate)
        policy = json.loads((cache.HERE / 'input_policy.json').read_text())
        for rel, expected in policy['sources'].items(): self.assertEqual(cache.sha(cache.HERE / rel), expected)

    def test_toy_emission_fixed_last_row_and_actual_coefficient_control(self):
        values = [-3, 2] + [0] * 111  # Toy only; no canonical coefficients are evaluated here.
        sources, negative = gen.row_sources(values)
        self.assertEqual(list(sources), gen.MODULES)
        self.assertEqual(gen.SCOPE, {'U_rows': [127], 'U_components': 113, 'CU_field': False, 'full_hT': False})
        text = '\n'.join(sources.values())
        self.assertIn('pack (weights.U 127) = packedURow_127', text)
        self.assertIn('∀ k : Fin 113, -(KU127 : Int) ≤ weights.U 127 k', text)
        self.assertIn('d = 127 ∧ k = 0 then weights.U d k + 1 else weights.U d k', text)
        self.assertIn('changedWeights.U 127 0 = weights.U 127 0 + 1 := by\n  rfl', text)
        self.assertIn('pack (changedWeights.U 127) = packedURow_127 := by\n  decide +kernel', negative)
        self.assertNotIn('if_pos', text)
        self.assertNotIn('URow000', text)
        declarations = [gen.NS + '.' + n for s in sources.values() for n in re.findall(r'^(?:def|theorem) (\w+)', s, re.M)]
        self.assertEqual(declarations, gen.NAMES)
        for bad in ([], [0] * 112, [0] * 114, [True] * 113):
            with self.assertRaises(ValueError): gen.row_sources(bad)
        with patch.dict(os.environ, {}, clear=True), self.assertRaises(ValueError): gen.production_row()
        # Emission/receipt boundary tested with a fake row, never production_row() locally.
        with tempfile.TemporaryDirectory() as tmp:
            here = Path(tmp); out = here / 'out'; out.mkdir()
            with patch.object(gen, 'HERE', here), patch.object(gen, 'cloud_only'), patch.object(gen, 'production_row', return_value=(values, {})):
                record = gen.emit(out); gen.emit(out, check=True)
                self.assertEqual(record['negative']['coordinate'], [127, 0])
                self.assertEqual(record['negative']['new'], record['negative']['old'] + 1)
                self.assertEqual(record['scope']['U_rows'], [127])
                for field, bad in [('scope', {**gen.SCOPE, 'U_rows': [0]}), ('modules', gen.MODULES * 2), ('declarations', gen.NAMES[:-1])]:
                    altered = {**record, field: bad}; (out / 'generation.json').write_text(json.dumps(altered))
                    with self.assertRaises(ValueError): gen.emit(out, check=True)
                (out / 'generation.json').write_text(json.dumps(record))
                extra = here / gen.PREFIX.replace('.', '/') / 'URow126.lean'; extra.write_text('-- toy extra source')
                with self.assertRaises(ValueError): gen.emit(out, check=True)

    def test_API_import_archive_overlap_and_object_errors(self):
        identity = cache.pin()['row0']
        api = {'id': identity['artifact_id'], 'expired': False,
               'workflow_run': {'id': identity['source_run'], 'head_sha': identity['source_sha']}}
        cache.previous.api_identity(api, identity)
        for bad in ({**api, 'id': 0}, {**api, 'expired': True}, {**api, 'workflow_run': {}},
                    {**api, 'workflow_run': {'id': identity['source_run'], 'head_sha': 'wrong'}}):
            with self.assertRaises(ValueError): cache.previous.api_identity(bad, identity)
        for raw in (b'import Unknown.Project\n', b'public import Mathlib\n', b'import Mathlib; axiom bad : False\n'):
            with self.assertRaises(ValueError): cache.previous.check_imports(raw, set())
        def archive(entries):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, 'w') as z:
                with warnings.catch_warnings():
                    warnings.simplefilter('ignore', UserWarning)
                    for name, value in entries: z.writestr(name, value)
            stream.seek(0)
            return zipfile.ZipFile(stream)
        with contextlib.ExitStack() as stack:
            a = stack.enter_context(archive([('same', b'bytes')]))
            b = stack.enter_context(archive([('same', b'bytes')]))
            c = stack.enter_context(archive([('same', b'bad')]))
            cache.check_overlaps([a, b])
            with self.assertRaises(ValueError): cache.check_overlaps([a, b, c])
            for entries in ([('../bad', b'')], [('/bad', b'')], [('x', b''), ('x', b'')], [('a\\b', b'')]):
                z = stack.enter_context(archive(entries))
                with self.assertRaises(ValueError): cache.previous.old.archive_index(z)
            with tempfile.TemporaryDirectory() as tmp:
                dest = Path(tmp) / 'object'
                cache.previous.restore_object(a, 'same', dest, cache.digest(b'bytes'))
                with self.assertRaises(ValueError): cache.previous.restore_object(c, 'same', Path(tmp) / 'bad', cache.digest(b'bytes'))
                with self.assertRaises(FileExistsError): cache.previous.restore_object(a, 'same', dest, cache.digest(b'bytes'))
        # Compiler drift and preexisting objects rejected before any restore write; no real objects used.
        with patch.object(cache, 'cloud_only'), patch.object(cache, 'sha', return_value='wrong'):
            with self.assertRaises(ValueError): cache.restore(None, None, None, None, None, None, {})

    def test_strict_audit_unknown_diagnostics_order_and_producer_exit(self):
        common = runner.common; names = ['Mock.a', 'Mock.b']
        good = "'Mock.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Mock.b' does not depend on any axioms\n"
        self.assertEqual(common.check_correspondence_axioms(good, names), 2)
        for bad in ('', good + 'suffix', 'warning: unexpected\n' + good, good.replace('propext', 'sorryAx'),
                    good.replace(',\n ', ',\n garbage\n '), good + "'truncated' depends on axioms: [", good * 2):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(bad, names)
        for requested in (names[::-1], names * 2, names[:1]):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(good, requested)
        with tempfile.TemporaryDirectory() as tmp, patch.object(common, 'OUT', Path(tmp)), patch.object(common.runner, 'run', side_effect=ValueError('producer exit1')):
            with self.assertRaisesRegex(ValueError, 'exit1'): runner.audit('mock', ['Mock'], names)

    def test_mocked_orchestrator_positive_and_failure_boundary_non_kernel(self):
        common = runner.common
        for failure in (None, 'compile', 'replay', 'audit', 'negative exit0', 'negative syntax', 'negative timeout'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as tmp, contextlib.ExitStack() as stack:
                here = Path(tmp); out = here / 'rawuboundary-out'
                stack.enter_context(patch.dict(os.environ, {'GITHUB_REPOSITORY': 'teal-sea/lean-checked-network', 'LEAN_NUM_THREADS': '2'}))
                for module in (runner, common, gen): stack.enter_context(patch.object(module, 'HERE', here))
                stack.enter_context(patch.object(runner, 'OUT', out)); stack.enter_context(patch.object(runner, 'cloud_only'))
                stack.enter_context(patch.object(runner, 'snapshot', return_value={}))
                stack.enter_context(patch.object(cache, 'restore', return_value={'objects': []}))
                stack.enter_context(patch.object(cache, 'PIN_PATH', here / 'pin.json')); (here / 'pin.json').write_text('FAKE')
                for n in ('lean', 'lake', 'leanchecker'):
                    path = here / 'bin' / n; path.parent.mkdir(exist_ok=True); path.write_bytes(b'FAKE not executed')
                hashes = {n: cache.sha(here / 'bin' / n) for n in ('lean', 'lake', 'leanchecker')}
                stack.enter_context(patch.object(cache, 'pin', return_value={'compiler_binary_sha256': hashes}))
                sources, negative = gen.row_sources([0] * 113)
                def emit(folder, check=False):
                    for m, text in sources.items():
                        path = here / (m.replace('.', '/') + '.lean'); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
                    (folder / 'changed-U127.lean').write_text(negative)
                    return {'scope': gen.SCOPE}
                stack.enter_context(patch.object(gen, 'emit', side_effect=emit))
                def run(label, args, seconds=300, negative=False):
                    if label == 'compiler-version': return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                    if label == 'compiler-prefix': return str(here)
                    if failure == 'compile' and label.startswith('fresh_compile_'): raise ValueError('FAKE compile exit1')
                    if failure == 'replay' and label.startswith('fresh_replay_'): raise ValueError('FAKE replay exit1')
                    if failure and failure.startswith('negative') and negative: raise ValueError('FAKE control ' + failure)
                    common.runner.STEPS[label] = {'seconds': 0.01}; (out / (label + '.time')).write_text('Maximum resident set size (kbytes): 12\n')
                    if label.startswith('fresh_compile_'): Path(args[4]).write_bytes(b'FAKE object, not proof evidence')
                    return ''
                stack.enter_context(patch.object(common.runner, 'run', side_effect=run))
                if failure == 'audit': stack.enter_context(patch.object(runner, 'audit', side_effect=ValueError('FAKE malformed diagnostic')))
                else: stack.enter_context(patch.object(runner, 'audit', side_effect=lambda label, imports, requested: len(requested)))
                if failure is None:
                    runner.main(None, None, None, None, None, None)
                    self.assertEqual(json.loads((out / 'U_ROW127_ACCEPTED.json').read_text())['scope'], gen.SCOPE)
                else:
                    with self.assertRaises(ValueError): runner.main(None, None, None, None, None, None)
                    self.assertFalse((out / 'U_ROW127_ACCEPTED.json').exists())
                self.assertFalse((here / gen.PREFIX.replace('.', '/') / 'URow126.lean').exists())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ci-archive', type=Path, required=True)
    parser.add_argument('--row0-archive', type=Path, required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--packed-archive', type=Path)
    group.add_argument('--metadata-dir', type=Path)
    args = parser.parse_args()
    packed_pin = json.loads(cache.previous.old.PIN_PATH.read_text())
    if args.packed_archive:
        cache.require(cache.stream_sha(args.packed_archive) == packed_pin['zip_sha256'], 'actual packed archive SHA')
        with zipfile.ZipFile(args.packed_archive) as z: PACKED = cache.previous.old.read_metadata(z, packed_pin)
    else:
        PACKED = {}
        for name, expected in packed_pin['metadata_sha256'].items():
            data = (args.metadata_dir / Path(name).name).read_bytes()
            cache.require(cache.digest(data) == expected, 'actual packed metadata SHA')
            PACKED[Path(name).name] = data.decode()
    cache.require(cache.stream_sha(args.ci_archive) == cache.previous.pin()['ci']['zip_sha256'], 'actual CI ZIP SHA')
    cache.require(cache.stream_sha(args.row0_archive) == cache.pin()['row0']['zip_sha256'], 'actual row0 ZIP SHA')
    with zipfile.ZipFile(args.ci_archive) as z: CI = cache.previous.read_ci(z)
    with zipfile.ZipFile(args.row0_archive) as z: ROW0 = cache.read_row0(z)
    unittest.main(argv=[__file__], verbosity=2)
