#!/usr/bin/env python3
"""Tiny mocked/source tests and actual archived metadata. Never kernel evidence."""
import argparse
import ast
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import rawcu_generate as gen
import rawcu_restore as restore
import rawcu_runner as runner

PACKED = None
CI = None


class RowProbe(unittest.TestCase):
    def test_actual_packed_and_CI_receipts_non_kernel(self):
        lock = restore.pin()
        records, source, _ = restore.old.validate_metadata(PACKED, json.loads(restore.old.PIN_PATH.read_text()))
        self.assertEqual(records, lock['packed_objects'])
        restore.verify_sources(source)
        self.assertEqual(restore.validate_ci(CI), lock['ci']['objects'])
        for filename, mutate in [('compiled.jsonl', lambda x: x + x),
                                 ('replayed.jsonl', lambda x: ''),
                                 ('complete-CI-axioms.out', lambda x: x.replace('propext', 'sorryAx')),
                                 ('negative-actual-bin-change.out', lambda x: 'syntax error only')]:
            with self.subTest(filename=filename):
                bad = dict(CI); bad[filename] = mutate(bad[filename])
                with self.assertRaises(ValueError): restore.validate_ci(bad)
        steps = [json.loads(s) for s in CI['steps.jsonl'].splitlines()]
        for kind in ('exit', 'wrong command', 'duplicate', 'missing'):
            bad = copy.deepcopy(steps)
            if kind == 'exit': bad[0]['exit'] = 1
            elif kind == 'wrong command': bad[-1]['command'] = ['echo', 'fake']
            elif kind == 'duplicate': bad.append(bad[-1])
            else: bad = bad[:-1]
            # Mutate a required compiler/replay producer too, independently of incidental steps.
            if kind == 'exit':
                next(s for s in bad if s['name'].startswith('fresh_compile_'))['exit'] = 1
            data = dict(CI); data['steps.jsonl'] = '\n'.join(json.dumps(s) for s in bad)
            with self.assertRaises(ValueError): restore.validate_ci(data)
        for field in ('compiler_binary_sha256', 'toolchain_sha256', 'current_github_sha'):
            data = dict(CI); v = json.loads(data['provenance.json']); v[field] = {}; data['provenance.json'] = json.dumps(v)
            with self.assertRaises(ValueError): restore.validate_ci(data)

    def test_archive_API_objects_and_import_boundaries(self):
        lock = restore.pin()['ci']
        api = {'id': lock['artifact_id'], 'expired': False,
               'workflow_run': {'id': lock['source_run'], 'head_sha': lock['source_sha']}}
        restore.api_identity(api, lock)
        for bad in ({**api, 'id': 1}, {**api, 'expired': True}, {**api, 'workflow_run': {}},
                    {**api, 'workflow_run': {'id': lock['source_run'], 'head_sha': 'wrong'}}):
            with self.assertRaises(ValueError): restore.api_identity(bad, lock)
        for path in ('../escape', '/absolute', 'a\\b'):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, 'w') as z: z.writestr(path, b'not a proof')
            stream.seek(0)
            with zipfile.ZipFile(stream) as z, self.assertRaises(ValueError): restore.old.archive_index(z)
        for source in (b'import Unverified.Object\n', b'public import Mathlib\n', b'import Mathlib; axiom fake : False\n'):
            with self.assertRaises(ValueError): restore.check_imports(source, set())
        restore.check_imports(b'import Mathlib\nimport Known\n', {'Known'})
        with patch.object(restore, 'HERE', Path('/nonexistent-probe-fixture')):
            with self.assertRaises(ValueError):
                restore.verify_union_sources([], [{'module': 'Missing', 'source_sha256': '0' * 64}])
        with zipfile.ZipFile(io.BytesIO(), 'w') as z:
            z.writestr('Known.lean', b'import Mathlib\n')
            with self.assertRaises(ValueError):
                restore.verify_union_sources([z], [{'module': 'Known', 'source_sha256': '0' * 64}])

    def test_exact_object_bytes_and_duplicate_archive_paths(self):
        import warnings
        with tempfile.TemporaryDirectory() as tmp:
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, 'w') as z: z.writestr('Object.olean', b'FAKE test-only object')
            stream.seek(0)
            with zipfile.ZipFile(stream) as z:
                path = Path(tmp) / 'good.olean'
                restore.restore_object(z, 'Object.olean', path, restore.digest(b'FAKE test-only object'))
                with self.assertRaises(ValueError): restore.restore_object(z, 'Object.olean', Path(tmp) / 'bad.olean', '0' * 64)
                with self.assertRaises(FileExistsError): restore.restore_object(z, 'Object.olean', path, restore.digest(b'FAKE test-only object'))
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as z:
            z.writestr('duplicate', b'a')
            with warnings.catch_warnings():
                warnings.simplefilter('ignore', UserWarning)
                z.writestr('duplicate', b'a')
        stream.seek(0)
        with zipfile.ZipFile(stream) as z, self.assertRaises(ValueError): restore.old.archive_index(z)

    def test_self_contained_emission_and_control(self):
        values = [-2, 3] + [0] * 111  # FAKE tiny witness, not canonical production coefficients.
        sources, negative = gen.row_sources(values)
        self.assertEqual(list(sources), gen.MODULES)
        self.assertEqual(gen.SCOPE, {'U_rows': [0], 'U_components': 113, 'CU_field': False, 'full_hT': False})
        self.assertIn('pack (weights.U 0) = packedURow_000', sources[gen.MODULES[0]])
        self.assertIn('∀ k : Fin 113', sources[gen.MODULES[0]])
        self.assertIn('def KU0 : Nat := 3', sources[gen.MODULES[0]])
        self.assertIn('decide +kernel', sources[gen.MODULES[0]])
        self.assertIn('U := fun d k => if d = 0 ∧ k = 0 then weights.U d k + 1 else weights.U d k', sources[gen.MODULES[1]])
        self.assertIn('pack (changedWeights.U 0) = packedURow_000', negative)
        self.assertNotIn('if_pos', sources[gen.MODULES[1]])
        import re
        declarations = [gen.NS + '.' + n for s in sources.values() for n in re.findall(r'^(?:def|theorem) (\w+)', s, re.M)]
        self.assertEqual(declarations, gen.NAMES)
        for bad in ([], [0] * 112, [0] * 114, [True] * 113):
            with self.assertRaises(ValueError): gen.row_sources(bad)
        # Closed serialized column grammar and original column[k][d] orientation.
        line = 'def U_0 : List Int := [' + ', '.join(['(.ofNat 0)', '(.negSucc 1)'] + ['(.ofNat 3)'] * 126) + ']\n'
        self.assertEqual(gen.parse_columns(line, 0, 1)[0][:2], [0, -2])
        for bad in (line + line, line.replace('U_0', 'U_1'), line.replace('(.ofNat 0)', 'arbitraryTerm'), line.replace(', ', ',\n ', 1)):
            with self.assertRaises(ValueError): gen.parse_columns(bad, 0, 1)

    def test_policy_inverse_and_unknown_drift(self):
        here = restore.HERE; policy = json.loads((here / 'input_policy.json').read_text())
        for name, value in policy['sources'].items(): self.assertEqual(restore.sha(here / name), value)
        workflow = (restore.ROOT / '.github/workflows/transformer.yml').read_text()
        accepted = restore.inverse_workflow(workflow)
        self.assertNotIn('mathlib-raw-cu-row0', accepted)
        with self.assertRaises(ValueError): restore.inverse_workflow(workflow + '# unknown drift\n')
        for path, rule in restore.pin()['nonproof_projections'].items():
            data = (restore.ROOT / path).read_bytes()
            self.assertEqual(restore.digest(restore.project_nonproof(path, data)), rule['accepted_sha256'])
            with self.assertRaises(ValueError): restore.project_nonproof(path, data + b' ')
        for name in ('rawcu_generate.py', 'rawcu_restore.py', 'rawcu_runner.py', 'test_rawcu.py'):
            ast.parse((here / name).read_text())
        for forbidden in ('import numpy', 'load_weights(', 'quantise(', 'build_tables('):
            self.assertNotIn(forbidden, (here / 'rawcu_generate.py').read_text())
        self.assertNotIn('matrix:', workflow[workflow.index('  raw-cu-row0:\n'):workflow.index('  raw-correspondence-CI:\n')])

    def test_mocked_runner_acceptance_and_failure_boundaries_non_kernel(self):
        """FAKE object bytes exercise control flow only, not proof validity."""
        import os
        import contextlib
        common = runner.common
        for failure in (None, 'compile', 'replay', 'audit', 'negative'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as tmp, contextlib.ExitStack() as stack:
                here = Path(tmp); out = here / 'rawcu-out'
                stack.enter_context(patch.dict(os.environ, {'GITHUB_REPOSITORY': 'teal-sea/lean-checked-network', 'LEAN_NUM_THREADS': '2'}))
                for module in (runner, common, gen): stack.enter_context(patch.object(module, 'HERE', here))
                stack.enter_context(patch.object(runner, 'OUT', out))
                stack.enter_context(patch.object(runner, 'cloud_only'))
                stack.enter_context(patch.object(runner, 'snapshot', return_value={}))
                stack.enter_context(patch.object(restore, 'restore', return_value={'objects': []}))
                stack.enter_context(patch.object(restore, 'PIN_PATH', here / 'pin.json'))
                (here / 'pin.json').write_text('FAKE test-only pin')
                names = ('lean', 'lake', 'leanchecker')
                for n in names:
                    path = here / 'bin' / n; path.parent.mkdir(exist_ok=True); path.write_bytes(b'FAKE executable, never run')
                hashes = {n: restore.sha(here / 'bin' / n) for n in names}
                stack.enter_context(patch.object(restore, 'pin', return_value={'compiler_binary_sha256': hashes}))
                sources, negative = gen.row_sources([0] * 113)
                record = {'scope': gen.SCOPE, 'declarations': gen.NAMES}
                def emit(folder, check=False):
                    for m, text in sources.items():
                        path = here / (m.replace('.', '/') + '.lean'); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
                    (folder / 'changed-U.lean').write_text(negative)
                    return record
                stack.enter_context(patch.object(gen, 'emit', side_effect=emit))
                def run(label, args, seconds=300, negative=False):
                    if label == 'compiler-version': return 'version 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
                    if label == 'compiler-prefix': return str(here)
                    if failure == 'compile' and label.startswith('fresh_compile_'): raise ValueError('FAKE compile exit1')
                    if failure == 'replay' and label.startswith('fresh_replay_'): raise ValueError('FAKE replay exit1')
                    if failure == 'negative' and label.startswith('negative'): raise ValueError('FAKE wrong control exit0')
                    common.runner.STEPS[label] = {'seconds': 0.01}
                    (out / (label + '.time')).write_text('Maximum resident set size (kbytes): 12\n')
                    if label.startswith('fresh_compile_'): Path(args[4]).write_bytes(b'FAKE object, no kernel evidence')
                    return ''
                stack.enter_context(patch.object(common.runner, 'run', side_effect=run))
                if failure == 'audit': stack.enter_context(patch.object(runner, 'audit', side_effect=ValueError('FAKE diagnostic')))
                else: stack.enter_context(patch.object(runner, 'audit', side_effect=lambda label, imports, requested: len(requested)))
                if failure is None:
                    runner.main(None, None, None, None)
                    accepted = json.loads((out / 'U_ROW0_ACCEPTED.json').read_text())
                    self.assertEqual(accepted['scope'], gen.SCOPE)
                    self.assertEqual(len(accepted['fresh_compiled_replayed']), 2)
                else:
                    with self.assertRaises(ValueError): runner.main(None, None, None, None)
                    self.assertFalse((out / 'U_ROW0_ACCEPTED.json').exists())
                self.assertFalse((here / 'TransformerBridge/RawCorrespondence/CUGenerated/URow001.lean').exists())

    def test_strict_audit_and_exit_propagation(self):
        import rawcorrespondence_runner as common
        names = ['Fake.a', 'Fake.b']
        good = "'Fake.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Fake.b' does not depend on any axioms\n"
        self.assertEqual(common.check_correspondence_axioms(good, names), 2)
        for bad in ('', good + 'garbage', 'warning: bad\n' + good, good.replace('propext', 'unknown'),
                    good.replace(',\n ', ',\n garbage\n '), good + "'truncated' depends on axioms: [", good * 2):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(bad, names)
        for expected in (names[::-1], names * 2, names[:1]):
            with self.assertRaises(ValueError): common.check_correspondence_axioms(good, expected)
        with tempfile.TemporaryDirectory() as tmp, patch.object(common, 'OUT', Path(tmp)), patch.object(common.runner, 'run', side_effect=ValueError('producer exit 1')):
            with self.assertRaisesRegex(ValueError, 'exit 1'): runner.audit('mocked', ['Fake'], names)
        import os
        with patch.dict(os.environ, {}, clear=True), self.assertRaises(ValueError):
            gen.production_row()  # No local production evaluation.


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ci-archive', type=Path, required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--packed-archive', type=Path)
    group.add_argument('--metadata-dir', type=Path)
    args = parser.parse_args()
    if args.packed_archive:
        with zipfile.ZipFile(args.packed_archive) as archive:
            PACKED = restore.old.read_metadata(archive, json.loads(restore.old.PIN_PATH.read_text()))
    else:
        PACKED = {}
        for name, value in json.loads(restore.old.PIN_PATH.read_text())['metadata_sha256'].items():
            raw = (args.metadata_dir / Path(name).name).read_bytes()
            restore.require(restore.digest(raw) == value, 'actual retained metadata hash')
            PACKED[Path(name).name] = raw.decode()
    restore.require(restore.stream_sha(args.ci_archive) == restore.pin()['ci']['zip_sha256'], 'actual CI archive hash')
    with zipfile.ZipFile(args.ci_archive) as archive: CI = restore.read_ci(archive)
    unittest.main(argv=[__file__], verbosity=2)
