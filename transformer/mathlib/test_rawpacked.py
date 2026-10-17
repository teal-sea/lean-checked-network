"""Tiny source/harness fixtures only. Never evaluates a checkpoint or invokes Lean."""
from contextlib import redirect_stdout
import ast
import io
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import rawpacked_data as data
import rawpacked_generate as gen
import rawpacked_runner as runner
import rawpilot_data as scalar_data
from row0_receipt import check_axioms


class PackedFixtures(unittest.TestCase):
    def test_inventory_scope_and_scalar_preservation(self):
        modules, names = data.inventory()
        self.assertEqual((len(modules), len(names), len(set(names))), (194, 2595, 2595))
        self.assertEqual(tuple(map(len, scalar_data.inventory())), (96, 2842))
        self.assertEqual(len([m for m in modules if re.search(r'\.Row\d{3}$', m)]), 128)
        self.assertFalse(any(re.search(r'\.TI\d{3}$|\.TIAll$', m) for m in modules))
        self.assertEqual(sum(__import__('math').prod(s) for s in data.SHAPES.values()), 226688)
        self.assertEqual(data.layout('Win'), ((1, 0), 512, 128))
        self.assertEqual(set(data.expected_coefficients()), set(data.SHAPES))
        self.assertEqual(re.findall(r'^  (\w+) :=', gen.scalar.weight_body(), re.M), list(data.SHAPES))
        site = gen.site_source()
        self.assertIn('(i : Fin 512)', site)
        self.assertIn('(weights.rawTables 256).TI 0 0 0 i', site)
        self.assertIn('(TransformerBridge.toTables TransformerCore.Net.tab).TI 0 0 0 i', site)
        self.assertIn('Ko Kw rows_eq o_bound rows_bound target_bound carry_bound packed_cert i', site)
        self.assertNotIn('TIAll', site)

    def test_tiny_signed_packing_and_orientation(self):
        base = 1 << 208
        self.assertEqual(gen.pack_int([-2, 3]), -2 + 3 * base)
        self.assertEqual(gen.pack_int([4, -5]), 4 - 5 * base)
        self.assertEqual(gen.pack_int([]), 0)
        # Genuine carry collision; length alone does not establish injectivity.
        self.assertEqual(gen.pack_int([base, 0]), gen.pack_int([0, 1]))
        columns = [[-2, 4], [3, -5]]
        self.assertEqual([gen.pack_int([col[d] for col in columns]) for d in range(2)],
                         [-2 + 3 * base, 4 - 5 * base])
        body = gen.row_body(0, [-2, 3])  # a tiny serialization string, never compiled
        self.assertIn('weights.Win 0 i', body)
        self.assertIn('∀ i : Fin 512', body)
        self.assertIn('-(Kw : Int)', body)
        self.assertNotIn('Ko', body)
        self.assertIn('.negSucc', gen.row_body(1, [4, -5]))

    def test_generic_support_exact_independent_gate_and_bounds(self):
        text = (data.HERE / 'TransformerBridge/RawPackedSupport.lean').read_text()
        actual = ['TransformerBridge.RawPacked.' + n for n in
                  re.findall(r'^(?:def|theorem) (\w+)\b', text, re.M)]
        self.assertEqual(actual, data.SUPPORT_NAMES)
        self.assertNotIn('Net.', text)
        self.assertNotIn('Generated', text)
        self.assertIn('TransformerCore.digits_eq', text)
        self.assertIn('contract_bounded o W Ko Kw ho hw', text)
        self.assertIn('(hB : 2 * K < B)', text)
        runner_text = Path(runner.__file__).read_text()
        self.assertLess(runner_text.index("audit('support'"), runner_text.index("run('generate'"))
        self.assertIn("'--raw-pilot'", runner_text)
        self.assertNotIn("'--raw-packed-pilot'", runner_text)
        self.assertIn('matrix_preprocessing', runner_text)
        self.assertIn('site_packed_TI', runner_text)
        fixture = (data.HERE / 'TransformerBridge/RawPackedFixture.lean').read_text()
        self.assertEqual(re.findall(r'^theorem (\w+)', fixture, re.M),
                         ['carry_collision', 'signed_transport'])

    def test_no_missing_bound_and_exact_row_coverage(self):
        rows = gen.rows_all_source()
        for suffix in ('.1', '.2 i'):
            self.assertEqual(re.findall(r'exact row_cert_(\d{3})' + re.escape(suffix), rows),
                             [f'{d:03d}' for d in range(128)])
        packed = gen.packed_source(7)
        self.assertIn('def Ko : Nat := 7', packed)
        self.assertIn('theorem target_bound (i : Fin 512)', packed)
        self.assertIn('2 * (128 * Ko * Kw) < TransformerCore.B', packed)
        self.assertNotIn('rowPacked_000 :', packed)
        # Pure data sources must not open namespaces absent from their imports.
        text = gen.source(['TransformerCore.Model'], data.NS + '.Data', 'def x : Int := 1')
        self.assertNotIn('open TransformerBridge', text)

    def test_public_only_and_producer_diagnostics(self):
        with patch.dict(gen.scalar.os.environ, {}, clear=True):
            with self.assertRaisesRegex(ValueError, 'public manual Actions only'):
                gen.cloud_only()
        with tempfile.TemporaryDirectory() as tmp, patch.object(runner, 'OUT', Path(tmp)), \
                redirect_stdout(io.StringIO()):
            self.exit, self.text = 2, 'error: FAKE actual producer error\nwarning: FAKE unknown warning\n'
            def fake(args, **kwargs):
                kwargs['stdout'].write(self.text)
                return subprocess.CompletedProcess(args, self.exit)
            with patch.object(runner.subprocess, 'run', side_effect=fake):
                for negative in (False, True):
                    with self.assertRaises(ValueError) as caught:
                        runner.run('fixture-failed-' + str(negative), ['FAKE'], negative=negative)
                    self.assertIn(self.text, str(caught.exception))
                    self.assertIn('exit 2', str(caught.exception))
                    self.assertNotIn('unrecognized warning', str(caught.exception))
                self.exit, self.text = 0, 'warning: FAKE unknown warning\n'
                with self.assertRaisesRegex(ValueError, 'unrecognized warning'):
                    runner.run('fixture-warning', ['FAKE'])
                for code in (0, 124, 137):
                    self.exit, self.text = code, 'decide is false\n'
                    with self.assertRaises(ValueError):
                        runner.run('fixture-invalid-negative-' + str(code), ['FAKE'], negative=True)
                self.exit, self.text = 1, 'Tactic `decide` proved that the proposition\nFAKE\nis false\n'
                runner.run('fixture-negative', ['FAKE'], negative=True)
            records = [json.loads(s) for s in (Path(tmp) / 'steps.jsonl').read_text().splitlines()]
            self.assertEqual([r['exit'] for r in records], [2, 2, 0, 0, 124, 137, 1])

    def test_tiny_manifest_is_closed_and_hash_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = root / data.PREFIX.replace('.', '/')
            folder.mkdir(parents=True)
            out = root / 'receipts'
            out.mkdir()
            path = folder / 'Fixture.lean'
            path.write_text('namespace Fixture\ndef x : Int := -2\nend Fixture\n')
            rel = str(path.relative_to(root))
            control = out / 'changed-production-literal.lean'
            control.write_text('-- FAKE tiny negative source\n')
            receipt = {'modules': [data.PREFIX + '.Fixture'], 'declarations': ['Fixture.x'],
                'pins': {'fixture': 'pinned'}, 'shapes': {'tok': [2, 2]},
                'scope': {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512},
                'coefficients': {'tok': {'shape': [2, 2], 'count': 4, 'serialized_axes': [0, 1],
                    'vectors': 2, 'width': 2, 'canonical_flat_integer_json_sha256': 'a' * 64}},
                'negative': {'source_sha256': data.sha(control), 'field': 'Win', 'coordinate': [1, 0],
                    'old': 3, 'new': 4, 'nonzero_ovec': 2, 'target_component': 0},
                'outputs': {rel: data.sha(path)}}
            manifest = out / 'generation.json'
            def write(obj):
                manifest.write_text(json.dumps(obj))
            write(receipt)
            with patch.object(data, 'HERE', root), patch.object(data, 'SHAPES', {'tok': (2, 2)}), \
                    patch.object(data, 'verify_pins', return_value={'fixture': 'pinned'}), \
                    patch.object(data, 'layout', return_value=((0, 1), 2, 2)), \
                    patch.object(data, 'expected_coefficients', return_value=receipt['coefficients']), \
                    patch.object(data, 'inventory', return_value=(receipt['modules'], ['Fixture.x'])):
                data.validate_generated(out)
                for key, value in [('declarations', []), ('coefficients', {}), ('scope', {})]:
                    write({**receipt, key: value})
                    with self.assertRaises(ValueError):
                        data.validate_generated(out)
                write(receipt)
                path.write_text(path.read_text().replace('-2', '-3'))
                with self.assertRaisesRegex(ValueError, 'hash differs'):
                    data.validate_generated(out)

    def test_existing_workflow_modes_and_jobs_preserved(self):
        workflow = (data.ROOT / '.github/workflows/transformer.yml').read_text()
        # Only the new input, its concurrency suffix and exclusion from old broad jobs vary.
        restored = workflow[:workflow.index('\n  raw-packed-pilot:')]
        restored = restored.replace('          - mathlib-raw-packed-pilot\n', '')
        restored = restored.replace("inputs.core_mode == 'mathlib-raw-packed-pilot' && '-mathlib-raw-packed' || ", '')
        restored = restored.replace(" && inputs.core_mode != 'mathlib-raw-packed-pilot'", '')
        self.assertEqual(hashlib.sha256((restored.rstrip() + '\n').encode()).hexdigest(),
                         '7dbae4d1c5b9f785e8b4aab4e118a4a8351f0323867d1c12b7bde375602a3101')
        self.assertIn("inputs.core_mode == 'mathlib-raw-packed-pilot' && github.event.repository.private == false", workflow)
        self.assertIn('runs-on: ubuntu-latest', workflow[workflow.index('\n  raw-packed-pilot:'):])
        self.assertIn('cancel-in-progress: false', workflow)

    def test_all_new_python_parses(self):
        for name in ('rawpacked_data.py', 'rawpacked_generate.py', 'rawpacked_runner.py', 'test_rawpacked.py'):
            ast.parse((data.HERE / name).read_text(), filename=name)

    def test_exact_named_audits_fail_closed(self):
        good = "'Fixture.a' does not depend on any axioms\n'Fixture.b' depends on axioms: [propext]\n"
        self.assertEqual(check_axioms(good, ['Fixture.a', 'Fixture.b']), 2)
        for bad in (good.splitlines()[0], good.replace('propext', 'bogus'), good + good.splitlines()[0]):
            with self.assertRaises(ValueError):
                check_axioms(bad, ['Fixture.a', 'Fixture.b'])


if __name__ == '__main__':
    unittest.main()
