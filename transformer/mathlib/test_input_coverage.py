"""Metadata/source-only controls. No Lean, packing, model evaluation, or row emission."""
import ast
import json
from pathlib import Path
import unittest
import input_source as s
from row0_receipt import check_axioms

HERE = Path(__file__).resolve().parent


class InputControls(unittest.TestCase):
    def test_inventory_and_middle_input_controls(self):
        full = [[a, b] for a in range(113) for b in range(113)]
        self.assertEqual(len(s.coverage(full)), 12769)
        for mutation in ('missing', 'duplicate', 'wrong-row', 'middle-input', 'bool', 'reorder'):
            bad = [p[:] for p in full]
            if mutation == 'missing': bad.pop(6384)
            elif mutation == 'duplicate': bad[6384] = bad[6383][:]
            elif mutation == 'wrong-row': bad[113][0] = 0
            elif mutation == 'middle-input': bad[6384][1] += 1
            elif mutation == 'bool': bad[0][0] = False
            else: bad[56], bad[57] = bad[57], bad[56]
            with self.assertRaises(ValueError): s.coverage(bad)
        row = [[1, b] for b in range(113)]
        s.coverage(row, 1)
        with self.assertRaises(ValueError): s.coverage(full[:113], 1)
        with self.assertRaises(ValueError): s.coverage(row[:-1], 1)

    def test_bounded_chunks_and_exact_names(self):
        for a in range(1, 113):
            chunks = s.chunks(a)
            self.assertEqual([b for _, bs in chunks for b in bs], list(range(113)))
            self.assertEqual([len(bs) for _, bs in chunks], [16] * 7 + [1])
            names = s.pair_names(a)
            self.assertEqual(len(names), 226)
            self.assertEqual(len(set(names)), 226)
        with self.assertRaises(ValueError): s.chunks(0)
        # One tiny literal source fixture only; never generate a production row locally.
        text = s.chunk_source(1, [56])
        self.assertIn('cachedFastCheck cfg tab frozenCache bnd E2 1 56 = true', text)
        self.assertIn('cached_pilot_1_56', text)
        self.assertIn('cachedFastCheck_eq cfg tab frozenCache cache_eq bnd E2 1 56', text)
        red = s.literal(1, 56, wrong_answer=True)
        self.assertIn('bnd E2 1 56 = false', red)
        self.assertNotIn('cached_pilot', red)
        for forbidden in ('native_decide', 'sorry', 'admit', 'set_option linter'):
            self.assertNotIn(forbidden, text + red)

    def test_tiny_template_specialization(self):
        # Shrink the enumeration in memory; no production row/all-grid emission.
        from unittest.mock import patch
        with patch.object(s, 'N', 1), patch.object(s, 'chunks', return_value=[('Fake.Chunk', [0])]):
            row = s.row_sources(1, HERE)
            all_inputs = s.all_sources(HERE)
        integer = row['TransformerBridge.InputRows.Row1']
        real = row['TransformerBridge.InputRows.Row1Real']
        self.assertIn('have hf := row1_fastCheck b', integer)
        self.assertIn('TransformerCore.Net.G_length 1 b hf k hk', integer)
        self.assertIn('rw [← row0_cfg]', integer)
        self.assertIn('rw [row0_E2]', integer)
        self.assertNotIn(' 0 b', integer + real)
        self.assertIn('(row1_integer_margin b)', real)
        self.assertIn('frozen_tables_bounded', real)
        integer = all_inputs['TransformerBridge.InputAll']
        real = all_inputs['TransformerBridge.InputAllReal']
        self.assertIn('theorem all_integer_margin (a b : Fin 113)', integer)
        self.assertIn('have hf := all_fastCheck a b', integer)
        self.assertIn('TransformerCore.Net.G_length a b hf k hk', integer)
        self.assertIn('theorem all_mq_argmax (a b : Fin 113)', real)
        self.assertIn('(all_integer_margin a b)', real)
        self.assertNotIn(' 0 b', integer + real)

    def test_exact_audit_rejects_subsets_and_custom_axioms(self):
        names = s.pair_names(1)
        lines = [f"'{n}' does not depend on any axioms" for n in names]
        self.assertEqual(check_axioms('\n'.join(lines), names), 226)
        for bad in (lines[:-1], lines + lines[:1], lines[:112] + lines[113:],
                    [f"'{names[0]}' depends on axioms: [evil]"] + lines[1:]):
            with self.assertRaises(ValueError): check_axioms('\n'.join(bad), names)

    def test_workflow_inverse_and_policy(self):
        root = HERE.parents[1]
        workflow = (root / '.github/workflows/transformer.yml').read_text()
        from rawcu_restore import inverse_workflow
        workflow = inverse_workflow(workflow)
        workflow = workflow[:workflow.index('  raw-correspondence-CI:\n')] + workflow[workflow.index('  row0-finalize:\n', workflow.index('  raw-correspondence-CI:\n')):]
        workflow = workflow.replace('          - mathlib-raw-correspondence-CI\n', '')
        workflow = workflow.replace("inputs.core_mode == 'mathlib-raw-correspondence-CI' && '-mathlib-raw-correspondence-CI' || ", '')
        workflow = workflow.replace("inputs.core_mode != 'mathlib-raw-correspondence-CI' && ", '')
        inverse = workflow.split('\n  input-row1:\n', 1)[0].rstrip() + '\n'
        inverse = inverse.replace('          - mathlib-input-row1\n', '').replace('          - mathlib-input-grid\n', '').replace('          - mathlib-input-all\n', '')
        inverse = inverse.replace("inputs.core_mode == 'mathlib-input-grid' && '-mathlib-input-grid' || inputs.core_mode == 'mathlib-input-all' && '-mathlib-input-all' || inputs.core_mode == 'mathlib-input-row1' && '-mathlib-input-row1' || ", '')
        inverse = inverse.replace("inputs.core_mode != 'mathlib-input-grid' && inputs.core_mode != 'mathlib-input-all' && inputs.core_mode != 'mathlib-input-row1' && ", '')
        inverse = inverse.replace("      input_artifact_lock:\n        description: Parent-adjudicated JSON lock (row1 for grid; rows1..112 for all assembly)\n        type: string\n        default: ''\n", '')
        import hashlib
        self.assertEqual(hashlib.sha256(inverse.encode()).hexdigest(),
                         '2bbb247b10304fc72c0e6d31cbd673a791f29d9e3f8362b211658f9eeb8d9be0')
        job = workflow.split('\n  input-row1:\n')[1].split('\n  input-grid-gate:\n')[0]
        self.assertIn('runs-on: ubuntu-latest', job)
        self.assertIn('github.event.repository.private == false', job)
        self.assertIn('--row 1', job)
        self.assertNotIn('matrix:', job)
        self.assertNotIn('--all', job)
        grid = workflow.split('\n  input-grid:\n')[1].split('\n  input-all:\n')[0]
        self.assertIn('needs: input-grid-gate', grid)
        self.assertIn('max-parallel: 4', grid)
        self.assertIn('--row1-lock', grid)
        self.assertIn('--rows-lock', workflow.split('\n  input-all:\n')[1])
        policy = json.loads((HERE / 'input_policy.json').read_text())
        for name, digest in policy['sources'].items():
            self.assertEqual(hashlib.sha256((HERE / name).read_bytes()).hexdigest(), digest)
        for name in ('input_runner.py', 'input_source.py'):
            ast.parse((HERE / name).read_text())


if __name__ == '__main__':
    unittest.main()
