"""Tiny fixture-only controls. No Lean, checkpoint evaluation or production numeric emission."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import rawpilot_data as data
import rawpilot_generate as gen
import rawpilot_runner as runner
from row0_receipt import check_axioms
import sync_core
import row0_runner as warning_policy


class RawPilotFixtures(unittest.TestCase):
    def test_closed_scope_and_fields(self):
        modules, names = data.inventory()
        self.assertEqual((len(modules), len(names), len(set(names))), (96, 2842, 2842))
        self.assertEqual(sum(__import__('math').prod(v) for v in data.SHAPES.values()), 226688)
        self.assertEqual(re.findall(r'^  (\w+) :=', gen.weight_body(), re.M), list(data.SHAPES))
        self.assertIn('Fin 512', gen.site_source())
        self.assertIn('(weights.rawTables 256).TI 0 0 0 i', gen.site_source())
        self.assertIn('(TransformerBridge.toTables TransformerCore.Net.tab).TI 0 0 0 i', gen.site_source())
        self.assertEqual(re.findall(r'exact ti_cert_(\d+)', gen.all_source('TI', 512)),
                         [f'{i:03d}' for i in range(512)])
        self.assertEqual(data.layout('WV'), ((0, 2, 1), 128, 128))
        self.assertEqual(data.layout('WO'), ((0, 2, 1), 512, 32))
        self.assertEqual(data.layout('Win'), ((1, 0), 512, 128))

    def test_tiny_serialization(self):
        emitted = {}
        with patch.object(gen, 'STAGES', (('V', 16), ('O', 16), ('TI', 16))):
            gen.emit({'tok': [[-2, 3], [4, -5]]}, [7, -8], [9, -10],
                     lambda m, s: emitted.__setitem__(m, s))
        self.assertIn('(.negSucc 1)', emitted[data.PREFIX + '.tok000'])
        self.assertIn('(.negSucc 4)', emitted[data.PREFIX + '.tok000'])
        self.assertIn('by decide +kernel', emitted[data.PREFIX + '.TI000'])
        self.assertIn('TransformerCore.Net.TI0_0_0 0', emitted[data.PREFIX + '.TI000'])
        self.assertNotIn('build_tables', emitted[data.PREFIX + '.Weights'])
        self.assertEqual(gen.literal(-1), '(.negSucc 0)')

    def test_raw_sync_is_narrow_and_old_modes_unchanged(self):
        self.assertEqual(len(sync_core.inventory()), 3)
        self.assertEqual(len(sync_core.inventory(support=True)), 4)
        self.assertEqual(len(sync_core.inventory(cached_support=True)), 6)
        raw = sync_core.inventory(raw_pilot=True)
        self.assertEqual(len(raw), 15)
        self.assertEqual(raw[-1][0], 'Transformer.Net.Weights')
        self.assertFalse(any('Cached' in m or '.B.' in m or 'Pair' in m for m, *_ in raw))
        for _, _, _, original, mirrored in raw:
            self.assertEqual(mirrored, re.sub(rb'\bTransformer\b', b'TransformerCore', original))

    def test_exact_audit_rejects_omissions_axioms_duplicates(self):
        names = ['Fixture.a', 'Fixture.b']
        good = "'Fixture.a' does not depend on any axioms\n'Fixture.b' depends on axioms: [propext]\n"
        self.assertEqual(check_axioms(good, names), 2)
        for bad in (good.splitlines()[0], good.replace('propext', 'sorryAx'),
                    good + good.splitlines()[0], good.replace('Fixture.b', 'Fixture.c')):
            with self.assertRaises(ValueError):
                check_axioms(bad, names)

    def test_producer_exit_warning_timeout_and_negative_boundaries(self):
        # Each subprocess is a fake tiny command; even successful controls are NOT Lean evidence.
        with tempfile.TemporaryDirectory() as tmp, patch.object(runner, 'OUT', Path(tmp)):
            calls = []

            def fake_command(args, **kwargs):
                calls.append(args)
                kwargs['stdout'].write(self.fake_text)
                return subprocess.CompletedProcess(args, self.fake_exit)

            with patch.object(runner.subprocess, 'run', side_effect=fake_command), redirect_stdout(io.StringIO()):
                for code in (1, 2, 124, 137):
                    self.fake_exit, self.fake_text = code, 'FAKE ordinary failure\n'
                    with self.assertRaises(ValueError):
                        runner.run('fake-producer-' + str(code), ['fixture'])
                for code, text in ((0, 'decide false'), (1, 'unrelated error'), (124, 'decide false')):
                    self.fake_exit, self.fake_text = code, text
                    with self.assertRaises(ValueError):
                        runner.run('fake-invalid-negative-' + str(code), ['fixture'], negative=True)
                self.fake_exit, self.fake_text = 1, "FAKE tactic 'decide' evaluated to false\n"
                runner.run('fake-required-negative', ['fixture'], negative=True)
                self.fake_exit, self.fake_text = 0, 'FAKE success\n'
                runner.run('fake-success', ['fixture'])
                self.fake_text = 'warning: unknown new RawPilot warning\n'
                with self.assertRaises(ValueError):
                    runner.run('fake-unknown-warning', ['fixture'])
            self.assertTrue(all(a[:2] == ['/usr/bin/time', '-v'] and 'timeout' in a for a in calls))
            records = [json.loads(line) for line in (Path(tmp) / 'steps.jsonl').read_text().splitlines()]
            self.assertEqual(len(records), 10)
            self.assertEqual(records[0]['exit'], 1)

    def test_both_runners_preserve_failure_diagnostics_and_strict_warnings(self):
        diagnostics = 'error: FAKE actual compiler failure\nwarning: FAKE unknown warning\ntrailing diagnostic\n'
        for owner in (runner, warning_policy):
            with self.subTest(runner=owner.__name__), tempfile.TemporaryDirectory() as tmp, \
                    patch.object(owner, 'OUT', Path(tmp)), redirect_stdout(io.StringIO()):
                def fake_command(args, **kwargs):
                    kwargs['stdout'].write(diagnostics)
                    return subprocess.CompletedProcess(args, code)

                with patch.object(owner.subprocess, 'run', side_effect=fake_command):
                    code = 2
                    with self.assertRaises(ValueError) as caught:
                        owner.run('fake-error-and-warning', ['fixture'])
                    self.assertIn('failed:', str(caught.exception))
                    self.assertIn('2', str(caught.exception))
                    self.assertIn(diagnostics, str(caught.exception))
                    self.assertNotIn('unrecognized warning:', str(caught.exception))
                    code = 0
                    with self.assertRaisesRegex(ValueError, 'unrecognized warning:'):
                        owner.run('fake-success-unknown-warning', ['fixture'])
                    code = 1
                    diagnostics = "decide evaluated to false\nwarning: FAKE unknown warning\n"
                    with self.assertRaisesRegex(ValueError, 'unrecognized warning:'):
                        owner.run('fake-negative-unknown-warning', ['fixture'], negative=True)
                records = [json.loads(line) for line in (Path(tmp) / 'steps.jsonl').read_text().splitlines()]
                self.assertEqual([r['exit'] for r in records], [2, 0, 1])
                self.assertNotIn('fake-error-and-warning', owner.STEPS)
            diagnostics = 'error: FAKE actual compiler failure\nwarning: FAKE unknown warning\ntrailing diagnostic\n'

    def test_tiny_receipt_rejects_missing_changed_extra_and_bad_control(self):
        # A single four-coefficient fixture, not a generated model or compiled Lean artifact.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = root / 'TransformerBridge/RawPilot/Generated'
            folder.mkdir(parents=True)
            out = root / 'receipts'
            out.mkdir()
            path = folder / 'Fixture.lean'
            rel = str(path.relative_to(root))
            text = 'namespace Fixture\ndef x : List Int := [1, -2, 3, -4]\nend Fixture\n'
            path.write_text(text)
            control = out / 'changed-production-literal.lean'
            control.write_text('-- FAKE control fixture; no Lean execution\n')
            receipt = {
                'modules': [data.PREFIX + '.Fixture'], 'declarations': ['Fixture.x'],
                'pins': {'fixture': 'pinned'}, 'shapes': {'tok': [2, 2]},
                'scope': {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512},
                'coefficients': {'tok': {'shape': [2, 2], 'count': 4, 'serialized_axes': [0, 1],
                    'vectors': 2, 'width': 2, 'canonical_flat_integer_json_sha256': 'a' * 64}},
                'negative': {'source_sha256': data.sha(control), 'field': 'Win', 'coordinate': [1, 0],
                             'old': 3, 'new': 4, 'nonzero_ovec': 2, 'target_component': 0},
                'outputs': {rel: data.sha(path)}}
            manifest = out / 'generation.json'
            manifest.write_text(json.dumps(receipt))
            with patch.object(data, 'HERE', root), patch.object(data, 'SHAPES', {'tok': (2, 2)}), \
                 patch.object(data, 'verify_pins', return_value={'fixture': 'pinned'}), \
                 patch.object(data, 'inventory', return_value=(receipt['modules'], ['Fixture.x'])):
                data.validate_generated(out)
                path.write_text(text.replace('3', '5'))
                with self.assertRaises(ValueError):
                    data.validate_generated(out)
                path.write_text(text)
                extra = folder / 'Extra.lean'
                extra.write_text('-- FAKE extra\n')
                with self.assertRaises(ValueError):
                    data.validate_generated(out)
                extra.unlink()
                for field, bad in [('declarations', []), ('coefficients', {}),
                                   ('scope', {'TI_components': 1})]:
                    altered = dict(receipt)
                    altered[field] = bad
                    manifest.write_text(json.dumps(altered))
                    with self.assertRaises(ValueError):
                        data.validate_generated(out)
                manifest.write_text(json.dumps(receipt))
                control.write_text('-- FAKE altered control\n')
                with self.assertRaises(ValueError):
                    data.validate_generated(out)

    def test_exact_immutable_raw_warning_baseline(self):
        headers = [
            "Transformer/Raw.lean:173:0: automatically included section variable(s) unused in theorem `Transformer.Weights.rsoftmax_eq`:",
            "Transformer/Raw.lean:181:0: automatically included section variable(s) unused in theorem `Transformer.Weights.resid_dot`:",
        ]
        original = (warning_policy.HERE / 'Transformer/Raw.lean').read_bytes()
        pins = json.loads((warning_policy.HERE / 'RawPilot-pins.json').read_text())
        self.assertEqual(data.sha(warning_policy.HERE / 'Transformer/Raw.lean'),
                         pins['transformer/mathlib/Transformer/Raw.lean'])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'Transformer/Raw.lean'
            source.parent.mkdir()
            source.write_bytes(original)
            with patch.object(warning_policy, 'HERE', root):
                for header in headers:
                    accepted = warning_policy.inherited_warnings('warning: ' + header)
                    self.assertEqual(len(accepted), 1)
                    self.assertEqual(accepted[0]['baseline_sha256'],
                                     pins['transformer/mathlib/Transformer/Raw.lean'])
                    with self.assertRaises(ValueError):
                        warning_policy.inherited_warnings('warning: ' + header + ' changed')
                with self.assertRaises(ValueError):
                    warning_policy.inherited_warnings('warning: Transformer/Raw.lean:1:0: new proof warning')
                # The actual Raw runner still rejects nonzero producers even with allowed warnings.
                def producer(args, **kwargs):
                    kwargs['stdout'].write('\n'.join('warning: ' + h for h in headers))
                    return subprocess.CompletedProcess(args, self.fake_exit)

                with patch.object(runner, 'OUT', root), \
                        patch.object(runner.subprocess, 'run', side_effect=producer), \
                        redirect_stdout(io.StringIO()):
                    self.fake_exit = 0
                    runner.run('fake-exact-raw-baseline', ['fixture'])
                    for code in (1, 2, 124, 137):
                        self.fake_exit = code
                        with self.assertRaises(ValueError):
                            runner.run('fake-exact-raw-nonzero-' + str(code), ['fixture'])
                source.write_bytes(original + b'\n')
                for header in headers:
                    with self.assertRaises(ValueError):
                        warning_policy.inherited_warnings('warning: ' + header)

    def test_local_generation_guard(self):
        with patch.dict(gen.os.environ, {'GITHUB_ACTIONS': 'false'}, clear=False):
            with self.assertRaises(ValueError):
                gen.cloud_only()


if __name__ == '__main__':
    unittest.main(verbosity=2)
