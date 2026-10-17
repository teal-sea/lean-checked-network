"""Tiny mocked execution controls, never kernel evidence or production generation."""
from contextlib import ExitStack
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
from unittest.mock import patch
import unittest

import input_artifacts as a
import input_runner as r
import input_source as s


class ExecutionControls(unittest.TestCase):
    def test_parent_lock_controls(self):
        lock = [{'row': 1, 'artifact_id': 2, 'run': 3, 'source_sha': 'a' * 40, 'zip_sha256': 'b' * 64}]
        a.validate_lock(lock)
        for bad in ([], lock * 2, [{**lock[0], 'row': 2}], [{**lock[0], 'row': True}],
                    [{**lock[0], 'zip_sha256': 'x'}], [{**lock[0], 'run': False}],
                    [{**lock[0], 'extra': 'ignored'}]):
            with self.assertRaises(ValueError): a.validate_lock(bad)
        with self.assertRaises(ValueError): a.validate_lock(lock, full=True)

    def scenario(self, root, failure=None, row=1):
        here = root / ('run-' + str(failure))
        here.mkdir()
        out = here / 'input-out'
        policy = here / 'input_policy.json'
        policy.write_text('{"sources": {}, "row0": {}}')
        pin = here / 'pin.json'
        pin.write_text('{"source_exceptions": {}}')
        generated = {m: '-- FAKE tiny source\n' for m, _ in s.chunks(1)}
        generated.update({f'TransformerBridge.InputRows.Row1{x}': '-- FAKE tiny source\n'
                          for x in ('Checks', '', 'Real')})
        calls = []

        def compile_module(m):
            calls.append(m)
            if failure == m: raise ValueError('FAKE producer exit')
            path = here / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'FAKE compiled object, no kernel evidence')
            for phase in ('fresh_compile_', 'fresh_replay_'):
                r.runner.STEPS[phase + m] = {'seconds': 0.01}
                (out / (phase + m + '.time')).write_text('Maximum resident set size (kbytes): 12\n')

        def negative(row):
            calls.append('negative')
            if failure == 'negative': raise ValueError('FAKE negative did not reject')

        def audit(*args):
            self.assertIn('TransformerCore.CachedFixture', args[1])
            self.assertIn('TransformerBridge.Row0Real', args[1])
            calls.append('audit')
            if failure == 'audit': raise ValueError('FAKE incomplete audit')

        identity_calls = []
        def identity():
            identity_calls.append(1)
            return {'compiler': 'FAKE' if failure != 'compiler-drift' or len(identity_calls) == 1 else 'changed'}

        with ExitStack() as stack:
            for target, name, value in (
                (r, 'HERE', here), (r, 'OUT', out), (r, 'POLICY', policy), (r.f, 'PIN', pin),
                (r.f, 'restore', lambda *args: ({'objects': []}, {}, {})),
                (r, 'restore_row0', lambda *args: {}), (r, 'policy_check', lambda *args: None),
                (r.source, 'row_sources', lambda *args: generated),
                (r.row0_prefix, 'identity', identity), (r.f, 'fresh_compile', compile_module),
                (r.runner, 'scan', lambda *args: None), (r, 'negative', negative),
                (r.runner, 'audit', audit), (r, 'audit_names', lambda *args: ['FAKE.exact_name']),
                (r.f, 'verify_sources', lambda *args: None), (r, 'validate_codegen', lambda *args: {})):
                stack.enter_context(patch.object(target, name, value))
            stack.enter_context(patch.dict(os.environ, {'GITHUB_ACTIONS': 'true',
                'GITHUB_REPOSITORY': 'teal-sea/lean-checked-network', 'INPUT_PUBLIC_STANDARD': '1',
                'LEAN_NUM_THREADS': '2', 'GITHUB_SHA': 'a' * 40,
                'GITHUB_REF': 'refs/heads/vizier/finish-transformer'}))
            args = SimpleNamespace(row=row, archive=None, artifact_metadata=None,
                row0_archive=None, row0_metadata=None, rows_lock=None, row1_lock=None)
            if failure is not None or row != 1:
                with self.assertRaises(ValueError): r.main(args)
                self.assertFalse((out / 'ROW_ACCEPTED.json').exists())
                self.assertFalse((out / 'ALL_ACCEPTED.json').exists())
            else:
                r.main(args)
                receipt = json.loads((out / 'ROW_ACCEPTED.json').read_text())
                self.assertEqual(receipt['fresh_compiled_replayed'], 11)
                self.assertEqual(len(receipt['pairs']), 113)
                self.assertIs(receipt['all_input_coverage'], False)
                self.assertEqual(calls, [*list(generated)[:8], 'negative', *list(generated)[8:], 'audit'])

    def test_row_archive_controls(self):
        import zipfile
        from row0_receipt import sha
        module = 'TransformerCore.Net.InputRows.FakeTiny'
        rel = module.replace('.', '/')
        text, data = '-- FAKE tiny source\n', b'FAKE tiny object'
        identity = {'compiler': 'FAKE compiler identity'}
        with tempfile.TemporaryDirectory(prefix='input-archive-') as tmp:
            root = Path(tmp)
            policy = root / 'input_policy.json'
            policy.write_text('{}')
            api = root / 'api.json'
            api.write_text(json.dumps({'id': 2, 'expired': False,
                'workflow_run': {'id': 3, 'head_sha': 'a' * 40}}))
            for change in (None, 'source', 'object', 'compiler', 'policy', 'step',
                           'negative', 'audit', 'middle-input'):
                pairs = [[1, b] for b in range(113)]
                if change == 'middle-input': pairs[56] = [1, 57]
                receipt = {'status': 'KERNEL_ACCEPTED', 'row': 1, 'pairs': pairs,
                    'source_sha': 'a' * 40, 'compiler': identity if change != 'compiler' else {},
                    'policy_sha256': sha(policy) if change != 'policy' else 'bad',
                    'generated_sources': {module: r.f.digest(text.encode())},
                    'fresh_objects': {module: r.f.digest(data)}}
                steps = [
                    {'name': 'fresh_compile_' + module, 'exit': 1 if change == 'step' else 0,
                     'command': ['lake', 'env', 'lean', '-o', '/fixture/.lake/build/lib/lean/' + rel + '.olean', rel + '.lean']},
                    {'name': 'fresh_replay_' + module, 'exit': 0, 'command': ['lake', 'env', 'leanchecker', module]},
                    {'name': 'negative_changed_actual_literal', 'exit': 0 if change == 'negative' else 1,
                     'command': ['lake', 'env', 'lean', '/fixture/input-out/changed-literal.lean']}]
                red = ('import TransformerCore.Net.Cached\n\nnamespace TransformerCore.Net.Cached\nopen TransformerCore.Net\n'
                    'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n' +
                    s.literal(1, 56, wrong_answer=True) + 'end TransformerCore.Net.Cached\n')
                archive = root / 'one-tiny-fixture.zip'
                with zipfile.ZipFile(archive, 'w') as z:
                    for name, content in {
                        'input-out/ROW_ACCEPTED.json': json.dumps(receipt),
                        'input-out/steps.jsonl': '\n'.join(json.dumps(x) for x in steps),
                        'input-out/changed-literal.lean': red,
                        'input-out/negative_changed_actual_literal.out': 'FAKE decide false control diagnostic',
                        'input-out/row-axioms.out': '' if change == 'audit' else "'FAKE.name' does not depend on any axioms",
                        rel + '.lean': 'bad' if change == 'source' else text,
                        '.lake/build/lib/lean/' + rel + '.olean': b'bad' if change == 'object' else data}.items():
                        z.writestr(name, content)
                lock = root / 'lock.json'
                lock.write_text(json.dumps([{'row': 1, 'artifact_id': 2, 'run': 3,
                    'source_sha': 'a' * 40, 'zip_sha256': sha(archive),
                    'archive': str(archive), 'api_metadata': str(api)}]))
                with patch.object(r, 'HERE', root), patch.object(r, 'POLICY', policy), \
                     patch.object(r.source, 'row_sources', return_value={module: text}), \
                     patch.object(r, 'validate_codegen', return_value={}), \
                     patch.object(r, 'audit_names', return_value=['FAKE.name']):
                    # The full-lock coverage guard is exercised separately. Here shrink the
                    # requested row list through a gate but retain normal archive validation.
                    contents = json.loads(lock.read_text())
                    # Gate expects throughput evidence as well.
                    with zipfile.ZipFile(archive, 'a') as z:
                        z.writestr('input-out/throughput.json', json.dumps({'throughput_acceptable': True,
                            'literal_compile_replay_seconds': 1, 'literal_peak_rss_kb': 1}))
                    contents[0]['zip_sha256'] = sha(archive)
                    lock.write_text(json.dumps(contents))
                    if change is None:
                        self.assertEqual(r.import_rows(lock, {}, identity, gate=True), {})
                    else:
                        with self.assertRaises(ValueError): r.import_rows(lock, {}, identity, gate=True)

    def test_acceptance_boundary(self):
        with tempfile.TemporaryDirectory(prefix='input-tiny-') as tmp:
            root = Path(tmp)
            self.scenario(root)
            for fail in [m for m, _ in s.chunks(1)] + [
                    'negative', 'TransformerBridge.InputRows.Row1Checks',
                    'TransformerBridge.InputRows.Row1', 'TransformerBridge.InputRows.Row1Real',
                    'audit', 'compiler-drift']:
                self.scenario(root, fail)
            self.scenario(root, 'missing-row1-lock', row=2)


if __name__ == '__main__':
    unittest.main()
