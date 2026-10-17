"""Actual A-policy/upload-layout compatibility controls; no kernel or production emission."""
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile
from unittest.mock import patch
import input_compat as c
import input_artifacts
import input_runner

HERE = Path(__file__).resolve().parent


class Compatibility(unittest.TestCase):
    def test_actual_policy_and_red_cases(self):
        old = (HERE / 'input_policy_a01a98c.json').read_bytes()
        self.assertEqual(c.digest(old), c.OLD_POLICY)
        item = {'row': 1, 'run': c.OLD_RUN, 'source_sha': c.OLD_HEAD}
        compiler = json.loads((HERE / 'input_policy_compatibility.json').read_text())['compiler']
        receipt = {'compiler': compiler, 'row': 1, 'source_sha': c.OLD_HEAD, 'policy_sha256': c.OLD_POLICY}
        def archive(data):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, 'w') as z:
                z.writestr('input_policy.json', data)
                z.writestr('row0_checkpoint.json', (HERE / 'input_checkpoint_a01a98c.json').read_bytes())
            stream.seek(0)
            return zipfile.ZipFile(stream)
        with archive(old) as z:
            self.assertEqual(c.validate_row_policy(z, receipt, item, HERE), 'PINNED_A01_ROW1_POLICY')
            with self.assertRaises(ValueError): c.validate_row_policy(z, {**receipt, 'compiler': {}}, item, HERE)
            for field, value in [('run', c.OLD_RUN + 1), ('row', 113), ('source_sha', 'b' * 40)]:
                with self.assertRaises(ValueError): c.validate_row_policy(z, receipt, {**item, field: value}, HERE)
            with self.assertRaises(ValueError): c.validate_row_policy(z, {**receipt, 'policy_sha256': '0' * 64}, item, HERE)
        with archive(old + b' ') as z:
            with self.assertRaises(ValueError): c.validate_row_policy(z, {**receipt, 'policy_sha256': c.digest(old + b' ')}, item, HERE)
        with archive(old) as z:
            for row in (2, 56, 112):
                self.assertEqual(c.validate_row_policy(z, {**receipt, 'row': row},
                    {**item, 'row': row, 'run': c.GRID_RUN}, HERE), 'PINNED_A01_ROW1_POLICY')
            for row in (False, True, 0, 113):
                with self.assertRaises(ValueError): c.validate_row_policy(z, {**receipt, 'row': row}, {**item, 'row': row, 'run': c.GRID_RUN}, HERE)
            with self.assertRaises(ValueError): c.validate_row_policy(z, {**receipt, 'row': 2}, {**item, 'row': 2}, HERE)
        current = (HERE / 'input_policy.json').read_bytes()
        with archive(current) as z:
            self.assertEqual(c.validate_row_policy(z, {**receipt, 'policy_sha256': c.digest(current)}, item, HERE), 'CURRENT_POLICY')
        # Mutate actual disk bytes in memory only: every real current source remains pinned.
        original = Path.read_bytes
        for suffix in ('.github/workflows/transformer.yml', 'input_runner.py', 'input_source.py',
                       'TransformerBridge/Row0.lean', 'input_policy_compatibility.json'):
            def changed(p, suffix=suffix):
                data = original(p)
                return data + b' ' if str(p).endswith(suffix) else data
            with archive(old) as z, patch.object(Path, 'read_bytes', changed):
                with self.assertRaises(ValueError): c.validate_row_policy(z, receipt, item, HERE)
        self.assertIs(input_artifacts.validate_row_policy, c.validate_row_policy)
        self.assertIs(input_runner.validate_row_policy, c.validate_row_policy)


if __name__ == '__main__': unittest.main()
