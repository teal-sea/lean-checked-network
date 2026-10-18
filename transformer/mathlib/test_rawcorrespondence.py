#!/usr/bin/env python3
"""Tiny arithmetic/static controls and actual retained metadata mutations; no Lean/model evaluation."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import sys
import unittest
import zipfile

import rawcorrespondence_generate as gen
import rawcorrespondence_restore as cache

METADATA = None
PIN = json.loads(cache.PIN_PATH.read_text())


# Actual archived diagnostic bytes; parser evidence only, never a kernel replay.
ACTUAL_AUDIT_FIXTURES = [("'TransformerBridge.RawCorrespondence.affine_eq_of_packed' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.contract_scale' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.CI_of_affine' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.unused_slots' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.tables_eq' does not depend on any axioms\n'TransformerBridge.RawCorrespondence.contract_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.contract_compose' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.score_composed' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.vvec_split' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.output_composed' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.xhat_contract_split' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.TU_of_ovec' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.CU_of_contract' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondence.G_of_contract' depends on axioms: [propext, Classical.choice, Quot.sound]\n'TransformerBridge.RawCorrespondenceFixture.signed_affine' depends on axioms: [propext, Classical.choice, Quot.sound]\n", ['TransformerBridge.RawCorrespondence.affine_eq_of_packed', 'TransformerBridge.RawCorrespondence.contract_scale', 'TransformerBridge.RawCorrespondence.CI_of_affine', 'TransformerBridge.RawCorrespondence.unused_slots', 'TransformerBridge.RawCorrespondence.tables_eq', 'TransformerBridge.RawCorrespondence.contract_add_left', 'TransformerBridge.RawCorrespondence.contract_compose', 'TransformerBridge.RawCorrespondence.score_composed', 'TransformerBridge.RawCorrespondence.vvec_split', 'TransformerBridge.RawCorrespondence.output_composed', 'TransformerBridge.RawCorrespondence.xhat_contract_split', 'TransformerBridge.RawCorrespondence.TU_of_ovec', 'TransformerBridge.RawCorrespondence.CU_of_contract', 'TransformerBridge.RawCorrespondence.G_of_contract', 'TransformerBridge.RawCorrespondenceFixture.signed_affine'], '34295a26b1d63c9289a9c4c57b3d2d47281abb8e0d3da42169fd5eae8d4cfcaf'), ("'TransformerBridge.RawCorrespondence.Canonical.representative_affine' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", ['TransformerBridge.RawCorrespondence.Canonical.representative_affine'], '96ab9b35921d41a580e2843c631e6ab0128770ddf8c2ab1139a94548a32d6a12')]

class CorrespondenceTests(unittest.TestCase):
    def test_mocked_audit_producer_strict_boundary(self):
        """Mocked output only: checks producer invocation, never executes Lean."""
        import tempfile
        from unittest.mock import patch
        import rawcorrespondence_runner as producer
        names = ['Example.first', 'Example.second']
        record = lambda n: "'" + n + "' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        good = ''.join(map(record, names))
        wrapped = "'TransformerBridge.RawCorrespondence.Canonical.representative_affine' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        with self.assertRaises(ValueError):
            producer.runner.check_axioms(wrapped, ['TransformerBridge.RawCorrespondence.Canonical.representative_affine'])
        with tempfile.TemporaryDirectory() as tmp, patch.object(producer, 'OUT', Path(tmp)):
            def mocked_run(label, args, seconds):
                self.assertEqual(label, 'mocked-axioms')
                self.assertEqual(args, ['lake', 'env', 'lean', str(Path(tmp) / 'mocked-axioms.lean')])
                self.assertEqual(seconds, 600)
                self.assertEqual(Path(args[-1]).read_text(), 'import Example\n#print axioms Example.first\n#print axioms Example.second\n')
                self.assertEqual(json.loads((Path(tmp) / 'mocked-axioms.expected.json').read_text()), names)
                return good
            with patch.object(producer.runner, 'run', side_effect=mocked_run):
                self.assertEqual(producer.audit('mocked', ['Example'], names), 2)
            bad_outputs = {
                'unknown axiom': good.replace('propext', 'sorryAx'),
                'missing': record(names[0]),
                'duplicate': record(names[0]) * 2,
                'reordered': ''.join(map(record, reversed(names))),
                'extra': good + record('Example.extra'),
                'malformed': good.replace('depends on axioms:', 'axioms:'),
                'truncated': good[:-2],
                'warning': 'warning: mocked diagnostic\n' + good,
            }
            for label, output in bad_outputs.items():
                with self.subTest(label=label), patch.object(producer.runner, 'run', return_value=output):
                    with self.assertRaises(ValueError):
                        producer.audit('mocked', ['Example'], names)
            with patch.object(producer.runner, 'run', return_value=wrapped):
                self.assertEqual(producer.audit('wrapped', ['Example'], ['TransformerBridge.RawCorrespondence.Canonical.representative_affine']), 1)
            with patch.object(producer.runner, 'run', side_effect=ValueError('producer failed: mocked-axioms, exit 1')):
                with self.assertRaisesRegex(ValueError, 'exit 1'):
                    producer.audit('mocked', ['Example'], names)
            with patch.object(producer.runner, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'duplicate requested'):
                    producer.audit('mocked', ['Example'], names + names)
                run.assert_not_called()

    def test_actual_diagnostics_closed_grammar_non_kernel(self):
        """Archived outputs and mocked mutations test parsing only, not Lean."""
        import rawcorrespondence_runner as producer
        for text, expected, digest in ACTUAL_AUDIT_FIXTURES:
            self.assertEqual(hashlib.sha256(text.encode()).hexdigest(), digest)
            self.assertEqual(producer.check_correspondence_axioms(text, expected), len(expected))
            mutations = [
                '', text[:-2], text + "'incomplete' depends on axioms: [propext,\n ",
                text.replace('propext', 'sorryAx'),
                text.replace('propext', 'propext, unknown'),
                text.replace('propext', 'propext,\n unknown'),
                text.replace('propext', 'propext,\n warning: surprise\n '),
                text.replace('propext', 'propext, propext'),
                text.replace('propext', ''), text.replace(']', ',]'),
                re.sub(r',(?: |\n )', lambda _: ',\t', text), re.sub(r',(?: |\n )', lambda _: ',\n\n ', text),
                text.replace('depends on axioms:', 'axioms:'),
                text + text, text + "'extra' does not depend on any axioms\n",
            ]
            for garbage in ('garbage', 'warning: diagnostic', 'error: diagnostic', ' ', '\n'):
                mutations.extend([garbage + '\n' + text, text + garbage,
                                  re.sub(r',(?: |\n )', lambda _: ',\n ' + garbage + '\n ', text, count=1)])
            for i, bad in enumerate(mutations):
                with self.subTest(digest=digest, mutation=i), self.assertRaises(ValueError):
                    producer.check_correspondence_axioms(bad, expected)
            for bad_names in (expected[:-1], expected + ['extra'], expected + expected,
                              ['wrong'] + expected[1:]):
                with self.assertRaises(ValueError):
                    producer.check_correspondence_axioms(text, bad_names)
        text, expected, _ = ACTUAL_AUDIT_FIXTURES[0]
        with self.assertRaises(ValueError):
            producer.check_correspondence_axioms(text, list(reversed(expected)))
        records = ["'A' does not depend on any axioms\n",
                   "'B' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"]
        self.assertEqual(producer.check_correspondence_axioms(''.join(records), ['A', 'B']), 2)
        for bad in (records[1] + records[0], records[0] * 2,
                    records[0] + 'garbage\n' + records[1],
                    records[0] + 'warning: diagnostic\n' + records[1],
                    records[0].replace('any axioms', 'any axioms ') + records[1]):
            with self.assertRaises(ValueError):
                producer.check_correspondence_axioms(bad, ['A', 'B'])

    def test_actual_retained_schema(self):
        self.assertIsNotNone(METADATA, 'actual metadata required; fake receipts cannot stand in')
        records, source, compiler = cache.validate_metadata(METADATA, PIN)
        self.assertEqual(len(records), 218)
        self.assertEqual(len(source['sources']), 51)
        self.assertEqual(len(compiler['binaries']), 3)

    def test_actual_receipt_mutations_rejected(self):
        mutations = []
        rows = [json.loads(s) for s in METADATA['compiled.jsonl'].splitlines()]
        for changed in [rows[:-1], rows + [rows[-1]], [{**rows[0], 'module': 'Transformer.Raw'}] + rows[1:]]:
            mutations.append(('compiled.jsonl', '\n'.join(json.dumps(x) for x in changed)))
        for field, value in [('scope', {'CI_components': 512}), ('modules', []), ('declarations', []),
                             ('coefficients', {}), ('pins', {}), ('outputs', {})]:
            obj = json.loads(METADATA['generation.json'])
            obj[field] = value
            mutations.append(('generation.json', json.dumps(obj)))
        obj = json.loads(METADATA['generation.json'])
        obj['pins']['transformer/mathlib/TransformerBridge/Bridge.lean'] = '0' * 64
        mutations.append(('generation.json', json.dumps(obj)))
        obj = json.loads(METADATA['generation.json']); obj['negative']['field'] = 'bin'
        mutations.append(('generation.json', json.dumps(obj)))
        obj = json.loads(METADATA['ACCEPTED.json']); obj['full_hT'] = 'PROVED'
        mutations.append(('ACCEPTED.json', json.dumps(obj)))
        obj = json.loads(METADATA['compiler.json']); obj['binaries']['lean']['sha256'] = '0' * 64
        mutations.append(('compiler.json', json.dumps(obj)))
        steps = [json.loads(s) for s in METADATA['steps.jsonl'].splitlines()]
        first = next(i for i, s in enumerate(steps) if s['name'].startswith('build_'))
        steps[first]['exit'] = 1
        mutations.append(('steps.jsonl', '\n'.join(json.dumps(x) for x in steps)))
        for filename, changed in mutations:
            with self.subTest(filename=filename):
                m = dict(METADATA); m[filename] = changed
                with self.assertRaises(ValueError):
                    cache.validate_metadata(m, PIN)

    def test_affine_signed_fixture(self):
        base = 1 << 208
        pack = lambda xs: sum(x * base ** i for i, x in enumerate(xs))
        matrix = [[-1, 2], [4, -3]]
        o, b = [-4, 6], [-5, 7]
        t = [sum(o[d] * matrix[d][i] for d in range(2)) + b[i] for i in range(2)]
        self.assertEqual(t, [23, -19])
        self.assertEqual(sum(o[d] * pack(matrix[d]) for d in range(2)) + pack(b), pack(t))
        self.assertLess(2 * (2 * 6 * 4 + 7), base)
        self.assertEqual(pack([base, 0]), pack([0, 1]))
        self.assertNotEqual([base, 0], [0, 1])

    def test_complete_defaults_domain(self):
        # Enumerates indexing/routing only, never model arithmetic or tables.
        slots = [(h, j, tk) for h in range(4) for j in range(3) for tk in range(114)]
        defaults = [s for s in slots if s[1] == 2 and s[2] != 113]
        active = [s for s in slots if s not in defaults]
        self.assertEqual((len(slots), len(active), len(defaults)), (1368, 916, 452))
        self.assertEqual(sum(tk == 113 and j < 2 for _, j, tk in active), 8)
        text = (cache.HERE / 'TransformerBridge/RawCorrespondenceSupport.lean').read_text()
        self.assertIn('theorem unused_slots', text)
        for field in ('sc', 'TI', 'TU'):
            self.assertIn(f'(W.rawTables S).{field} h 2 tk', text)
        self.assertIn('(hG : T.G = R.G)', text)
        for f in ('sc', 'TI', 'TU', 'CI', 'CU', 'G'):
            self.assertRegex(text, rf'\(h{f} : T\.{f} = R\.{f}\)')

    def test_control_helper_emission_non_kernel(self):
        """Static emitted strings only; rfl acceptance still requires public Lean CI."""
        baseline = {'TransformerBridge.RawCorrespondence.Generated.Parameters': 'da8759b32a54d46a05cf161be4f01ab46a7c620f230b3fdb9a7341b66deb31c0', 'TransformerBridge.RawCorrespondence.Generated.Representative': '0c96a65a37ebb7718554680bbb33abc225d6a5a6d76b422037fca7972567bc57', 'TransformerBridge.RawCorrespondence.Generated.PackedCI': 'e02359f33fa3dbefebd1e72aa3bfab29508c3caf0aa53702ff5ebefcee75182e', 'TransformerBridge.RawCorrespondence.Generated.CI': 'f5139ac9c6d7c68a51f4cb11af8c6c44444e18361a264e489a62e5d301bfd586', 'TransformerBridge.RawCorrespondence.Generated.Control': '467d2312d00ca734e054057149ca53369c1231e76a40c0dc589ec5735f8fa961'}
        old = 'theorem changed_bin_zero : changedWeights.bin 0 = weights.bin 0 + 1 := by\n  simp only [changedWeights, if_pos rfl]\n'
        fixed = 'theorem changed_bin_zero : changedWeights.bin 0 = weights.bin 0 + 1 := by\n  rfl\n'
        emitted = gen.sources()
        self.assertEqual(set(emitted), set(baseline))
        for module, text in emitted.items():
            with self.subTest(module=module):
                if module.endswith('.Control'):
                    self.assertEqual(text.count(fixed), 1)
                    self.assertNotIn(old, text)
                    text = text.replace(fixed, old)
                self.assertEqual(hashlib.sha256(text.encode()).hexdigest(), baseline[module])
        self.assertEqual(hashlib.sha256(gen.negative_source().encode()).hexdigest(), '9804f0a5b0a389a20df9d8bbb77e447df10d643d07a7453fe5aeb23c47b34129')

    def test_source_inventory_and_production_gates(self):
        for module, expected in [(gen.SUPPORT, gen.SUPPORT_NAMES), (gen.LINEAR, gen.LINEAR_NAMES), (gen.FIXTURE, gen.FIXTURE_NAMES)]:
            text = (cache.HERE / (module.replace('.', '/') + '.lean')).read_text()
            ns = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', text, re.M)
            found = [ns[0] + '.' + n for n in re.findall(r'^(?:def|theorem) (\w+)\b', text, re.M)]
            self.assertEqual(found, expected)
        modules, names = gen.inventory()
        sources = gen.sources()  # Static proof text only: no numeric emitter/checkpoint invocation.
        found = []
        self.assertEqual(list(sources), modules)
        for module, text in sources.items():
            ns = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', text, re.M)
            self.assertEqual(ns, [gen.NS])
            found += [ns[0] + '.' + n for n in re.findall(r'^(?:def|theorem) (\w+)\b', text, re.M)]
        self.assertEqual(found, names)
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(len(names), 16)
        self.assertIn(gen.OLD_PREFIX + '.RowsAll', sources[modules[0]])
        self.assertIn('Fin 1', sources[modules[1]])
        self.assertIn(gen.PREFIX + '.Representative', sources[modules[2]])
        self.assertIn('pack weights.bin = pack frozenCI', sources[modules[2]])
        self.assertIn('theorem CI_field', sources[modules[3]])
        self.assertIn('(TransformerBridge.toTables TransformerCore.Net.tab).CI =', sources[modules[3]])
        negative = gen.negative_source()
        self.assertIn('bin := fun i => if i = 0 then weights.bin i + 1 else weights.bin i', sources[modules[4]])
        self.assertIn('theorem changed_CI_ne', sources[modules[4]])
        self.assertIn(gen.PREFIX + '.Control', negative)
        self.assertIn('decide +kernel', negative)
        self.assertNotIn('Win :=', negative)

    def test_no_checkpoint_evaluation_and_cloud_guard(self):
        for name in ('rawcorrespondence_generate.py', 'rawcorrespondence_restore.py', 'rawcorrespondence_runner.py'):
            text = (cache.HERE / name).read_text(); ast.parse(text)
            self.assertNotRegex(text, r'\bimport numpy\b|\bimport int_transformer\b|\bquantise\(|\bload_weights\(')
        self.assertIn('cloud_only()', (cache.HERE / 'rawcorrespondence_generate.py').read_text())
        self.assertIn('cloud_only()', (cache.HERE / 'rawcorrespondence_restore.py').read_text())
        self.assertIn('cloud_only()', (cache.HERE / 'rawcorrespondence_runner.py').read_text())
        self.assertNotIn('extractall', (cache.HERE / 'rawcorrespondence_restore.py').read_text().replace('Never extractall', 'Never expand'))

    def test_current_source_compatibility(self):
        from unittest.mock import patch
        source = json.loads(METADATA['sources.json'])
        cache.verify_current_sources(source)
        original = Path.read_bytes
        for suffix in ('test_rawpacked.py', 'Transformer/Raw.lean', 'rawpacked_generate.py'):
            def changed(p, suffix=suffix):
                data = original(p)
                return data + b' ' if str(p).endswith(suffix) else data
            with patch.object(Path, 'read_bytes', changed):
                with self.assertRaises(ValueError): cache.verify_current_sources(source)
        pin = json.loads(original(cache.PIN_PATH))
        for mutation in ('extra', 'inverse', 'old', 'current'):
            bad = json.loads(json.dumps(pin))
            rule = bad['nonproof_source_compatibility']['transformer/mathlib/test_rawpacked.py']
            if mutation == 'extra': bad['nonproof_source_compatibility']['other'] = rule
            elif mutation == 'inverse': rule['inverse_projection'] += 'unknown'
            elif mutation == 'old': rule['accepted_sha256'] = '0' * 64
            else: rule['current_sha256'] = '0' * 64
            def altered(p):
                return json.dumps(bad).encode() if p == cache.PIN_PATH else original(p)
            with patch.object(Path, 'read_text', lambda p, *a, **k: altered(p).decode()):
                with self.assertRaises(ValueError): cache.verify_current_sources(source)

    def test_workflow_exact_preservation(self):
        path = cache.ROOT / '.github/workflows/transformer.yml'
        text = path.read_text()
        start = text.index('  raw-correspondence-CI:\n'); end = text.index('  row0-finalize:\n', start)
        block = text[start:end]
        self.assertIn('runs-on: ubuntu-latest', block)
        self.assertIn('inputs.core_mode == \'mathlib-raw-correspondence-CI\'', block)
        self.assertNotIn('pip install', block)
        self.assertIn('12100029309', block)
        self.assertEqual(text.count("inputs.core_mode != 'mathlib-raw-correspondence-CI'"), 3)
        old = (text[:start] + text[end:]).replace('          - mathlib-raw-correspondence-CI\n', '')
        old = old.replace("inputs.core_mode == 'mathlib-raw-correspondence-CI' && '-mathlib-raw-correspondence-CI' || ", '')
        old = old.replace("inputs.core_mode != 'mathlib-raw-correspondence-CI' && ", '')
        baseline = PIN['workflow_base_sha256']
        self.assertRegex(baseline, r'^[0-9a-f]{64}$')
        self.assertEqual(hashlib.sha256(old.encode()).hexdigest(), baseline)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--archive', type=Path)
    group.add_argument('--metadata-dir', type=Path)
    args = parser.parse_args()
    if args.archive:
        with zipfile.ZipFile(args.archive) as z:
            METADATA = cache.read_metadata(z, PIN)
    else:
        METADATA = {}
        for name, expected in PIN['metadata_sha256'].items():
            data = (args.metadata_dir / Path(name).name).read_bytes()
            cache.require(cache.digest(data) == expected, 'retained metadata digest mismatch')
            METADATA[Path(name).name] = data.decode()
    unittest.main(argv=[sys.argv[0]], verbosity=2)
