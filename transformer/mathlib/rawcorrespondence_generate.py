#!/usr/bin/env python3
"""Emit CI proof source only in public manual Actions. No checkpoint/quantizer evaluation."""
import argparse
import hashlib
import json
from pathlib import Path

from rawpilot_generate import cloud_only, source
from rawpacked_data import PREFIX as OLD_PREFIX, NS as OLD_NS

HERE = Path(__file__).resolve().parent
PREFIX = 'TransformerBridge.RawCorrespondence.Generated'
NS = 'TransformerBridge.RawCorrespondence.Canonical'
SUPPORT = 'TransformerBridge.RawCorrespondenceSupport'
FIXTURE = 'TransformerBridge.RawCorrespondenceFixture'
LINEAR = 'TransformerBridge.RawCorrespondenceLinear'
LINEAR_NAMES = ['TransformerBridge.RawCorrespondence.' + n for n in
                ('contract_add_left', 'contract_compose', 'score_composed', 'vvec_split',
                 'output_composed', 'xhat_contract_split', 'TU_of_ovec', 'CU_of_contract', 'G_of_contract')]
SUPPORT_NAMES = ['TransformerBridge.RawCorrespondence.' + n for n in
                 ('affine_eq_of_packed', 'contract_scale', 'CI_of_affine', 'unused_slots', 'tables_eq')]
FIXTURE_NAMES = ['TransformerBridge.RawCorrespondenceFixture.signed_affine']
DECLARATIONS = {
    'Parameters': ['scaledX', 'frozenCI', 'Kx', 'Kb', 'x_bound', 'bias_bound'],
    'Representative': ['representative_affine'],
    'PackedCI': ['target_bound', 'carry_bound', 'packed_cert'],
    'CI': ['ci_eq', 'CI_field'],
    'Control': ['changedWeights', 'changed_bin_zero', 'changed_CI_zero', 'changed_CI_ne'],
}


def inventory():
    return ([PREFIX + '.' + m for m in DECLARATIONS],
            [NS + '.' + n for names in DECLARATIONS.values() for n in names])


def sources():
    pre = f'open TransformerBridge.RawPilot TransformerBridge.RawPacked\nopen TransformerBridge.RawCorrespondence {OLD_NS}\n\n'
    bodies = {
        'Parameters': ([SUPPORT, OLD_PREFIX + '.RowsAll', 'TransformerCore.Net.W.Misc'], '''def scaledX (d : Fin 128) : Int := (256 : Int) ^ 2 * weights.xhat 113 2 d

def frozenCI (i : Fin 512) : Int := TransformerCore.nth 0 TransformerCore.Net.CI i

def Kx : Nat := 256 ^ 2 * 117

def Kb : Nat := 520813984

theorem x_bound (d : Fin 128) : -(Kx : Int) ≤ scaledX d ∧ scaledX d ≤ Kx := by
  revert d
  decide +kernel

theorem bias_bound (i : Fin 512) : -(Kb : Int) ≤ weights.bin i ∧ weights.bin i ≤ Kb := by
  revert i
  decide +kernel
'''),
        'Representative': ([PREFIX + '.Parameters'], '''/-- First production use of the new primitive: actual CI coordinate zero, packed at width one.
This gate precedes the complete width-512 certificate. -/
theorem representative_affine : (weights.rawTables 256).CI 0 = frozenCI 0 := by
  rw [CI_of_affine]
  exact affine_eq_of_packed scaledX
    (fun d : Fin 128 => fun _ : Fin 1 => weights.Win d 0)
    (fun d => pack (fun _ : Fin 1 => weights.Win d 0))
    (fun _ : Fin 1 => weights.bin 0) (fun _ : Fin 1 => frozenCI 0)
    Kx Kw Kb (fun _ => rfl) x_bound (fun d _ => rows_bound d 0)
    (fun _ => bias_bound 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 0
'''),
        'PackedCI': ([PREFIX + '.Representative'], '''theorem target_bound (i : Fin 512) :
    -((128 * Kx * Kw + Kb : Nat) : Int) ≤ frozenCI i ∧
      frozenCI i ≤ (128 * Kx * Kw + Kb : Nat) := by
  revert i
  decide +kernel

theorem carry_bound : 2 * (128 * Kx * Kw + Kb) < TransformerCore.B := by decide +kernel

theorem packed_cert : contract scaledX packedRows + pack weights.bin = pack frozenCI := by
  decide +kernel
'''),
        'CI': ([PREFIX + '.PackedCI', 'TransformerCore.Net.Weights'], '''theorem ci_eq (i : Fin 512) : (weights.rawTables 256).CI i = frozenCI i := by
  rw [CI_of_affine]
  exact affine_eq_of_packed scaledX weights.Win packedRows weights.bin frozenCI
    Kx Kw Kb rows_eq x_bound rows_bound bias_bound target_bound carry_bound packed_cert i

/-- Complete unconditional CI field, in the requested frozen-to-raw orientation. -/
theorem CI_field : (TransformerBridge.toTables TransformerCore.Net.tab).CI =
    (weights.rawTables 256).CI := by
  funext i
  exact (ci_eq i).symm
'''),
        'Control': ([PREFIX + '.CI'], '''/-- Alter exactly one actual canonical learned bin coefficient. -/
def changedWeights : Transformer.Weights := { weights with
  bin := fun i => if i = 0 then weights.bin i + 1 else weights.bin i }

theorem changed_bin_zero : changedWeights.bin 0 = weights.bin 0 + 1 := by
  simp only [changedWeights, if_pos rfl]

/-- This proves the real perturbation affects CI before the independent false decide control. -/
theorem changed_CI_zero : (changedWeights.rawTables 256).CI 0 =
    (weights.rawTables 256).CI 0 + 1 := by
  change (256 : Int) ^ 2 * (∑ d, weights.xhat 113 2 d * weights.Win d 0) +
      changedWeights.bin 0 =
    ((256 : Int) ^ 2 * (∑ d, weights.xhat 113 2 d * weights.Win d 0) + weights.bin 0) + 1
  rw [changed_bin_zero]
  ring

theorem changed_CI_ne : (changedWeights.rawTables 256).CI 0 ≠ frozenCI 0 := by
  rw [changed_CI_zero, ci_eq]
  omega
'''),
    }
    return {PREFIX + '.' + m: source(imports, NS, pre + body)
            for m, (imports, body) in bodies.items()}


def negative_source():
    return source([PREFIX + '.Control'], NS,
        f'open TransformerBridge.RawPilot {OLD_NS}\n\n' + """example : (changedWeights.rawTables 256).CI 0 =
    (TransformerBridge.toTables TransformerCore.Net.tab).CI 0 := by
  rw [TransformerBridge.RawCorrespondence.CI_of_affine]
  decide +kernel
""")


def validate(root, out):
    modules, names = inventory()
    record = json.loads((out / 'generation.json').read_text())
    expected = sources()
    paths = {m.replace('.', '/') + '.lean': text.encode() for m, text in expected.items()}
    actual = {str(p.relative_to(root)) for p in (root / PREFIX.replace('.', '/')).rglob('*.lean')}
    if actual != set(paths) or record.get('modules') != modules or record.get('declarations') != names:
        raise ValueError('missing/duplicate/extra/wrong-field CI source inventory')
    hashes = {p: hashlib.sha256(data).hexdigest() for p, data in paths.items()}
    if record.get('outputs') != hashes or any((root / p).read_bytes() != data for p, data in paths.items()):
        raise ValueError('CI generated source identity differs')
    if record.get('scope') != {'CI_components': 512, 'full_hT': False}:
        raise ValueError('wrong CI field scope')
    if record.get('negative') != {'field': 'bin', 'coordinate': [0], 'delta': 1,
                                  'witness': NS + '.changed_CI_ne'}:
        raise ValueError('wrong actual coefficient control')
    neg = (out / 'changed-bin.lean').read_bytes()
    if neg != negative_source().encode() or record.get('negative_sha256') != hashlib.sha256(neg).hexdigest():
        raise ValueError('changed actual bin control differs')
    return record


def main(check=False):
    cloud_only()
    out = HERE / 'rawcorrespondence-out'
    out.mkdir(exist_ok=True)
    modules, names = inventory()
    outputs = {}
    for module, text in sources().items():
        rel = module.replace('.', '/') + '.lean'
        path = HERE / rel
        if not check:
            if path.exists():
                raise ValueError('refusing preexisting CI source')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        outputs[rel] = hashlib.sha256(text.encode()).hexdigest()
    neg = negative_source()
    if not check:
        (out / 'changed-bin.lean').write_text(neg)
        (out / 'generation.json').write_text(json.dumps({
            'scope': {'CI_components': 512, 'full_hT': False}, 'modules': modules,
            'declarations': names, 'outputs': outputs,
            'negative_sha256': hashlib.sha256(neg.encode()).hexdigest(),
            'negative': {'field': 'bin', 'coordinate': [0], 'delta': 1,
                         'witness': NS + '.changed_CI_ne'},
            'kernel_verdict': 'KERNEL_NOT_RUN'}, indent=2) + '\n')
    validate(HERE, out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    main(parser.parse_args().check)
