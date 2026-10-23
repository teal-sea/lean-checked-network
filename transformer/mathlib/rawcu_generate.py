"""Exactly one real U row packing witness. Production parsing/emission is cloud only."""
import json
from pathlib import Path
import re
import sys
from rawpilot_generate import cloud_only, source, literal
from rawpacked_generate import pack_int
from rawpilot_data import HERE, sha
from rawcu_restore import require, digest

PREFIX = 'TransformerBridge.RawCorrespondence.CUGenerated'
NS = 'TransformerBridge.RawCorrespondence.CUCanonical'
SCOPE = {'U_rows': [0], 'U_components': 113, 'CU_field': False, 'full_hT': False}
MODULES = [PREFIX + '.URow000', PREFIX + '.Control']
NAMES = [NS + '.' + n for n in ('KU0', 'packedURow_000', 'urow_cert_000', 'changedWeights', 'changed_u_zero')]


def parse_columns(text, start, count):
    """Closed exact integer literal grammar from the authenticated original producer."""
    rows = []
    for i in range(start, start + count):
        matches = re.findall(r'^def U_' + str(i) + r' : List Int := (\[.*\])$', text, re.M)
        require(len(matches) == 1, 'missing/duplicate U column')
        body = matches[0][1:-1]
        tokens = body.split(', ')
        require(len(tokens) == 128, 'U column dimension')
        values = []
        for token in tokens:
            m = re.fullmatch(r'\(\.(ofNat|negSucc) (0|[1-9][0-9]*)\)', token)
            require(m is not None, 'nonliteral U coefficient')
            v = int(m[2]); values.append(v if m[1] == 'ofNat' else -v - 1)
        rows.append(values)
    declarations = re.findall(r'^def U_(\d+) :', text, re.M)
    require(declarations == [str(i) for i in range(start, start + count)], 'extra/reordered U column')
    return rows


def row_sources(values):
    require(type(values) is list and len(values) == 113 and all(type(v) is int for v in values), 'exact U row0 dimensions')
    bound = max(abs(v) for v in values)
    packed = pack_int(values)
    row = source(['TransformerBridge.RawPacked.Generated.Weights'], NS,
        'open TransformerBridge.RawPacked TransformerBridge.RawPackedPilot\n\n' +
        f'def KU0 : Nat := {bound}\n\ndef packedURow_000 : Int := {literal(packed)}\n\n' +
        'theorem urow_cert_000 : pack (weights.U 0) = packedURow_000 ∧\n'
        '    (∀ k : Fin 113, -(KU0 : Int) ≤ weights.U 0 k ∧ weights.U 0 k ≤ KU0) := by\n'
        '  decide +kernel\n')
    control = source([MODULES[0]], NS,
        'open TransformerBridge.RawPackedPilot\n\n'
        'def changedWeights : Transformer.Weights := { weights with\n'
        '  U := fun d k => if d = 0 ∧ k = 0 then weights.U d k + 1 else weights.U d k }\n\n'
        'theorem changed_u_zero : changedWeights.U 0 0 = weights.U 0 0 + 1 := by\n  rfl\n')
    negative = source([MODULES[1]], NS,
        'open TransformerBridge.RawPacked TransformerBridge.RawPackedPilot\n\n'
        'example : pack (changedWeights.U 0) = packedURow_000 := by\n  decide +kernel\n')
    return dict(zip(MODULES, [row, control])), negative


def production_row():
    cloud_only()
    from rawcu_restore import pin
    lock = pin(); expected = {r['module']: r['source_sha256'] for r in lock['packed_objects']}
    columns, hashes = [], {}
    for start, count in [(0, 64), (64, 49)]:
        module = 'TransformerBridge.RawPacked.Generated.U' + str(start // 64).zfill(3)
        path = HERE / (module.replace('.', '/') + '.lean')
        require(sha(path) == expected[module], 'original U source drift')
        columns += parse_columns(path.read_text(), start, count)
        hashes[str(path.relative_to(HERE))] = sha(path)
    # Existing serialization: U columns[k][d], unchanged semantic coordinate U d k.
    canonical = [columns[k][d] for d in range(128) for k in range(113)]
    from rawpacked_data import expected_coefficients
    require(digest(json.dumps(canonical, separators=(',', ':')).encode()) ==
            expected_coefficients()['U']['canonical_flat_integer_json_sha256'], 'canonical U coefficient hash/layout')
    return [column[0] for column in columns], hashes


def emit(out, check=False):
    cloud_only()
    sys.set_int_max_str_digits(0)
    values, hashes = production_row()
    sources, negative = row_sources(values)
    record = {'scope': SCOPE, 'modules': MODULES, 'declarations': NAMES,
              'outputs': {m.replace('.', '/') + '.lean': digest(s.encode()) for m, s in sources.items()},
              'original_U_sources': hashes, 'row_sha256': digest(json.dumps(values, separators=(',', ':')).encode()),
              'negative': {'field': 'U', 'coordinate': [0, 0], 'old': values[0], 'new': values[0] + 1,
                           'delta': 1, 'negative_sha256': digest(negative.encode())}, 'kernel_verdict': 'KERNEL_NOT_RUN'}
    for m, text in sources.items():
        path = HERE / (m.replace('.', '/') + '.lean')
        if not check:
            require(not path.exists(), 'preexisting U probe source'); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
        require(path.read_text() == text, 'U probe emitted source drift')
    if not check:
        (out / 'changed-U.lean').write_text(negative)
        (out / 'generation.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    require((out / 'changed-U.lean').read_text() == negative and json.loads((out / 'generation.json').read_text()) == record,
            'U probe receipt/control reproducibility')
    actual = {str(p.relative_to(HERE)) for p in (HERE / PREFIX.replace('.', '/')).rglob('*.lean')}
    require(actual == set(record['outputs']), 'extra/missing U probe sources')
    return record
