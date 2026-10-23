"""Closed packed-pilot inventory. Importing performs no model evaluation."""
import json
import re

from rawpilot_data import HERE, ROOT, SHAPES, CHUNK, CERT_CHUNK, layout, sha, verify_pins

PREFIX = 'TransformerBridge.RawPacked.Generated'
NS = 'TransformerBridge.RawPackedPilot'
SUPPORT = 'TransformerBridge.RawPackedSupport'
SUPPORT_NAMES = ['TransformerBridge.RawPacked.' + n for n in (
    'pack', 'pack_zero', 'pack_succ', 'pack_add', 'pack_mul', 'pack_const_zero',
    'pack_sumN', 'pack_contract', 'pkI_injective_bounded', 'pack_injective_bounded',
    'sumN_bounded', 'contract_bounded', 'contract_eq_of_packed')]


def expected_coefficients():
    return json.loads((HERE / 'RawPacked-coefficients.json').read_text())['coefficients']


def inventory():
    modules, names = [], []
    for key in SHAPES:
        _, rows, _ = layout(key)
        for start in range(0, rows, CHUNK):
            modules.append(f'{PREFIX}.{key}{start // CHUNK:03d}')
            names.extend(f'{NS}.Data.{key}_{i}' for i in range(start, min(start + CHUNK, rows)))
        modules.append(f'{PREFIX}.{key}')
        names.append(f'{NS}.Data.{key}')
    modules += [PREFIX + '.Weights', PREFIX + '.Vectors']
    names.extend(NS + '.' + n for n in ('weights', 'proposedV', 'proposedO'))
    for stage, count in (('V', 32), ('O', 128)):
        for start in range(0, count, CERT_CHUNK):
            modules.append(f'{PREFIX}.{stage}{start // CERT_CHUNK:03d}')
            names.extend(f'{NS}.{stage.lower()}_cert_{i:03d}' for i in range(start, start + CERT_CHUNK))
        modules.append(PREFIX + '.' + stage + 'All')
        names.append(NS + '.' + stage.lower() + '_eq')
    modules.append(PREFIX + '.Params')
    names.extend(NS + '.' + n for n in ('Kw',))
    for d in range(128):
        modules.append(f'{PREFIX}.Row{d:03d}')
        names.extend(f'{NS}.{n}_{d:03d}' for n in ('rowPacked', 'row_cert'))
    modules.append(PREFIX + '.RowsAll')
    names.extend(NS + '.' + n for n in ('packedRows', 'rows_eq', 'rows_bound'))
    modules.append(PREFIX + '.PackedTI')
    names.extend(NS + '.' + n for n in ('Ko', 'o_bound', 'target_bound', 'carry_bound', 'packed_cert'))
    modules.append(PREFIX + '.Site')
    names.extend(NS + '.' + n for n in ('ti_eq', 'ti_head0_pos0_token0'))
    return modules, names


def validate_generated(out):
    receipt = json.loads((out / 'generation.json').read_text())
    modules, names = inventory()
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    if receipt['modules'] != modules or receipt['declarations'] != names:
        raise ValueError('packed exact ordered inventory mismatch')
    if receipt['pins'] != verify_pins() or receipt['shapes'] != {k: list(v) for k, v in SHAPES.items()}:
        raise ValueError('packed provenance/dimensions mismatch')
    if receipt['scope'] != {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512}:
        raise ValueError('wrong packed site')
    if set(receipt['coefficients']) != set(SHAPES):
        raise ValueError('all eleven actual raw fields required')
    for key, shape in SHAPES.items():
        axes, rows, width = layout(key)
        item = receipt['coefficients'][key]
        if (item['shape'] != list(shape) or item['count'] != rows * width or
                item['serialized_axes'] != list(axes) or item['vectors'] != rows or item['width'] != width or
                not re.fullmatch(r'[0-9a-f]{64}', item['canonical_flat_integer_json_sha256'])):
            raise ValueError('wrong canonical coefficient inventory: ' + key)
    if receipt['coefficients'] != expected_coefficients():
        raise ValueError('canonical coefficient hashes differ from accepted scalar reference')
    control = receipt['negative']
    d, i = control['coordinate']
    if (control['source_sha256'] != sha(out / 'changed-production-literal.lean') or
            control['field'] != 'Win' or not 0 <= d < 128 or i != 0 or
            control['new'] != control['old'] + 1 or control['nonzero_ovec'] == 0 or
            control['target_component'] != 0):
        raise ValueError('invalid actual changed Win control')
    folder = HERE / PREFIX.replace('.', '/')
    actual = {str(p.relative_to(HERE)) for p in folder.rglob('*.lean')}
    if actual != set(paths) or set(receipt['outputs']) != set(paths):
        raise ValueError('packed source inventory not closed')
    found = []
    for rel in paths:
        p = HERE / rel
        if sha(p) != receipt['outputs'][rel]:
            raise ValueError('packed generated source hash differs: ' + rel)
        ns = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', p.read_text(), re.M)
        if len(ns) != 1:
            raise ValueError('unexpected generated namespace')
        found.extend(ns[0] + '.' + n for n in re.findall(r'^(?:def|theorem) (\w+)\b', p.read_text(), re.M))
    if found != names or len(names) != len(set(names)):
        raise ValueError('actual packed declaration inventory differs')
    return receipt
