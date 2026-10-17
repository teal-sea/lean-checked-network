"""Closed raw-pilot inventory/provenance. Importing this file performs no numerics."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PREFIX = 'TransformerBridge.RawPilot.Generated'
NS = 'TransformerBridge.RawPilot'
SHAPES = {'tok': (114, 128), 'pos': (3, 128), 'WQ': (4, 128, 32),
          'WK': (4, 128, 32), 'WV': (4, 128, 32), 'WO': (4, 32, 128),
          'Win': (128, 512), 'bin': (512,), 'Wout': (512, 128),
          'bout': (128,), 'U': (128, 113)}
# Serialization changes layout only. Original tensor coordinate semantics are preserved.
AXES = {'WQ': (0, 2, 1), 'WK': (0, 2, 1), 'WV': (0, 2, 1), 'WO': (0, 2, 1),
        'Win': (1, 0), 'U': (1, 0)}
CHUNK = 64
CERT_CHUNK = 16
STAGES = (('V', 32), ('O', 128), ('TI', 512))
SUPPORT_NAMES = [NS + '.' + n for n in
                 ('sumN', 'sumN_eq', 'contract', 'contract_eq', 'ovec_of_vvec', 'TI_of_ovec')]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_pins():
    pins = json.loads((HERE / 'RawPilot-pins.json').read_text())
    for rel, digest in pins.items():
        if sha(ROOT / rel) != digest:
            raise ValueError('raw-pilot pinned input changed: ' + rel)
    if (HERE / 'lean-toolchain').read_text() != 'leanprover/lean4:v4.35.0\n':
        raise ValueError('wrong compiler pin')
    return pins


def layout(key):
    shape = SHAPES[key]
    axes = AXES.get(key, tuple(range(len(shape))))
    arranged = tuple(shape[i] for i in axes)
    width = arranged[-1]
    rows = 1
    for n in arranged[:-1]:
        rows *= n
    return axes, rows, width


def inventory():
    modules, names = [], []
    for key in SHAPES:
        _, rows, _ = layout(key)
        for start in range(0, rows, CHUNK):
            modules.append(f'{PREFIX}.{key}{start // CHUNK:03d}')
            names.extend(f'{NS}.Data.{key}_{i}' for i in range(start, min(start + CHUNK, rows)))
        modules.append(f'{PREFIX}.{key}')
        names.append(f'{NS}.Data.{key}')
    modules.extend([PREFIX + '.Weights', PREFIX + '.Vectors'])
    names.extend(NS + '.' + n for n in ('weights', 'proposedV', 'proposedO'))
    for stage, count in STAGES:
        for start in range(0, count, CERT_CHUNK):
            modules.append(f'{PREFIX}.{stage}{start // CERT_CHUNK:03d}')
            names.extend(f'{NS}.{stage.lower()}_cert_{i:03d}' for i in range(start, start + CERT_CHUNK))
        modules.append(f'{PREFIX}.{stage}All')
        names.append(f'{NS}.{stage.lower()}_eq')
    modules.append(PREFIX + '.Site')
    names.append(NS + '.ti_head0_pos0_token0')
    return modules, names


def validate_generated(out):
    receipt = json.loads((out / 'generation.json').read_text())
    modules, names = inventory()
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    if receipt['modules'] != modules or receipt['declarations'] != names:
        raise ValueError('raw-pilot exact ordered module/declaration inventory mismatch')
    if receipt['pins'] != verify_pins() or receipt['shapes'] != {k: list(v) for k, v in SHAPES.items()}:
        raise ValueError('raw-pilot provenance or dimensions mismatch')
    if receipt['scope'] != {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512}:
        raise ValueError('wrong raw-pilot site')
    if set(receipt['coefficients']) != set(SHAPES):
        raise ValueError('missing actual raw weight field')
    for key, shape in SHAPES.items():
        axes, rows, width = layout(key)
        coefficient = receipt['coefficients'][key]
        if (coefficient['shape'] != list(shape) or coefficient['count'] != rows * width or
                coefficient['serialized_axes'] != list(axes) or coefficient['vectors'] != rows or
                coefficient['width'] != width or not re.fullmatch(
                    r'[0-9a-f]{64}', coefficient['canonical_flat_integer_json_sha256'])):
            raise ValueError('incorrect canonical coefficient inventory: ' + key)
    control = receipt['negative']
    d, i = control['coordinate']
    if (control['source_sha256'] != sha(out / 'changed-production-literal.lean') or
            control['field'] != 'Win' or not 0 <= d < 128 or i != 0 or
            control['new'] != control['old'] + 1 or control['nonzero_ovec'] == 0 or
            control['target_component'] != 0):
        raise ValueError('invalid changed production literal control')
    expected = set(paths)
    actual = {str(p.relative_to(HERE)) for p in (HERE / 'TransformerBridge/RawPilot/Generated').glob('*.lean')}
    if actual != expected or set(receipt['outputs']) != expected:
        raise ValueError('raw-pilot generated file inventory mismatch')
    found = []
    for rel in paths:
        p = HERE / rel
        if sha(p) != receipt['outputs'][rel]:
            raise ValueError('raw-pilot generated hash mismatch: ' + rel)
        text = p.read_text()
        # Emission has exactly one namespace and only plain def/theorem declarations.
        ns = re.findall(r'^namespace ([A-Za-z0-9_.]+)$', text, re.M)
        if len(ns) != 1:
            raise ValueError('unexpected generated namespace')
        found.extend(ns[0] + '.' + n for n in re.findall(r'^(?:def|theorem) (\w+)\b', text, re.M))
    if found != names or len(names) != len(set(names)):
        raise ValueError('actual generated declaration coverage differs')
    return receipt
