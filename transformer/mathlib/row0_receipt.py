"""Closed ROW0/113 generation receipt checks. No model arithmetic or Lean execution."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
CORE = HERE.parent / 'lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generator():
    spec = importlib.util.spec_from_file_location('gen_cached', CORE / 'gen_cached.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def coverage(pairs):
    if (type(pairs) is not list or
            any(type(p) is not list or len(p) != 2 or any(type(x) is not int for x in p) for p in pairs) or
            pairs != [[0, b] for b in range(113)]):
        raise ValueError('expected exactly ordered unique ROW0/113 coverage')


def validate_codegen(root):
    g = generator()
    receipt = json.loads((root / 'ci-out/cache-codegen/manifest.json').read_text())
    coverage(receipt['pairs'])
    if receipt['generator_sha256'] != sha(CORE / 'gen_cached.py'):
        raise ValueError('generator receipt mismatch')
    if receipt['input_manifest_sha256'] != sha(CORE / 'cached-inputs.sha256'):
        raise ValueError('input manifest receipt mismatch')
    if receipt['inputs'] != g.verify_inputs(CORE, CORE / 'cached-inputs.sha256'):
        raise ValueError('frozen input receipt mismatch')
    if receipt['generic_sha256'] != sha(CORE / 'Transformer/Cached.lean'):
        raise ValueError('cached support receipt mismatch')
    if receipt["base"] != str(g.BASE) or receipt["baseline_source"] != "9a7f6d6a5ce7c5be37012c45144ddd8548e5b9a8":
        raise ValueError("frozen generation base/baseline mismatch")
    units, axioms = [], []
    vector_count, unit_count = 0, 0
    for key, names in [*g.groups().items(), ('Bias', ['CI', 'CU'])]:
        vector_count += len(names)
        unit_count += (len(names) + g.CHUNK - 1) // g.CHUNK
        for i in range(0, len(names), g.CHUNK):
            units.append(f'Transformer.Net.CachedUnits.{key}_{i // g.CHUNK:03d}')
            axioms.extend('Transformer.Net.Cached.eq_' + n for n in names[i:i + g.CHUNK])
        if key != 'Bias':
            units.append(f'Transformer.Net.CachedUnits.{key}')
            axioms.append('Transformer.Net.Cached.eq_' + key)
    units.append('Transformer.Net.Cached')
    axioms.extend('Transformer.Net.Cached.eq_' + k for k in ('TI0', 'TI1', 'TU0', 'TU1'))
    axioms.append('Transformer.Net.Cached.cache_eq')
    pairs = [f'Transformer.Net.CachedPair0_{b}' for b in range(113)]
    for b in range(113):
        axioms.extend((f'Transformer.Net.Cached.cached_value_0_{b}',
                       f'Transformer.Net.Cached.cached_pilot_0_{b}'))
    sources = [m.replace('.', '/') + '.lean' for m in units + pairs]
    actual_pairs = {str(p.relative_to(root)) for p in (root / 'Transformer/Net').glob('CachedPair*.lean')}
    if actual_pairs != set(sources[-113:]):
        raise ValueError('literal file coverage is not exactly ROW0/113')
    actual_units = {str(p.relative_to(root)) for p in (root / 'Transformer/Net/CachedUnits').glob('*.lean')}
    if actual_units != {s for s in sources if s.startswith('Transformer/Net/CachedUnits/')}:
        raise ValueError('packing unit file inventory differs')
    if receipt['modules'] != units or receipt['generated'] != sources or receipt['axioms'] != axioms:
        raise ValueError('closed generated inventory mismatch')
    if (receipt['vector_count'], receipt['certificate_units'], receipt['max_vectors_per_unit']) != (vector_count, unit_count, g.CHUNK):
        raise ValueError('packing inventory mismatch')
    if set(receipt['outputs']) != set(sources):
        raise ValueError('generated hash inventory mismatch')
    for rel in sources:
        if receipt['outputs'][rel] != sha(root / rel):
            raise ValueError('generated source hash mismatch: ' + rel)
    for name, values in [('modules', units), ('sources', sources), ('axioms', axioms)]:
        if (root / f'ci-out/cache-codegen/{name}.txt').read_text() != '\n'.join(values) + '\n':
            raise ValueError('generated list mismatch: ' + name)
    return receipt


def check_axioms(text, expected):
    names = []
    for line in text.splitlines():
        m = re.fullmatch(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        if not m or (m[3] is not None and (not m[3] or not set(m[3].split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'})):
            raise ValueError('unexpected/nonstandard axiom record: ' + line)
        names.append(m[1])
    if names != expected or len(names) != len(set(names)):
        raise ValueError('exact selected axiom names/count/order mismatch')
    return len(names)
