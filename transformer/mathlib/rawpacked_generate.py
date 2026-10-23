#!/usr/bin/env python3
"""Separate packed candidate; only public manual Actions may evaluate the checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

import rawpilot_generate as scalar
from rawpilot_generate import cloud_only, literal, vector
from rawpacked_data import (HERE, ROOT, PREFIX, NS, SHAPES, CHUNK, CERT_CHUNK,
                            inventory, layout, sha, verify_pins, expected_coefficients)


def source(imports, namespace, body):
    return scalar.source(imports, namespace,
        ('' if namespace.endswith('.Data') else
         'open TransformerBridge.RawPilot TransformerBridge.RawPacked\n\n') + body)


def pack_int(values):
    """Witness only; row_cert in Lean independently evaluates original Win coordinates."""
    acc = 0
    for value in reversed(values):
        acc = int(value) + (acc << 208)
    return acc


def row_body(d, values):
    return (f'def rowPacked_{d:03d} : Int := {literal(pack_int(values))}\n\n' +
        f'theorem row_cert_{d:03d} :\n' +
        f'    pack (fun i : Fin 512 => weights.Win {d} i) = rowPacked_{d:03d} ∧\n' +
        f'      (∀ i : Fin 512, -(Kw : Int) ≤ weights.Win {d} i ∧ weights.Win {d} i ≤ Kw) := by\n' +
        '  decide +kernel\n')


def rows_all_source():
    imports = [f'{PREFIX}.Row{d:03d}' for d in range(128)]
    body = 'def packedRows (d : Fin 128) : Int := TransformerCore.nth 0 ['
    body += ', '.join(f'rowPacked_{d:03d}' for d in range(128)) + '] d.val\n\n'
    body += '''theorem rows_eq (d : Fin 128) : pack (weights.Win d) = packedRows d := by
  fin_cases d
'''
    body += ''.join(f'  · exact row_cert_{d:03d}.1\n' for d in range(128))
    body += '''
theorem rows_bound (d : Fin 128) (i : Fin 512) :
    -(Kw : Int) ≤ weights.Win d i ∧ weights.Win d i ≤ Kw := by
  fin_cases d
'''
    body += ''.join(f'  · exact row_cert_{d:03d}.2 i\n' for d in range(128))
    return source(imports, NS, body)


def packed_source(Ko):
    return source([PREFIX + '.RowsAll', PREFIX + '.Vectors', 'TransformerCore.Net.W.TI0_0'], NS,
        f'def Ko : Nat := {Ko}\n\n' + '''theorem o_bound (d : Fin 128) : -(Ko : Int) ≤ proposedO d ∧ proposedO d ≤ Ko := by
  revert d
  decide +kernel

theorem target_bound (i : Fin 512) :
    -((128 * Ko * Kw : Nat) : Int) ≤ TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i ∧
      TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i ≤ (128 * Ko * Kw : Nat) := by
  revert i
  decide +kernel

theorem carry_bound : 2 * (128 * Ko * Kw) < TransformerCore.B := by decide +kernel

theorem packed_cert : contract proposedO packedRows =
    pack (fun i : Fin 512 => TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i) := by
  decide +kernel
''')


def site_source():
    return source([PREFIX + '.PackedTI', PREFIX + '.OAll', 'TransformerCore.Net.Weights'], NS,
        '''theorem ti_eq (i : Fin 512) :
    contract proposedO (fun d => weights.Win d i) =
      TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i := by
  exact contract_eq_of_packed proposedO weights.Win packedRows
    (fun k : Fin 512 => TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 k)
    Ko Kw rows_eq o_bound rows_bound target_bound carry_bound packed_cert i

/-- The exact unconditional full production-site statement; no bound hypothesis remains. -/
theorem ti_head0_pos0_token0 (i : Fin 512) :
    (weights.rawTables 256).TI 0 0 0 i =
      (TransformerBridge.toTables TransformerCore.Net.tab).TI 0 0 0 i := by
  change (weights.rawTables 256).TI 0 0 0 i =
    TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i
  exact (TI_of_ovec weights 256 0 0 0 proposedO o_eq (by decide) i).trans (ti_eq i)
''')


def emit(weights, v, o, put):
    # Same all-eleven canonical storage and coordinate semantics as the accepted scalar producer.
    for key, rows in weights.items():
        chunks = []
        for start in range(0, len(rows), CHUNK):
            module = f'{PREFIX}.{key}{start // CHUNK:03d}'
            chunks.append(module)
            body = ''.join(f'def {key}_{i} : List Int := {vector(rows[i])}\n'
                           for i in range(start, min(start + CHUNK, len(rows))))
            put(module, source(['TransformerCore.Model'], NS + '.Data', body))
        body = f'def {key} : List (List Int) := [' + ', '.join(f'{key}_{i}' for i in range(len(rows))) + ']\n'
        put(PREFIX + '.' + key, source(chunks, NS + '.Data', body))
    put(PREFIX + '.Weights', source(['TransformerBridge.RawPackedSupport'] +
        [PREFIX + '.' + k for k in weights], NS, scalar.weight_body()))
    put(PREFIX + '.Vectors', source(['TransformerBridge.RawPackedSupport'], NS,
        f'def proposedV (l : Fin 32) : Int := TransformerCore.nth 0 {vector(v)} l.val\n\n' +
        f'def proposedO (d : Fin 128) : Int := TransformerCore.nth 0 {vector(o)} d.val\n'))
    for stage, count in (('V', 32), ('O', 128)):
        for start in range(0, count, CERT_CHUNK):
            body = ''
            for i in range(start, start + CERT_CHUNK):
                lhs, rhs = scalar.cert_type(stage, i)
                body += f'theorem {stage.lower()}_cert_{i:03d} :\n    {lhs} = {rhs} := by decide +kernel\n\n'
            put(f'{PREFIX}.{stage}{start // CERT_CHUNK:03d}',
                source([PREFIX + '.Weights', PREFIX + '.Vectors'], NS, body))
        # Reuse the accepted V/O proofs with only module/namespace relocation.
        text = scalar.all_source(stage, count).replace(scalar.PREFIX, PREFIX).replace(scalar.NS, NS)
        text = text.replace('namespace ' + NS + '\n',
            'namespace ' + NS + '\n\nopen TransformerBridge.RawPilot\n')
        put(PREFIX + '.' + stage + 'All', text)
    Ko = max(abs(int(x)) for x in o)
    Kw = max(abs(int(x)) for column in weights['Win'] for x in column)
    put(PREFIX + '.Params', source(['TransformerBridge.RawPackedSupport'], NS,
        f'def Kw : Nat := {Kw}\n'))
    # Existing storage is columns[i][d]. Every certificate reads weights.Win d i,
    # so the kernel checks the coordinate correspondence instead of trusting transpose.
    for d in range(128):
        values = [column[d] for column in weights['Win']]
        put(f'{PREFIX}.Row{d:03d}', source([PREFIX + '.Weights', PREFIX + '.Params'], NS,
            row_body(d, values)))
    put(PREFIX + '.RowsAll', rows_all_source())
    put(PREFIX + '.PackedTI', packed_source(Ko))
    put(PREFIX + '.Site', site_source())


def main(check=False):
    cloud_only()
    sys.set_int_max_str_digits(0)
    pins = verify_pins()
    # Verify the original closed sixteen-file input set without generating any tables/caches.
    sys.path.insert(0, str(ROOT / 'transformer/lean'))
    import gen_cached
    frozen = gen_cached.verify_inputs(ROOT / 'transformer/lean', ROOT / 'transformer/lean/cached-inputs.sha256')
    sys.path.insert(0, str(ROOT / 'transformer'))
    import int_transformer as it
    import numpy as np
    learned = it.load_weights(ROOT / 'transformer/runs/best.npz')
    if list(learned) != list(SHAPES) or any(learned[k].shape != SHAPES[k] for k in SHAPES):
        raise ValueError('checkpoint must supply all eleven exact original shapes')
    if any(not np.isfinite(learned[k]).all() for k in SHAPES):
        raise ValueError('nonfinite checkpoint coefficient')
    quantized = it.quantise(learned, 8)
    if (quantized['q'], quantized['S'], quantized['t']) != (8, 256, 32):
        raise ValueError('wrong quantization scales')
    serialized, coefficients = {}, {}
    for key in SHAPES:
        a = quantized[key]
        if a.shape != SHAPES[key] or a.dtype != object or any(type(n) is not int for n in a.flat):
            raise ValueError('noncanonical integer coefficient tensor: ' + key)
        axes, rows, width = layout(key)
        arranged = a.transpose(axes).reshape(rows, width)
        if not np.array_equal(arranged.reshape(tuple(SHAPES[key][i] for i in axes)).transpose(np.argsort(axes)), a):
            raise ValueError('raw serialization coordinate roundtrip failed: ' + key)
        serialized[key] = [[int(n) for n in row] for row in arranged]
        canonical = json.dumps([int(n) for n in a.flat], separators=(',', ':')).encode()
        coefficients[key] = {'shape': list(a.shape), 'count': int(a.size),
                             'canonical_flat_integer_json_sha256': hashlib.sha256(canonical).hexdigest(),
                             'serialized_axes': list(axes), 'vectors': rows, 'width': width}
    if coefficients != expected_coefficients():
        raise ValueError('canonical eleven-field hashes differ from accepted scalar reference')
    # Exactly the single requested site. No scores, other heads/tokens, logits or build_tables.
    x = quantized['tok'][0] + quantized['pos'][0]
    v = x @ quantized['WV'][0]
    o = v @ quantized['WO'][0]
    outputs = {}

    def put(module, text):
        rel = module.replace('.', '/') + '.lean'
        path = HERE / rel
        data = text.encode()
        if check:
            if path.read_bytes() != data:
                raise ValueError('nonreproducible raw-packed-pilot source: ' + rel)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        outputs[rel] = hashlib.sha256(data).hexdigest()

    emit(serialized, v, o, put)
    modules, declarations = inventory()
    out = HERE / 'rawpacked-out'
    out.mkdir(exist_ok=True)
    # Change one actual Win[d,0] integer literal; choose a nonzero certified O coordinate.
    d = next(i for i, value in enumerate(o) if value != 0)
    old = int(quantized['Win'][d, 0])
    new = old + 1
    negative = source([PREFIX + '.Site'], NS,
        'def changedWeights : Transformer.Weights := { weights with\n' +
        f'  Win := fun d i => if d.val = {d} ∧ i.val = 0 then {literal(new)} else weights.Win d i }}\n\n' +
        'example : (changedWeights.rawTables 256).TI 0 0 0 0 =\n' +
        '    (TransformerBridge.toTables TransformerCore.Net.tab).TI 0 0 0 0 := by\n' +
        '  have ho : ∀ d, changedWeights.ovec 0 0 0 d = proposedO d := by\n' +
        '    intro d\n' +
        '    exact o_eq d\n' +
        '  change (changedWeights.rawTables 256).TI 0 0 0 0 =\n' +
        '    TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 0\n' +
        '  rw [TI_of_ovec changedWeights 256 0 0 0 proposedO ho (by decide) 0]\n' +
        '  decide +kernel\n')
    negpath = out / 'changed-production-literal.lean'
    if check:
        if negpath.read_text() != negative:
            raise ValueError('changed-literal control is not reproducible')
    else:
        negpath.write_text(negative)
    receipt = {'scope': {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512},
               'pins': pins, 'frozen_inputs': frozen, 'shapes': {k: list(v) for k, v in SHAPES.items()},
               'coefficients': coefficients, 'modules': modules, 'declarations': declarations, 'outputs': outputs,
               'negative': {'source_sha256': sha(negpath), 'field': 'Win', 'coordinate': [d, 0],
                            'old': old, 'new': new, 'nonzero_ovec': int(o[d]), 'target_component': 0},
               'numpy': np.__version__, 'python': sys.version,
               'quantization': 'unchanged int_transformer.load_weights and quantise(q=8); rnd=floor(v+0.5)',
               'kernel_verdict': 'NOT_RUN'}
    dest = out / 'generation.json'
    if check:
        if json.loads(dest.read_text()) != receipt:
            raise ValueError('generation receipt not reproducible')
    else:
        dest.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(f'raw-packed-pilot generation reproducible={check} fields=11 coefficients={sum(v["count"] for v in coefficients.values())} '
          f'certificates=32+128+128rows+1packed modules={len(modules)} declarations={len(declarations)}; Lean NOT_RUN')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    main(parser.parse_args().check)
