#!/usr/bin/env python3
"""Emit all canonical q8 raw coefficients and ONE full TI site, in public Actions only.

Python vectors are witnesses. Every arithmetic equality is separately kernel-certified.
Never calls build_tables; never reads target table values as raw coefficients.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

from rawpilot_data import (CERT_CHUNK, CHUNK, HERE, NS, PREFIX, ROOT, SHAPES,
                           STAGES, inventory, layout, sha, verify_pins)


def cloud_only():
    if os.environ.get('GITHUB_ACTIONS') != 'true' or os.environ.get('GITHUB_EVENT_NAME') != 'workflow_dispatch':
        raise ValueError('real raw coefficient generation is public manual Actions only')
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    if event['repository']['private'] is not False:
        raise ValueError('free standard public repository required')


def literal(n):
    n = int(n)
    return f'(.ofNat {n})' if n >= 0 else f'(.negSucc {-n - 1})'


def vector(values):
    return '[' + ', '.join(literal(n) for n in values) + ']'


def source(imports, namespace, body):
    return (''.join('import ' + m + '\n' for m in imports) +
            '\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n' +
            'namespace ' + namespace + '\n\n' + body + '\nend ' + namespace + '\n')


def weight_body():
    return '''def weights : Transformer.Weights where
  tok := fun tk d => TransformerCore.nth 0 (TransformerCore.nth [] Data.tok tk.val) d.val
  pos := fun j d => TransformerCore.nth 0 (TransformerCore.nth [] Data.pos j.val) d.val
  WQ := fun h d l => TransformerCore.nth 0 (TransformerCore.nth [] Data.WQ (h.val * 32 + l.val)) d.val
  WK := fun h d l => TransformerCore.nth 0 (TransformerCore.nth [] Data.WK (h.val * 32 + l.val)) d.val
  WV := fun h d l => TransformerCore.nth 0 (TransformerCore.nth [] Data.WV (h.val * 32 + l.val)) d.val
  WO := fun h l d => TransformerCore.nth 0 (TransformerCore.nth [] Data.WO (h.val * 128 + d.val)) l.val
  Win := fun d i => TransformerCore.nth 0 (TransformerCore.nth [] Data.Win i.val) d.val
  bin := fun i => TransformerCore.nth 0 (TransformerCore.nth [] Data.bin 0) i.val
  Wout := fun i d => TransformerCore.nth 0 (TransformerCore.nth [] Data.Wout i.val) d.val
  bout := fun d => TransformerCore.nth 0 (TransformerCore.nth [] Data.bout 0) d.val
  U := fun d k => TransformerCore.nth 0 (TransformerCore.nth [] Data.U k.val) d.val
'''


def cert_type(stage, index):
    if stage == 'V':
        return (f'contract (weights.xhat 0 0) (fun d => weights.WV 0 d {index})', f'proposedV {index}')
    if stage == 'O':
        return (f'contract proposedV (fun l => weights.WO 0 l {index})', f'proposedO {index}')
    return (f'contract proposedO (fun d => weights.Win d {index})',
            f'TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 {index}')


def all_source(stage, count):
    chunks = [f'{PREFIX}.{stage}{i:03d}' for i in range(count // CERT_CHUNK)]
    if stage == 'V':
        pre = '''theorem v_eq (l : Fin 32) : weights.vvec 0 0 0 l = proposedV l := by
  change (∑ d, weights.xhat 0 0 d * weights.WV 0 d l) = proposedV l
  rw [← contract_eq]
  fin_cases l
'''
    elif stage == 'O':
        chunks.append(PREFIX + '.VAll')
        pre = '''theorem o_eq (d : Fin 128) : weights.ovec 0 0 0 d = proposedO d := by
  rw [ovec_of_vvec weights 0 0 0 proposedV v_eq]
  fin_cases d
'''
    else:
        pre = '''theorem ti_eq (i : Fin 512) :
    contract proposedO (fun d => weights.Win d i) =
      TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i := by
  fin_cases i
'''
    pre += ''.join(f'  · exact {stage.lower()}_cert_{i:03d}\n' for i in range(count))
    return source(chunks, NS, pre)


def site_source():
    return source([PREFIX + '.TIAll', PREFIX + '.OAll', 'TransformerCore.Net.Weights'], NS, '''/-- All 512 components at the production site consumed by Bridge.toTables. -/
theorem ti_head0_pos0_token0 (i : Fin 512) :
    (weights.rawTables 256).TI 0 0 0 i =
      (TransformerBridge.toTables TransformerCore.Net.tab).TI 0 0 0 i := by
  change (weights.rawTables 256).TI 0 0 0 i =
    TransformerCore.nth 0 TransformerCore.Net.TI0_0_0 i
  exact (TI_of_ovec weights 256 0 0 0 proposedO o_eq (by decide) i).trans (ti_eq i)
''')


def emit(weights, v, o, put):
    # This function also supports tiny serialization fixtures; production dimensions are checked in main.
    for key, values in weights.items():
        rows = values
        chunks = []
        for start in range(0, len(rows), CHUNK):
            module = f'{PREFIX}.{key}{start // CHUNK:03d}'
            chunks.append(module)
            body = ''.join(f'def {key}_{i} : List Int := {vector(rows[i])}\n'
                           for i in range(start, min(start + CHUNK, len(rows))))
            put(module, source(['TransformerCore.Model'], NS + '.Data', body))
        body = f'def {key} : List (List Int) := [' + ', '.join(f'{key}_{i}' for i in range(len(rows))) + ']\n'
        put(PREFIX + '.' + key, source(chunks, NS + '.Data', body))
    put(PREFIX + '.Weights', source(['TransformerBridge.RawPilotSupport'] +
                                   [PREFIX + '.' + k for k in weights], NS, weight_body()))
    put(PREFIX + '.Vectors', source(['TransformerBridge.RawPilotSupport'], NS,
        f'def proposedV (l : Fin 32) : Int := TransformerCore.nth 0 {vector(v)} l.val\n\n' +
        f'def proposedO (d : Fin 128) : Int := TransformerCore.nth 0 {vector(o)} d.val\n'))
    for stage, count in STAGES:
        for start in range(0, count, CERT_CHUNK):
            imports = [PREFIX + '.Weights', PREFIX + '.Vectors']
            if stage == 'TI':
                imports.append('TransformerCore.Net.W.TI0_0')
            body = ''
            for i in range(start, start + CERT_CHUNK):
                lhs, rhs = cert_type(stage, i)
                body += f'theorem {stage.lower()}_cert_{i:03d} :\n    {lhs} = {rhs} := by decide +kernel\n\n'
            put(f'{PREFIX}.{stage}{start // CERT_CHUNK:03d}', source(imports, NS, body))
        put(f'{PREFIX}.{stage}All', all_source(stage, count))
    put(PREFIX + '.Site', site_source())


def main(check=False):
    cloud_only()
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
                raise ValueError('nonreproducible raw-pilot source: ' + rel)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        outputs[rel] = hashlib.sha256(data).hexdigest()

    emit(serialized, v, o, put)
    modules, declarations = inventory()
    out = HERE / 'rawpilot-out'
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
    print(f'raw-pilot generation reproducible={check} fields=11 coefficients={sum(v["count"] for v in coefficients.values())} '
          f'certificates=32+128+512 modules={len(modules)} declarations={len(declarations)}; Lean NOT_RUN')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    main(parser.parse_args().check)
