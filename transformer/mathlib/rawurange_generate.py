"""Bounded learned-U row batch, at most four rows in one certificate module."""
import json
import re
import sys
from rawpilot_data import HERE, sha
from rawpilot_generate import cloud_only, source
import rawcu_generate as template
from rawpacked_data import expected_coefficients
from rawcu_restore import require, digest

PREFIX = 'TransformerBridge.RawCorrespondence.URangeGenerated'
NS = 'TransformerBridge.RawCorrespondence.URangeCanonical'


def rows_for(start, count):
    require(type(start) is int and type(count) is int and 1 <= start <= 126 and
            1 <= count <= 4 and start + count <= 127, 'U range requires rows1..126 and count1..4')
    return list(range(start, start + count))


def scope(start, count):
    return {'U_rows': rows_for(start, count), 'U_components': 113, 'CU_field': False, 'full_hT': False}


def inventory(start, count):
    rows = rows_for(start, count); tag = f'{rows[0]:03d}_{rows[-1]:03d}'
    modules = [PREFIX + '.Rows' + tag, PREFIX + '.Control' + tag]
    row_names = [NS + '.' + n for r in rows for n in (f'KU_{r:03d}', f'packedURow_{r:03d}', f'urow_cert_{r:03d}')]
    control_names = [NS + f'.changedWeights_{start:03d}', NS + f'.changed_u_{start:03d}_zero']
    return modules, row_names, control_names


def batch_sources(start, count, values):
    rows = rows_for(start, count)
    require(type(values) is dict and all(type(r) is int for r in values) and list(values) == rows, 'missing/duplicate/extra/gapped/reordered U batch rows')
    modules, _, _ = inventory(start, count); bodies = []; control = negative = None
    for r in rows:
        originals, bad = template.row_sources(values[r])
        replacements = [(template.MODULES[0], modules[0]), (template.MODULES[1], modules[1]), (template.NS, NS),
                        ('KU0', f'KU_{r:03d}'), ('packedURow_000', f'packedURow_{r:03d}'),
                        ('urow_cert_000', f'urow_cert_{r:03d}'), ('changedWeights', f'changedWeights_{r:03d}'),
                        ('changed_u_zero', f'changed_u_{r:03d}_zero'),
                        (f'changedWeights_{r:03d}.U 0', f'changedWeights_{r:03d}.U {r}'),
                        ('weights.U 0', f'weights.U {r}'), ('d = 0 ∧ k = 0', f'd = {r} ∧ k = 0')]
        def adapt(text):
            for old, new in replacements: text = text.replace(old, new)
            return text
        row = adapt(originals[template.MODULES[0]])
        body = row.split('namespace ' + NS + '\n\n', 1)[1].rsplit('\nend ' + NS + '\n', 1)[0]
        bodies.append(body)
        if r == start:
            control = adapt(originals[template.MODULES[1]]); negative = adapt(bad)
    combined = source(['TransformerBridge.RawPacked.Generated.Weights'], NS, '\n'.join(bodies))
    return dict(zip(modules, [combined, control])), negative


def production_rows(start, count):
    rows = rows_for(start, count)  # Reject invalid requests before any production access.
    cloud_only()
    from rawcu_restore import pin
    expected = {r['module']: r['source_sha256'] for r in pin()['packed_objects']}
    columns, hashes = [], {}
    for first, size in [(0, 64), (64, 49)]:
        module = 'TransformerBridge.RawPacked.Generated.U' + str(first // 64).zfill(3)
        path = HERE / (module.replace('.', '/') + '.lean')
        require(sha(path) == expected[module], 'U range canonical source drift')
        columns += template.parse_columns(path.read_text(), first, size)
        hashes[str(path.relative_to(HERE))] = sha(path)
    canonical = [columns[k][d] for d in range(128) for k in range(113)]
    require(digest(json.dumps(canonical, separators=(',', ':')).encode()) ==
            expected_coefficients()['U']['canonical_flat_integer_json_sha256'], 'U range canonical hash/layout')
    return {r: [column[r] for column in columns] for r in rows}, hashes


def emit(out, start, count, check=False):
    rows_for(start, count); cloud_only(); sys.set_int_max_str_digits(0)
    values, hashes = production_rows(start, count)
    sources, negative = batch_sources(start, count, values)
    modules, row_names, control_names = inventory(start, count)
    record = {'scope': scope(start, count), 'modules': modules, 'declarations': row_names + control_names,
              'outputs': {m.replace('.', '/') + '.lean': digest(s.encode()) for m, s in sources.items()},
              'original_U_sources': hashes,
              'row_sha256': {str(r): digest(json.dumps(values[r], separators=(',', ':')).encode()) for r in rows_for(start, count)},
              'negative': {'field': 'U', 'coordinate': [start, 0], 'old': values[start][0], 'new': values[start][0] + 1,
                           'delta': 1, 'negative_sha256': digest(negative.encode())}, 'kernel_verdict': 'KERNEL_NOT_RUN'}
    for module, text in sources.items():
        path = HERE / (module.replace('.', '/') + '.lean')
        if not check:
            require(not path.exists(), 'preexisting U range source')
            path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
        require(path.read_text() == text, 'U range proof source differs')
    if not check:
        (out / 'changed-U-range.lean').write_text(negative)
        (out / 'generation.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    require(json.loads((out / 'generation.json').read_text()) == record and
            (out / 'changed-U-range.lean').read_text() == negative, 'U range receipt/negative differs')
    actual = {str(p.relative_to(HERE)) for p in (HERE / PREFIX.replace('.', '/')).rglob('*.lean')}
    require(actual == set(record['outputs']), 'U range extra/missing module')
    found = [NS + '.' + n for s in sources.values() for n in re.findall(r'^(?:def|theorem) (\w+)', s, re.M)]
    require(found == row_names + control_names, 'U range declaration inventory')
    return record
