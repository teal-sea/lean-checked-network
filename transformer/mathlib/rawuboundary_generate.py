"""Fixed learned-U row127 boundary. No range, other row or complete field mode."""
import json
import sys
from rawpilot_data import HERE, sha
from rawpilot_generate import cloud_only
import rawcu_generate as template
from rawpacked_data import expected_coefficients
from rawuboundary_restore import require, digest

ROW = 127
PREFIX = 'TransformerBridge.RawCorrespondence.UBoundaryGenerated'
NS = 'TransformerBridge.RawCorrespondence.UBoundaryCanonical'
SCOPE = {'U_rows': [127], 'U_components': 113, 'CU_field': False, 'full_hT': False}
MODULES = [PREFIX + '.URow127', PREFIX + '.Control127']
NAMES = [NS + '.' + n for n in ('KU127', 'packedURow_127', 'urow_cert_127', 'changedWeights', 'changed_u_127_zero')]


def row_sources(values):
    """Reuse the accepted signed-pack template, changing only fixed names/coordinate."""
    sources, negative = template.row_sources(values)
    replacements = [(template.MODULES[0], MODULES[0]), (template.MODULES[1], MODULES[1]),
                    (template.NS, NS), ('KU0', 'KU127'), ('packedURow_000', 'packedURow_127'),
                    ('urow_cert_000', 'urow_cert_127'), ('changed_u_zero', 'changed_u_127_zero'),
                    ('changedWeights.U 0', 'changedWeights.U 127'), ('weights.U 0', 'weights.U 127'),
                    ('d = 0 ∧ k = 0', 'd = 127 ∧ k = 0')]
    def adapt(text):
        for old, new in replacements: text = text.replace(old, new)
        return text
    return {m: adapt(s) for m, s in zip(MODULES, sources.values())}, adapt(negative)


def production_row():
    cloud_only()
    # Same authenticated parser and original serialized U[k][d] layout as accepted row0.
    from rawcu_restore import pin
    expected = {r['module']: r['source_sha256'] for r in pin()['packed_objects']}
    columns, hashes = [], {}
    for start, count in [(0, 64), (64, 49)]:
        module = 'TransformerBridge.RawPacked.Generated.U' + str(start // 64).zfill(3)
        path = HERE / (module.replace('.', '/') + '.lean')
        require(sha(path) == expected[module], 'boundary original U source drift')
        columns += template.parse_columns(path.read_text(), start, count)
        hashes[str(path.relative_to(HERE))] = sha(path)
    canonical = [columns[k][d] for d in range(128) for k in range(113)]
    require(digest(json.dumps(canonical, separators=(',', ':')).encode()) ==
            expected_coefficients()['U']['canonical_flat_integer_json_sha256'], 'boundary U canonical hash/layout')
    return [column[ROW] for column in columns], hashes


def emit(out, check=False):
    cloud_only(); sys.set_int_max_str_digits(0)
    values, hashes = production_row()
    sources, negative = row_sources(values)
    record = {'scope': SCOPE, 'modules': MODULES, 'declarations': NAMES,
              'outputs': {m.replace('.', '/') + '.lean': digest(s.encode()) for m, s in sources.items()},
              'original_U_sources': hashes, 'row_sha256': digest(json.dumps(values, separators=(',', ':')).encode()),
              'negative': {'field': 'U', 'coordinate': [127, 0], 'old': values[0], 'new': values[0] + 1,
                           'delta': 1, 'negative_sha256': digest(negative.encode())}, 'kernel_verdict': 'KERNEL_NOT_RUN'}
    for module, text in sources.items():
        path = HERE / (module.replace('.', '/') + '.lean')
        if not check:
            require(not path.exists(), 'preexisting boundary proof source')
            path.parent.mkdir(parents=True, exist_ok=True); path.write_text(text)
        require(path.read_text() == text, 'boundary proof source differs')
    if not check:
        (out / 'changed-U127.lean').write_text(negative)
        (out / 'generation.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    require(json.loads((out / 'generation.json').read_text()) == record and
            (out / 'changed-U127.lean').read_text() == negative, 'boundary generation/negative differs')
    actual = {str(p.relative_to(HERE)) for p in (HERE / PREFIX.replace('.', '/')).rglob('*.lean')}
    require(actual == set(record['outputs']), 'wrong/extra boundary module inventory')
    return record
