"""Tiny fixtures only: emission, exact rename, coverage/provenance/audit red controls.

No Lean/Lake commands; no real frozen packing or numerical network evaluation.
"""
import copy
import json
from pathlib import Path
import tempfile

import row0_receipt as r
from row0_source import check_branches, checks_source, selected
import sync_core


def reject(fn):
    try:
        fn()
    except (ValueError, FileNotFoundError):
        return
    raise AssertionError('negative control accepted')


def write_receipt(root, meta):
    out = root / 'ci-out/cache-codegen'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'manifest.json').write_text(json.dumps(meta))
    for name, key in [('modules', 'modules'), ('sources', 'generated'), ('axioms', 'axioms')]:
        (out / (name + '.txt')).write_text('\n'.join(meta[key]) + '\n')


def main():
    assert [len(sync_core.inventory()), len(sync_core.inventory(support=True)),
            len(sync_core.inventory(True)), len(sync_core.inventory(cached_support=True))] == [3, 4, 30, 6]
    r.coverage([[0, b] for b in range(113)])
    for bad in ([[0, b] for b in range(113) if b != 56],
                [[0, b if b != 56 else 55] for b in range(113)],
                [[1 if b == 56 else 0, b] for b in range(113)],
                [[0, b] for b in reversed(range(113))]):
        reject(lambda: r.coverage(bad))
    check_branches(r.HERE / 'TransformerBridge/Row0Checks.lean')
    # The analytic proof body is exactly the existing Compose body, specialized pointwise.
    compose = (r.HERE / 'Transformer/Compose.lean').read_text()
    proof = compose.split('theorem real_model_adds_mod_113\n', 1)[1]
    proof = proof.split('\n/-- The same at the chosen', 1)[0].split(':= by\n', 1)[1]
    expected_body = proof.removeprefix('  intro a b\n').replace('(hA a b) hclose', 'hA hclose')
    pointwise = (r.HERE / 'TransformerBridge/Pointwise.lean').read_text()
    actual_body = pointwise.split(':= by\n', 1)[1].rsplit('\nend Transformer', 1)[0]
    assert actual_body.strip() == expected_body.strip()

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        branch = root / 'Row0Checks.lean'
        for bad in (checks_source().replace('cached_pilot_0_56', 'cached_pilot_0_55'),
                    checks_source().replace('  · exact TransformerCore.Net.Cached.cached_pilot_0_56\n', ''),
                    checks_source().replace('CachedPair0_56', 'CachedPair1_56')):
            branch.write_text(bad)
            reject(lambda: check_branches(branch))
        # Fourteen tiny signed/empty vectors, never the real 2346-vector packing.
        g = r.generator()
        original_groups = g.groups
        g.groups = lambda heads=1, tokens=2, grows=2: original_groups(heads, tokens, grows)
        names = [n for ns in g.groups().values() for n in ns] + ['CI', 'CU']
        vectors = {n: ([], [-7], [3, -2, 1])[i % 3] for i, n in enumerate(names)}
        origins = {n: 'W.Fixture' for n in names}
        meta = g.emit(root, vectors, origins, heads=1, tokens=2, grows=2, row0=True)
        meta.update({'base': str(g.BASE), 'inputs': g.verify_inputs(r.CORE, r.CORE / 'cached-inputs.sha256'),
                     'generator_sha256': r.sha(r.CORE / 'gen_cached.py'),
                     'input_manifest_sha256': r.sha(r.CORE / 'cached-inputs.sha256'),
                     'generic_sha256': r.sha(r.CORE / 'Transformer/Cached.lean'),
                     'baseline_source': '9a7f6d6a5ce7c5be37012c45144ddd8548e5b9a8'})
        meta['pairs'] = [list(p) for p in meta['pairs']]
        meta['outputs'] = {rel: r.sha(root / rel) for rel in meta['generated']}
        original_generator = r.generator
        r.generator = lambda: g
        try:
            write_receipt(root, meta)
            assert r.validate_codegen(root) == meta
            names_selected = selected(meta)
            good = ''.join(f"'{n}' does not depend on any axioms\n" for n in names_selected)
            assert r.check_axioms(good, names_selected) == len(names_selected)
            standard = good.replace('does not depend on any axioms',
                                    'depends on axioms: [propext, Classical.choice, Quot.sound]')
            assert r.check_axioms(standard, names_selected) == len(names_selected)
            for bad in (good.replace(names_selected[-1], names_selected[0]),
                        '\n'.join(good.splitlines()[:-1]), good + 'unexpected\n',
                        good.replace('does not depend on any axioms', 'depends on axioms: [bad]', 1)):
                reject(lambda: r.check_axioms(bad, names_selected))
            for key, value in [('pairs', [p for p in meta['pairs'] if p != [0, 56]]),
                               ('pairs', [[1, 56] if p == [0, 56] else p for p in meta['pairs']]),
                               ('pairs', [[0, 55] if p == [0, 56] else p for p in meta['pairs']]),
                               ('generator_sha256', '0' * 64), ('base', '1'),
                               ('modules', meta['modules'][:-1]),
                               ('axioms', meta['axioms'][:-1]),
                               ('generic_sha256', '0' * 64), ('vector_count', 999)]:
                bad = copy.deepcopy(meta)
                bad[key] = value
                write_receipt(root, bad)
                reject(lambda: r.validate_codegen(root))
            write_receipt(root, meta)
            extra = root / 'Transformer/Net/CachedPair1_56.lean'
            extra.write_text('-- unrelated row fixture\n')
            reject(lambda: r.validate_codegen(root))
            reject(lambda: g.emit(root, vectors, origins, heads=1, tokens=2, grows=2, row0=True))
            extra.unlink()
            middle = root / 'Transformer/Net/CachedPair0_56.lean'
            original = middle.read_bytes()
            altered = original.replace(b'E2 0 56 = true', b'E2 0 55 = true', 1)
            assert altered != original
            middle.write_bytes(altered)
            reject(lambda: r.validate_codegen(root))
            middle.unlink()
            reject(lambda: r.validate_codegen(root))
            middle.write_bytes(original)
            # Validate a full import topology using small fixture modules, without frozen numerics.
            fixture_base = root / 'closure'
            for module, _, _, source, _ in sync_core.inventory(True):
                path = fixture_base / (module.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('\n'.join(line for line in source.decode().splitlines()
                                          if line.startswith('import ')) + '\n')
            for rel in meta['generated']:
                path = fixture_base / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((root / rel).read_bytes())
            for module in ('Cached', 'CachedFixture'):
                (fixture_base / f'Transformer/{module}.lean').write_bytes(
                    (r.CORE / f'Transformer/{module}.lean').read_bytes())
            (fixture_base / 'Transformer/Net/W/Fixture.lean').write_text('namespace Transformer\nend Transformer\n')
            old_base, old_allowed = sync_core.BASE, sync_core.ALLOWED
            old_validate = r.validate_codegen
            sync_core.BASE = fixture_base
            sync_core.ALLOWED = {*old_allowed, 'Transformer.Net.W.Fixture'}
            r.validate_codegen = lambda _: meta
            try:
                rows = sync_core.inventory(row0=True)
                modules = [row[0] for row in rows]
                for index, (module, _, _, source, target) in enumerate(rows):
                    assert target == sync_core.re.sub(rb'\bTransformer\b', b'TransformerCore', source)
                    for line in source.decode().splitlines():
                        if line.startswith('import '):
                            assert line[7:] in modules[:index], (module, line)
                victim = fixture_base / 'Transformer/Net/CachedPair0_56.lean'
                victim.write_text('import Transformer.Net.Pair1_56\n')
                reject(lambda: sync_core.inventory(row0=True))
                for import_line in (' import Transformer.Net.Cached', 'public import Transformer.Net.Cached',
                                    'import Transformer.Net.Cached Transformer.Model'):
                    victim.write_text(import_line + '\n')
                    reject(lambda: sync_core.inventory(row0=True))
            finally:
                sync_core.BASE, sync_core.ALLOWED = old_base, old_allowed
                r.validate_codegen = old_validate
        finally:
            r.generator = original_generator
    print('ok: ROW0 tiny fixtures; missing/duplicate/wrong-row/middle alteration, source and audit '
          'controls; explicit 113 branches; closed exact rename/topology. NO kernel evidence.')


if __name__ == '__main__':
    main()
