#!/usr/bin/env python3
"""Exact source mirror; no Lean evaluation. Frozen numeric mirrors are CI outputs only."""
import argparse
import hashlib
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'lean'
SEEDS = ('Transformer.Model', 'Transformer.Fast', 'Transformer.Equiv')
BOUNDS = ('Transformer.BoundsLib', 'Transformer.Net.Table', 'Transformer.Net.Cols')
# Closed scope: never follow row/pair/Cached imports or silently expand the proof input.
ALLOWED = set(SEEDS + BOUNDS + ('Transformer.Net.Weights',))
ALLOWED.update('Transformer.Net.W.' + x for x in
               ('TI0_0', 'TI0_1', 'TI0_2', 'TI0_3', 'TI1_0', 'TI1_1', 'TI1_2', 'TI1_3', 'TU0', 'TU1', 'Misc'))
ALLOWED.update('Transformer.Net.B.' + x for x in
               ('TI0_0', 'TI0_1', 'TI0_2', 'TI0_3', 'TI1_0', 'TI1_1', 'TI1_2', 'TI1_3', 'TU0', 'TU1', 'Misc', 'G'))


def inventory(bounds=False, support=False, row0=False, cached_support=False):
    allowed = set(ALLOWED)
    extra_seeds = ()
    if row0:
        from row0_receipt import validate_codegen
        receipt = validate_codegen(BASE)
        extra_seeds = ("Transformer.CachedFixture", *receipt["modules"],
                       *(f"Transformer.Net.CachedPair0_{b}" for b in range(113)))
        allowed.update(("Transformer.Cached", *extra_seeds))
    if cached_support:
        extra_seeds = ("Transformer.CachedFixture",)
        allowed.update(("Transformer.Cached", *extra_seeds))
    seen, active, ordered = set(), set(), []

    def visit(module):
        if module not in allowed:
            raise ValueError(f'out-of-scope import: {module}')
        if module in active:
            raise ValueError(f'import cycle: {module}')
        if module in seen:
            return
        active.add(module)
        src = BASE / (module.replace('.', '/') + '.lean')
        data = src.read_bytes()
        # These exact retained modules use one import per line, without modifiers.
        for line in data.decode().splitlines():
            if re.match(r'^\s*(?:(?:public|private|meta)\s+)?import\b', line):
                if not re.fullmatch(r'import [A-Za-z0-9_.]+', line):
                    raise ValueError(f'unsupported import syntax in {module}: {line}')
                visit(line.removeprefix('import '))
        active.remove(module)
        seen.add(module)
        target = re.sub(rb'\bTransformer\b', b'TransformerCore', data)
        dst = module.replace('Transformer', 'TransformerCore', 1).replace('.', '/') + '.lean'
        ordered.append((module, src, dst, data, target))

    for seed in SEEDS + (BOUNDS if bounds or row0 else (BOUNDS[:1] if support or cached_support else ())) + extra_seeds:
        visit(seed)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--bounds', action='store_true')
    modes.add_argument('--support-only', action='store_true')
    modes.add_argument('--row0', action='store_true', help='closed stable ROW0/113 mirror; requires checked row generation')
    modes.add_argument('--cached-support-only', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--inventory', action='store_true', help='hash only; do not emit mirrors')
    parser.add_argument('--manifest', type=Path)
    args = parser.parse_args()
    rows = inventory(args.bounds, args.support_only, args.row0, args.cached_support_only)
    manifest = []
    for module, src, dst, data, target in rows:
        dest = HERE / dst
        if args.check:
            if dest.read_bytes() != target:
                raise ValueError(f'mirror differs: {dst}')
            print(f'ok   {dst} is the renamed {src.relative_to(BASE)}')
        elif not args.inventory:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(target)
        manifest.append('\t'.join((module.replace('Transformer', 'TransformerCore', 1),
                                   str(src.relative_to(BASE)), dst,
                                   hashlib.sha256(data).hexdigest(), hashlib.sha256(target).hexdigest())))
    if args.manifest:
        args.manifest.write_text('\n'.join(manifest) + '\n')
    print(f'sync status=OK modules={len(rows)} mode={"row0" if args.row0 else "cached-support" if args.cached_support_only else "bounds" if args.bounds else "support" if args.support_only else "program"}')


if __name__ == '__main__':
    main()
