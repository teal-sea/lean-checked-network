#!/usr/bin/env python3
"""At most four learned-U rows in one module; bounded throughput pilot only."""
import argparse
import json
import os
from pathlib import Path
import re
from rawpilot_generate import cloud_only
from rawpilot_data import HERE, sha
import rawurange_generate as gen
import rawurange_restore as cache
import rawcorrespondence_runner as common

OUT = HERE / 'rawurange-out'


def audit(label, imports, names):
    # Use the working adapter/producer unchanged; its OUT and underlying runner OUT are scoped here.
    return common.audit(label, imports, names)


def snapshot():
    policy = json.loads((HERE / 'input_policy.json').read_text())
    for rel, expected in policy['sources'].items():
        cache.require(sha(HERE / rel) == expected, 'current source policy drift: ' + rel)
    return {rel: sha(HERE / rel) for rel in policy['sources']}


def main(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, row127_archive, row127_api, start=1, count=4):
    gen.rows_for(start, count)
    modules, row_names, control_names = gen.inventory(start, count)
    cloud_only()
    cache.require(os.environ.get('GITHUB_REPOSITORY') == 'teal-sea/lean-checked-network' and
                  os.environ.get('LEAN_NUM_THREADS') in ('1', '2'), 'wrong public repository/threads')
    cache.require(not OUT.exists() and not (HERE / gen.PREFIX.replace('.', '/')).exists(), 'preexisting U row probe')
    OUT.mkdir(); common.OUT = OUT; common.runner.OUT = OUT; common.runner.STEPS.clear()
    candidate = snapshot()
    version = common.runner.run('compiler-version', ['lake', 'env', 'lean', '--version'], 60)
    cache.require('commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version and 'version 4.35.0' in version, 'wrong compiler')
    prefix = Path(common.runner.run('compiler-prefix', ['lake', 'env', 'lean', '--print-prefix'], 60).strip())
    binaries = {t: (prefix / 'bin' / t).resolve() for t in ('lean', 'lake', 'leanchecker')}
    restored = cache.restore(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, row127_archive, row127_api, binaries)
    (OUT / 'restored-union.json').write_text(json.dumps(restored, indent=2, sort_keys=True) + '\n')
    record = gen.emit(OUT, start, count); gen.emit(OUT, start, count, check=True)
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    common.runner.run('U-range-scan', ['../lean/scan_sources.sh', *paths, str(OUT / 'changed-U-range.lean')], 60)
    fresh = []
    for module in modules:
        common.check_declarations(module, gen.NS,
            row_names if module == modules[0] else control_names)
        fresh.append(common.fresh_compile(module))
        audit('batch' if module == modules[0] else 'control', [module],
              row_names if module == modules[0] else control_names)
    old_names = [*common.SCALAR_NAMES, *common.PACKED_NAMES, *common.old_inventory()[1],
                 *common.gen.SUPPORT_NAMES, *common.gen.LINEAR_NAMES, *common.gen.FIXTURE_NAMES, *common.gen.inventory()[1]]
    names = old_names + (cache.boundary.row0.NAMES + cache.row127.NAMES) + (row_names + control_names)
    audit_count = audit('complete-U-range', ['TransformerBridge.RawPacked.Generated.Site',
                  'TransformerBridge.RawCorrespondence.Generated.Control',
                  'TransformerBridge.RawCorrespondenceFixture', 'TransformerBridge.RawCorrespondenceLinear', cache.boundary.row0.MODULES[-1], cache.row127.MODULES[-1], modules[-1]], names)
    common.runner.run('negative-actual-U-range-change', ['lake', 'env', 'lean', str(OUT / 'changed-U-range.lean')], 900, negative=True)
    gen.emit(OUT, start, count, check=True)
    cache.require(snapshot() == candidate, 'candidate source changed')
    cache.require({t: sha(p) for t, p in binaries.items()} == cache.pin()['compiler_binary_sha256'], 'compiler changed')
    cache.require((OUT / 'compiled.jsonl').read_bytes() == (OUT / 'replayed.jsonl').read_bytes(), 'fresh compile/replay mismatch')
    for r in restored['objects'] + fresh:
        stem = r['module'].replace('.', '/')
        cache.require(sha(HERE / (stem + '.lean')) == r['source_sha256'] and
                      cache.stream_sha(HERE / '.lake/build/lib/lean' / (stem + '.olean')) == r['olean_sha256'], 'final source/object drift')
    throughput = {}
    for r in fresh:
        m = r['module']; stats = {}
        for phase in ('fresh_compile_', 'fresh_replay_'):
            label = phase + m
            rss = re.findall(r'Maximum resident set size \(kbytes\): (\d+)', (OUT / (label + '.time')).read_text())
            cache.require(len(rss) == 1, 'missing RSS')
            stats[phase] = {'seconds': common.runner.STEPS[label]['seconds'], 'peak_rss_kib': int(rss[0])}
        throughput[m] = stats
    (OUT / 'throughput.json').write_text(json.dumps(throughput, indent=2, sort_keys=True) + '\n')
    accepted = {'kernel_verdict': 'KERNEL_ACCEPTED', 'scope': gen.scope(start, count), 'fresh_compiled_replayed': fresh,
                'restored_objects': restored['objects'], 'exact_production_audit_names': audit_count,
                'negative_actual_U_range_change': 'KERNEL_DECIDE_FALSE_EXIT_1', 'generation': record,
                'candidate': candidate, 'compiler_binary_sha256': cache.pin()['compiler_binary_sha256'],
                'checkpoint_sha256': sha(cache.PIN_PATH), 'fanout': 'NOT_AUTHORIZED'}
    (OUT / 'U_RANGE_ACCEPTED.json').write_text(json.dumps(accepted, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('packed-archive', 'packed-api', 'ci-archive', 'ci-api', 'row0-archive', 'row0-api', 'row127-archive', 'row127-api'): parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--start', type=int, default=1)
    parser.add_argument('--count', type=int, default=4)
    args = parser.parse_args()
    try:
        main(args.packed_archive, args.packed_api, args.ci_archive, args.ci_api, args.row0_archive, args.row0_api, args.row127_archive, args.row127_api, args.start, args.count)
    except Exception as error:
        if OUT.exists():
            (OUT / 'FAILURE.json').write_text(json.dumps({'kernel_verdict': 'NOT_ACCEPTED', 'error': str(error),
                'requested_start': args.start, 'requested_count': args.count, 'completed_steps': list(common.runner.STEPS)}, indent=2) + '\n')
        raise
