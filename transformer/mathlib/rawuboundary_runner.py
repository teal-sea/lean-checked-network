#!/usr/bin/env python3
"""Single learned-U row127 boundary; no other row or field dispatch."""
import argparse
import json
import os
from pathlib import Path
import re
from rawpilot_generate import cloud_only
from rawpilot_data import HERE, sha
import rawuboundary_generate as gen
import rawuboundary_restore as cache
import rawcorrespondence_runner as common

OUT = HERE / 'rawuboundary-out'


def audit(label, imports, names):
    # Use the working adapter/producer unchanged; its OUT and underlying runner OUT are scoped here.
    return common.audit(label, imports, names)


def snapshot():
    policy = json.loads((HERE / 'input_policy.json').read_text())
    for rel, expected in policy['sources'].items():
        cache.require(sha(HERE / rel) == expected, 'current source policy drift: ' + rel)
    return {rel: sha(HERE / rel) for rel in policy['sources']}


def main(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api):
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
    restored = cache.restore(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, binaries)
    (OUT / 'restored-union.json').write_text(json.dumps(restored, indent=2, sort_keys=True) + '\n')
    record = gen.emit(OUT); gen.emit(OUT, check=True)
    paths = [m.replace('.', '/') + '.lean' for m in gen.MODULES]
    common.runner.run('U-row127-scan', ['../lean/scan_sources.sh', *paths, str(OUT / 'changed-U127.lean')], 60)
    fresh = []
    for module in gen.MODULES:
        common.check_declarations(module, gen.NS,
            gen.NAMES[:3] if module == gen.MODULES[0] else gen.NAMES[3:])
        fresh.append(common.fresh_compile(module))
        audit('row127' if module == gen.MODULES[0] else 'control', [module],
              gen.NAMES[:3] if module == gen.MODULES[0] else gen.NAMES[3:])
    old_names = [*common.SCALAR_NAMES, *common.PACKED_NAMES, *common.old_inventory()[1],
                 *common.gen.SUPPORT_NAMES, *common.gen.LINEAR_NAMES, *common.gen.FIXTURE_NAMES, *common.gen.inventory()[1]]
    names = old_names + cache.row0.NAMES + gen.NAMES
    count = audit('complete-U-row127', ['TransformerBridge.RawPacked.Generated.Site',
                  'TransformerBridge.RawCorrespondence.Generated.Control',
                  'TransformerBridge.RawCorrespondenceFixture', 'TransformerBridge.RawCorrespondenceLinear', cache.row0.MODULES[-1], gen.MODULES[-1]], names)
    common.runner.run('negative-actual-U127-change', ['lake', 'env', 'lean', str(OUT / 'changed-U127.lean')], 900, negative=True)
    gen.emit(OUT, check=True)
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
    accepted = {'kernel_verdict': 'KERNEL_ACCEPTED', 'scope': gen.SCOPE, 'fresh_compiled_replayed': fresh,
                'restored_objects': restored['objects'], 'exact_production_audit_names': count,
                'negative_actual_U127_change': 'KERNEL_DECIDE_FALSE_EXIT_1', 'generation': record,
                'candidate': candidate, 'compiler_binary_sha256': cache.pin()['compiler_binary_sha256'],
                'checkpoint_sha256': sha(cache.PIN_PATH), 'fanout': 'NOT_AUTHORIZED'}
    (OUT / 'U_ROW127_ACCEPTED.json').write_text(json.dumps(accepted, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('packed-archive', 'packed-api', 'ci-archive', 'ci-api', 'row0-archive', 'row0-api'): parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    try:
        main(args.packed_archive, args.packed_api, args.ci_archive, args.ci_api, args.row0_archive, args.row0_api)
    except Exception as error:
        if OUT.exists():
            (OUT / 'FAILURE.json').write_text(json.dumps({'kernel_verdict': 'NOT_ACCEPTED', 'error': str(error),
                'scope': gen.SCOPE, 'completed_steps': list(common.runner.STEPS)}, indent=2) + '\n')
        raise
