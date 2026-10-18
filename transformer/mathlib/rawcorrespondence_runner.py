#!/usr/bin/env python3
"""ONE complete CI field using a hash-verified accepted prefix; no cold preprocessing."""
import argparse
import json
import os
from pathlib import Path
import re

import rawpacked_runner as runner
from rawpilot_generate import cloud_only
from rawpilot_data import HERE, sha, SUPPORT_NAMES as SCALAR_NAMES
from rawpacked_data import SUPPORT_NAMES as PACKED_NAMES, inventory as old_inventory, PREFIX as OLD_PREFIX
import rawcorrespondence_generate as gen
import rawcorrespondence_restore as cache

OUT = HERE / 'rawcorrespondence-out'




def check_correspondence_axioms(text, expected):
    """Parse complete records; only comma separators may wrap as LF + one space.

    No stripping, line dropping, or general whitespace normalization is allowed.
    Only fully parsed records are serialized into the frozen strict validator.
    """
    if len(expected) != len(set(expected)):
        raise ValueError('duplicate requested raw-correspondence audit declaration')
    axiom = r'(?:propext|Classical\.choice|Quot\.sound)'
    record = re.compile(
        r"'([^'\r\n]+)' (does not depend on any axioms|depends on axioms: \["
        + axiom + r'(?:(?:, |,\n )' + axiom + r')*\])(?:\n|\Z)')
    offset, canonical = 0, []
    while offset < len(text):
        match = record.match(text, offset)
        if match is None:
            raise ValueError('unexpected/nonstandard correspondence axiom record at offset ' + str(offset))
        body = match[2]
        if body.startswith('depends on axioms: ['):
            values = re.split(r', |,\n ', body[len('depends on axioms: ['):-1])
            if len(values) != len(set(values)):
                raise ValueError('duplicate correspondence axiom')
            body = 'depends on axioms: [' + ', '.join(values) + ']'
        canonical.append("'" + match[1] + "' " + body + '\n')
        offset = match.end()
    return runner.check_axioms(''.join(canonical), expected)


def audit(label, imports, names):
    """Audit complete Lean records through the local closed-grammar adapter."""
    if len(names) != len(set(names)):
        raise ValueError('duplicate requested raw-correspondence audit declaration')
    path = OUT / (label + '-axioms.lean')
    path.write_text(''.join('import ' + m + '\n' for m in imports) +
                    ''.join('#print axioms ' + n + '\n' for n in names))
    (OUT / (label + '-axioms.expected.json')).write_text(json.dumps(names, indent=2) + '\n')
    text = runner.run(label + '-axioms', ['lake', 'env', 'lean', str(path)], 600)
    count = check_correspondence_axioms(text, names)
    print(f'{label} exact declarations={count}/{len(names)} standard-axioms-only=YES', flush=True)
    return count


def snapshot():
    paths = ['rawcorrespondence_runner.py', 'rawcorrespondence_restore.py',
             'rawcorrespondence_generate.py', 'RawCorrespondence-checkpoint.json',
             'rawcorrespondence.sh', 'test_rawcorrespondence.py',
             'TransformerBridge/RawCorrespondenceSupport.lean',
             'TransformerBridge/RawCorrespondenceFixture.lean',
             'TransformerBridge/RawCorrespondenceLinear.lean', '../../.github/workflows/transformer.yml']
    return {p: sha(HERE / p) for p in paths}


def check_declarations(module, namespace, names):
    text = (HERE / (module.replace('.', '/') + '.lean')).read_text()
    found = re.findall(r'^(?:def|theorem) (\w+)\b', text, re.M)
    cache.require([namespace + '.' + n for n in found] == names, 'exact new declaration inventory differs: ' + module)


def fresh_compile(module):
    rel = module.replace('.', '/')
    obj = HERE / '.lake/build/lib/lean' / (rel + '.olean')
    cache.require(not obj.exists(), 'fresh object already exists: ' + module)
    obj.parent.mkdir(parents=True, exist_ok=True)
    # Direct compilation deliberately avoids Lake's old timestamp/trace invalidation.
    runner.run('fresh_compile_' + module,
               ['lake', 'env', 'lean', '-o', str(obj), rel + '.lean'], 900)
    item = {'module': module, 'source_sha256': sha(HERE / (rel + '.lean')), 'olean_sha256': sha(obj)}
    with (OUT / 'compiled.jsonl').open('a') as f:
        f.write(json.dumps(item, sort_keys=True) + '\n')
    runner.run('fresh_replay_' + module, ['lake', 'env', 'leanchecker', module], 900)
    cache.require(sha(obj) == item['olean_sha256'], 'new object changed during replay')
    with (OUT / 'replayed.jsonl').open('a') as f:
        f.write(json.dumps(item, sort_keys=True) + '\n')
    return item


def main(archive, api):
    cloud_only()
    cache.require(os.environ.get('GITHUB_REPOSITORY') == 'teal-sea/lean-checked-network',
                  'only the existing authorized public repository')
    cache.require(os.environ.get('LEAN_NUM_THREADS') in ('1', '2'), 'only 1–2 Lean threads')
    cache.require(not OUT.exists(), 'preexisting correspondence receipts')
    cache.require(not (HERE / gen.PREFIX.replace('.', '/')).exists(), 'preexisting CI proof sources')
    OUT.mkdir()
    runner.OUT = OUT
    runner.STEPS.clear()
    immutable = snapshot()
    version = runner.run('compiler-version', ['lake', 'env', 'lean', '--version'], 60)
    cache.require(bool(re.search(r'version 4\.35\.0(?:,|\))', version)), 'wrong compiler version')
    prefix = Path(runner.run('compiler-prefix', ['lake', 'env', 'lean', '--print-prefix'], 60).strip())
    binaries = {t: (prefix / 'bin' / t).resolve() for t in ('lean', 'lake', 'leanchecker')}
    restored = cache.restore(archive, api, binaries)
    (OUT / 'restored-previous.json').write_text(json.dumps(restored, indent=2) + '\n')
    (OUT / 'provenance.json').write_text(json.dumps({
        'current_github_sha': os.environ.get('GITHUB_SHA'), 'candidate': immutable,
        'scope': 'CI512 only; exact canonical RawPackedPilot.weights; full hT open',
        'compiler_binary_sha256': {t: sha(p) for t, p in binaries.items()},
        'toolchain_sha256': sha(HERE / 'lean-toolchain'),
        'lake_manifest_sha256': sha(HERE / 'lake-manifest.json')}, indent=2) + '\n')
    support = [gen.SUPPORT, gen.LINEAR, gen.FIXTURE]
    check_declarations(gen.SUPPORT, 'TransformerBridge.RawCorrespondence', gen.SUPPORT_NAMES)
    check_declarations(gen.LINEAR, 'TransformerBridge.RawCorrespondence', gen.LINEAR_NAMES)
    check_declarations(gen.FIXTURE, 'TransformerBridge.RawCorrespondenceFixture', gen.FIXTURE_NAMES)
    runner.run('support-scan', ['../lean/scan_sources.sh', *(m.replace('.', '/') + '.lean' for m in support)], 60)
    fresh = [fresh_compile(m) for m in support]
    support_count = audit('new-support', [gen.FIXTURE, gen.LINEAR], [*gen.SUPPORT_NAMES, *gen.LINEAR_NAMES, *gen.FIXTURE_NAMES])
    # Only after symbolic support and its signed affine fixture pass: proof source emission.
    runner.run('generate-CI-proof', ['python3', '-B', '-W', 'error', 'rawcorrespondence_generate.py'], 60)
    runner.run('generate-CI-proof-check', ['python3', '-B', '-W', 'error', 'rawcorrespondence_generate.py', '--check'], 60)
    gen.validate(HERE, OUT)
    modules, names = gen.inventory()
    cache.require((len(modules), len(names), support_count) == (5, 16, 15), 'wrong CI gate inventory')
    paths = [m.replace('.', '/') + '.lean' for m in modules]
    runner.run('CI-scan', ['../lean/scan_sources.sh', *paths, str(OUT / 'changed-bin.lean')], 60)
    for module in modules:
        fresh.append(fresh_compile(module))
        # Width-one actual learned affine certificate is the gate before width512.
        if module.endswith('.Representative'):
            audit('representative', [module], [gen.NS + '.representative_affine'])
    all_names = [*SCALAR_NAMES, *PACKED_NAMES, *old_inventory()[1], *gen.SUPPORT_NAMES, *gen.LINEAR_NAMES, *gen.FIXTURE_NAMES, *names]
    cache.require(len(all_names) == 2645, 'wrong complete CI exact audit count')
    count = audit('complete-CI', [OLD_PREFIX + '.Site', gen.PREFIX + '.Control', gen.FIXTURE, gen.LINEAR], all_names)
    runner.run('negative-actual-bin-change', ['lake', 'env', 'lean', str(OUT / 'changed-bin.lean')], 900, negative=True)
    gen.validate(HERE, OUT)
    cache.require(snapshot() == immutable, 'candidate source changed')
    cache.require({t: sha(p) for t, p in binaries.items()} ==
                  json.loads(cache.PIN_PATH.read_text())['compiler_binary_sha256'], 'compiler changed')
    cache.require((OUT / 'compiled.jsonl').read_bytes() == (OUT / 'replayed.jsonl').read_bytes(),
                  'exact new compiled/replayed records differ')
    cache.require([r['module'] for r in fresh] == [*support, *modules], 'new module inventory differs')
    for item in [*restored['objects'], *fresh]:
        stem = item['module'].replace('.', '/')
        cache.require(sha(HERE / (stem + '.lean')) == item['source_sha256'] and
                      cache.stream_sha(HERE / '.lake/build/lib/lean' / (stem + '.olean')) == item['olean_sha256'],
                      'final source/object identity changed: ' + item['module'])
    # Earlier source identities are rechecked, including canonical model, rounding and frozen bytes.
    with __import__('zipfile').ZipFile(archive) as z:
        metadata = cache.read_metadata(z, json.loads(cache.PIN_PATH.read_text()))
        cache.verify_current_sources(json.loads(metadata['sources.json']))
    throughput = {label: {'compile_seconds': runner.STEPS['fresh_compile_' + module]['seconds'],
                         'replay_seconds': runner.STEPS['fresh_replay_' + module]['seconds']}
                  for label, module in zip(['support', 'linear', 'fixture', *gen.DECLARATIONS], [*support, *modules])}
    for label, module in zip(['support', 'linear', 'fixture', *gen.DECLARATIONS], [*support, *modules]):
        rss = []
        for phase in ('fresh_compile_', 'fresh_replay_'):
            text = (OUT / (phase + module + '.time')).read_text()
            values = re.findall(r'Maximum resident set size \(kbytes\): (\d+)', text)
            cache.require(len(values) == 1, 'missing measured RSS: ' + phase + module)
            rss.append(int(values[0]))
        throughput[label]['max_command_peak_rss_kib'] = max(rss)
    (OUT / 'throughput.json').write_text(json.dumps(throughput, indent=2) + '\n')
    (OUT / 'CI_ACCEPTED.json').write_text(json.dumps({
        'kernel_verdict': 'KERNEL_ACCEPTED', 'CI_components': 512, 'full_hT': False,
        'restored_previous_compiled_replayed': 218, 'fresh_compiled_replayed': fresh,
        'exact_production_audit_names': count, 'new_support_names': [*gen.SUPPORT_NAMES, *gen.LINEAR_NAMES, *gen.FIXTURE_NAMES], 'new_support_audit_names': support_count,
        'negative_actual_bin_change': 'KERNEL_REJECTED_EXIT_1',
        'fanout': 'NOT_LAUNCHED; parent accepts next field separately'}, indent=2) + '\n')
    print('CI KERNEL_ACCEPTED 512/512; full hT NOT_PROVED; no other field fanout', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--artifact-metadata', type=Path, required=True)
    args = parser.parse_args()
    try:
        main(args.archive, args.artifact_metadata)
    except Exception as error:
        if OUT.exists():
            (OUT / 'FAILURE.json').write_text(json.dumps({'kernel_verdict': 'NOT_ACCEPTED',
                'error': str(error), 'completed_steps': list(runner.STEPS)}, indent=2) + '\n')
        raise
