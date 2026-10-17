#!/usr/bin/env python3
"""Serial public Actions row extension and fail-closed full-grid assembly."""
import argparse
import json
import os
from pathlib import Path
import re
import zipfile

import input_source as source
import row0_finalize as f
import row0_prefix
import row0_runner as runner
from input_compat import validate_row_policy
from row0_receipt import sha, validate_codegen
from row0_source import selected

HERE = Path(__file__).resolve().parent
POLICY = HERE / 'input_policy.json'
OUT = HERE / 'input-out'


def policy_check(policy):
    for name, digest in policy['sources'].items():
        source.require(sha(HERE / name) == digest, 'input source drift: ' + name)


def api_check(path, pin):
    api = json.loads(path.read_text())
    source.require(api.get('id') == pin['artifact_id'] and api.get('expired') is False and
                   api.get('workflow_run', {}).get('id') == pin['run'] and
                   api.get('workflow_run', {}).get('head_sha') == pin['source_sha'], 'artifact API identity')


def restore_row0(archive, api, pin):
    source.require(f.stream_sha(archive) == pin['zip_sha256'], 'accepted row0 ZIP identity')
    api_check(api, pin)
    with zipfile.ZipFile(archive) as z:
        f.archive_index(z)
        accepted = json.loads(z.read('row0-finalize-out/MQ_ACCEPTED.json'))
        source.require(accepted['status'] == 'KERNEL_ACCEPTED' and
                       accepted['new_source_commit'] == pin['source_sha'] and
                       accepted['fresh_object_sha256'] == pin['objects'] and
                       accepted['selected_axioms'] == 2634, 'accepted row0 receipt mismatch')
        for name, digest in accepted['candidate_sources'].items():
            if name != '../../.github/workflows/transformer.yml':
                source.require(sha(HERE / name) == digest, 'accepted row0 source mismatch: ' + name)
        for module, digest in pin['objects'].items():
            rel = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
            f.write_new(HERE / rel, f.read_checked(z, rel, digest))
    return pin['objects']


def write_sources(sources):
    for module, text in sources.items():
        f.write_new(HERE / (module.replace('.', '/') + '.lean'), text.encode())


def objects(modules):
    return {m: sha(HERE / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')) for m in modules}


def verify_generated(sources):
    for m, text in sources.items():
        source.require((HERE / (m.replace('.', '/') + '.lean')).read_text() == text,
                       'generated source/literal drift: ' + m)


def audit_names(receipt, rows):
    names = selected(receipt, real=True)
    for a in rows:
        names.extend(source.pair_names(a))
        names.extend(f'TransformerBridge.row{a}_{s}' for s in ('fastCheck', 'integer_margin', 'mq_argmax'))
    return names


def negative(a):
    path = OUT / 'changed-literal.lean'
    text = ('import TransformerCore.Net.Cached\n\nnamespace TransformerCore.Net.Cached\nopen TransformerCore.Net\n'
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n' +
            source.literal(a, 56, wrong_answer=True) + 'end TransformerCore.Net.Cached\n')
    path.write_text(text)
    runner.run('negative_changed_actual_literal', ['lake', 'env', 'lean', str(path)], 600, negative=True)


def import_rows(lock_path, policy, identity, gate=False):
    # Parent supplies an explicit adjudicated artifact lock only after each real run.
    lock = json.loads(lock_path.read_text())
    source.require(type(lock) is list and [x.get('row') for x in lock] == ([1] if gate else list(range(1, 113))),
                   'full assembly requires exactly ordered rows 1..112 plus retained row0')
    restored = {}
    base_receipt = validate_codegen(HERE.parent / 'lean')
    for item in lock:
        a = item['row']
        archive, api = Path(item['archive']), Path(item['api_metadata'])
        source.require(f.stream_sha(archive) == item['zip_sha256'], 'row archive SHA mismatch')
        api_check(api, item)
        expected = source.row_sources(a, HERE)
        with zipfile.ZipFile(archive) as z:
            f.archive_index(z)
            receipt = json.loads(z.read('input-out/ROW_ACCEPTED.json'))
            source.require(receipt['status'] == 'KERNEL_ACCEPTED' and receipt['row'] == a and
                           receipt['compiler'] == identity and
                           receipt['source_sha'] == item['source_sha'], 'row receipt identity mismatch')
            validate_row_policy(z, receipt, item, HERE)
            source.coverage(receipt['pairs'], a)
            if gate:
                measured = json.loads(z.read('input-out/throughput.json'))
                source.require(measured['throughput_acceptable'] is True and
                    measured['literal_compile_replay_seconds'] < 927.1758614700007 and
                    measured['literal_peak_rss_kb'] <= 5242880, 'row1 throughput gate failed')
            source.require(receipt['generated_sources'] ==
                           {m: f.digest(t.encode()) for m, t in expected.items()}, 'row generated source identity')
            source.require(set(receipt['fresh_objects']) == set(expected), 'row object inventory')
            steps = [json.loads(line) for line in z.read('input-out/steps.jsonl').decode().splitlines()]
            for module, digest in receipt['fresh_objects'].items():
                rel = module.replace('.', '/')
                source.require(z.read(rel + '.lean') == expected[module].encode(), 'row source bytes')
                for phase, command in [('fresh_compile_', ['lake', 'env', 'lean', '-o',
                         str(HERE / '.lake/build/lib/lean' / (rel + '.olean')), rel + '.lean']),
                         ('fresh_replay_', ['lake', 'env', 'leanchecker', module])]:
                    found = [r for r in steps if r.get('name') == phase + module]
                    source.require(len(found) == 1 and found[0]['exit'] == 0, 'missing row compile/replay')
                    cmd = found[0]['command']
                    if phase == 'fresh_compile_':
                        source.require(len(cmd) == 6 and cmd[:4] == ['lake', 'env', 'lean', '-o'] and
                            cmd[4].endswith('/.lake/build/lib/lean/' + rel + '.olean') and
                            cmd[5] == rel + '.lean', 'wrong row compile command')
                    else:
                        source.require(cmd == command, 'wrong row replay command')
                data = f.read_checked(z, '.lake/build/lib/lean/' + rel + '.olean', digest)
                if not gate:
                    f.write_new(HERE / '.lake/build/lib/lean' / (rel + '.olean'), data)
                    restored[module] = digest
            names = audit_names(base_receipt, [a])
            from row0_receipt import check_axioms
            check_axioms(z.read('input-out/row-axioms.out').decode(), names)
            neg = [s for s in steps if s.get('name') == 'negative_changed_actual_literal']
            source.require(len(neg) == 1 and neg[0]['exit'] == 1, 'missing actual literal negative exit')
            negative_text = z.read('input-out/negative_changed_actual_literal.out').decode()
            source.require('decide' in negative_text and 'false' in negative_text,
                           'negative control did not reject the literal obligation')
            canonical_red = ('import TransformerCore.Net.Cached\n\nnamespace TransformerCore.Net.Cached\nopen TransformerCore.Net\n'
                'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n' +
                source.literal(a, 56, wrong_answer=True) + 'end TransformerCore.Net.Cached\n')
            source.require(z.read('input-out/changed-literal.lean') == canonical_red.encode(),
                           'negative control changed the wrong obligation')
            source.require(neg[0]['command'][:3] == ['lake', 'env', 'lean'] and
                len(neg[0]['command']) == 4 and neg[0]['command'][3].endswith('/input-out/changed-literal.lean'),
                'wrong negative command')
            # Authenticated receipt and archive are parent adjudicated, not self-signed cache evidence.
        if not gate:
            write_sources(expected)
    return restored


def main(args):
    source.require(os.environ.get('GITHUB_ACTIONS') == 'true' and
                   os.environ.get('GITHUB_REPOSITORY') == 'teal-sea/lean-checked-network' and
                   os.environ.get('GITHUB_REF') == 'refs/heads/vizier/finish-transformer' and
                   os.environ.get('INPUT_PUBLIC_STANDARD') == '1' and
                   os.environ.get('LEAN_NUM_THREADS') in ('1', '2'), 'public standard Actions only')
    source.require(not OUT.exists(), 'mixed input receipts')
    OUT.mkdir()
    runner.OUT = OUT
    runner.STEPS.clear()
    policy = json.loads(POLICY.read_text())
    policy_check(policy)
    policy_sha = sha(POLICY)
    identity = row0_prefix.identity()
    pin = json.loads(f.PIN.read_text())
    restored, receipt, record = f.restore(args.archive, args.artifact_metadata, pin)
    (OUT / 'restored-previous.json').write_text(json.dumps(restored, indent=2) + '\n')
    (OUT / 'retained-prefix-receipt.json').write_text(json.dumps(record, indent=2) + '\n')
    (OUT / 'retained-generation-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    retained = {x['module']: x['sha256'] for x in restored['objects']}
    retained.update(restore_row0(args.row0_archive, args.row0_metadata, policy['row0']))
    if args.row is not None and args.row != 1:
        source.require(args.row1_lock is not None, 'later rows require parent-adjudicated row1 lock')
        retained.update(import_rows(args.row1_lock, policy, identity, gate=True))
    if args.row is not None:
        expected = source.row_sources(args.row, HERE)
        pairs = [[args.row, b] for b in range(113)]
        source.coverage(pairs, args.row)
        rows = [args.row]
    else:
        source.require(args.rows_lock is not None, 'full assembly needs parent-adjudicated rows lock')
        retained.update(import_rows(args.rows_lock, policy, identity))
        expected = source.all_sources(HERE)
        pairs = [[a, b] for a in range(113) for b in range(113)]
        source.coverage(pairs)
        rows = list(range(1, 113))
    write_sources(expected)
    (OUT / 'requested-pairs.json').write_text(json.dumps(pairs) + '\n')
    runner.scan('input-source-scan', [m.replace('.', '/') + '.lean' for m in expected])
    if args.row is not None:
        # All positive chunks precede the actual changed-literal rejection.
        for module in list(expected)[:8]:
            f.fresh_compile(module)
        negative(args.row)
        for module in list(expected)[8:]:
            f.fresh_compile(module)
    else:
        for module in expected:
            f.fresh_compile(module)
    names = audit_names(receipt, rows)
    if args.row is None:
        names += ['TransformerBridge.all_' + s for s in ('fastCheck', 'integer_margin', 'mq_argmax')]
    runner.audit('row' if args.row is not None else 'all',
                 ['TransformerCore.CachedFixture', 'TransformerBridge.Row0Real', list(expected)[-1]], names)
    policy_check(policy)
    source.require(sha(POLICY) == policy_sha and row0_prefix.identity() == identity, 'final policy/compiler drift')
    f.verify_sources(record, pin['source_exceptions'])
    validate_codegen(HERE.parent / 'lean')
    verify_generated(expected)
    source.require(objects(retained) == retained, 'retained object drift')
    fresh = objects(expected)
    timing = {}
    for m in expected:
        timing[m] = {phase: {'seconds': runner.STEPS[phase + m]['seconds'],
            'max_rss_kb': int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',
                (OUT / (phase + m + '.time')).read_text())[1])}
            for phase in ('fresh_compile_', 'fresh_replay_')}
    measured = {'modules': timing}
    if args.row is not None:
        chunk_modules = [m for m, _ in source.chunks(args.row)]
        seconds = sum(timing[m][phase]['seconds'] for m in chunk_modules
                      for phase in ('fresh_compile_', 'fresh_replay_'))
        rss = max(timing[m][phase]['max_rss_kb'] for m in chunk_modules
                  for phase in ('fresh_compile_', 'fresh_replay_'))
        measured.update({'literal_pairs': 113, 'chunk_sizes': [len(bs) for _, bs in source.chunks(args.row)],
                         'literal_compile_replay_seconds': seconds, 'literal_pairs_per_second': 113 / seconds,
                         'literal_peak_rss_kb': rss, 'baseline_row0_seconds': 927.1758614700007,
                         'throughput_acceptable': seconds < 927.1758614700007 and rss <= 5242880,
                         'criteria': 'literal compile+replay faster than row0; peak RSS <= 5 GiB'})
    (OUT / 'throughput.json').write_text(json.dumps(measured, indent=2) + '\n')
    result = {'status': 'KERNEL_ACCEPTED', 'row': args.row, 'pairs': pairs,
              'scope': 'frozen fused quantized table integer margin and real-softmax/argmax',
              'source_sha': os.environ['GITHUB_SHA'], 'compiler': identity,
              'policy_sha256': policy_sha, 'restored_previous_compiled_replayed': len(retained),
              'fresh_compiled_replayed': len(fresh), 'fresh_objects': fresh,
              'generated_sources': {m: f.digest(t.encode()) for m, t in expected.items()},
              'selected_axioms': len(names), 'all_input_coverage': args.row is None}
    (OUT / ('ROW_ACCEPTED.json' if args.row is not None else 'ALL_ACCEPTED.json')).write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', required=True, type=Path)
    p.add_argument('--artifact-metadata', required=True, type=Path)
    p.add_argument('--row0-archive', required=True, type=Path)
    p.add_argument('--row0-metadata', required=True, type=Path)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--row', type=int, choices=range(1, 113))
    mode.add_argument('--all', action='store_true')
    p.add_argument('--rows-lock', type=Path)
    p.add_argument('--row1-lock', type=Path)
    main(p.parse_args())
