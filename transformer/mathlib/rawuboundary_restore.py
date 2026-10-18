"""Exact three-archive continuation; one learned-U row127 boundary only."""
from contextlib import ExitStack
import json
from pathlib import Path
import re
import zipfile

import rawcu_restore as previous
import rawcu_generate as row0
from rawpilot_data import HERE, ROOT, sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms

PIN_PATH = HERE / 'RawUBoundary-checkpoint.json'
require = previous.require
digest = previous.digest
stream_sha = previous.stream_sha


def pin():
    return json.loads(PIN_PATH.read_text())


def inverse_workflow(text):
    """New hash-bound layer back to the actual accepted row0 workflow bytes."""
    rule = pin()['workflow_projection']
    require(digest(text.encode()) == rule['current_sha256'], 'unknown boundary workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment) == 1, 'boundary workflow inverse occurrence')
        text = text.replace(fragment, '', 1)
    require(text.count(rule['exclusion']) == 3, 'boundary workflow exclusion count')
    text = text.replace(rule['exclusion'], '')
    require(digest(text.encode()) == rule['accepted_sha256'], 'row0 workflow inverse differs')
    return text


def project_current(path, data):
    rule = pin()['nonproof_projections'].get(path)
    if rule is None:
        return data
    require(digest(data) == rule['current_sha256'], 'unknown boundary source drift: ' + path)
    for edit in rule['edits']:
        before, after = edit['current'].encode(), edit['accepted'].encode()
        require(data.count(before) == 1, 'boundary source inverse occurrence: ' + path)
        data = data.replace(before, after, 1)
    require(digest(data) == rule['accepted_sha256'], 'row0 source inverse differs: ' + path)
    return data


def verify_current_candidate(candidate):
    require(candidate == pin()['row0']['candidate'], 'row0 candidate inventory differs')
    for rel, expected in candidate.items():
        path = (HERE / rel).resolve()
        raw = path.read_bytes()
        if path == ROOT / '.github/workflows/transformer.yml':
            raw = inverse_workflow(raw.decode()).encode()
        else:
            raw = project_current(str(path.relative_to(ROOT)), raw)
        require(digest(raw) == expected, 'row0 candidate source drift: ' + rel)


def read_row0(archive):
    previous.old.archive_index(archive)
    result = {}
    for name, expected in pin()['row0']['metadata_sha256'].items():
        require(archive.getinfo(name).file_size < 1_000_000, 'oversized row0 metadata')
        data = archive.read(name)
        require(digest(data) == expected, 'row0 metadata hash: ' + name)
        result[Path(name).name] = data.decode()
    return result


def historical_names():
    import rawcorrespondence_runner as common
    return [*common.SCALAR_NAMES, *common.PACKED_NAMES, *common.old_inventory()[1],
            *common.gen.SUPPORT_NAMES, *common.gen.LINEAR_NAMES, *common.gen.FIXTURE_NAMES,
            *common.gen.inventory()[1]]


def validate_row0(data):
    lock = pin(); load = lambda name: json.loads(data[name])
    records = [json.loads(s) for s in data['compiled.jsonl'].splitlines()]
    require(records == lock['row0']['objects'] and data['compiled.jsonl'] == data['replayed.jsonl'], 'row0 exact compile/replay inventory')
    require([r['module'] for r in records] == row0.MODULES, 'row0 missing/duplicate/wrong modules')
    accepted = load('U_ROW0_ACCEPTED.json'); generation = load('generation.json')
    require(accepted['kernel_verdict'] == 'KERNEL_ACCEPTED' and accepted['scope'] == row0.SCOPE and
            accepted['fresh_compiled_replayed'] == records and accepted['exact_production_audit_names'] == 2650 and
            accepted['negative_actual_U_change'] == 'KERNEL_DECIDE_FALSE_EXIT_1' and
            accepted['fanout'] == 'NOT_AUTHORIZED', 'row0 acceptance boundary')
    oldlock = previous.pin()
    require(sha(previous.PIN_PATH) == lock['row0_checkpoint_sha256'] and
            accepted['checkpoint_sha256'] == lock['row0_checkpoint_sha256'], 'immutable row0 checkpoint')
    require(accepted['compiler_binary_sha256'] == oldlock['compiler_binary_sha256'] == lock['compiler_binary_sha256'], 'row0 compiler drift')
    require(generation == accepted['generation'] and generation['scope'] == row0.SCOPE and
            generation['modules'] == row0.MODULES and generation['declarations'] == row0.NAMES and
            generation['kernel_verdict'] == 'KERNEL_NOT_RUN', 'row0 generation schema/scope')
    require(generation['outputs'] == {r['module'].replace('.', '/') + '.lean': r['source_sha256'] for r in records}, 'row0 output source identity')
    original = {r['module'].replace('.', '/') + '.lean': r['source_sha256'] for r in oldlock['packed_objects']}
    wanted_sources = {k: original[k] for k in ('TransformerBridge/RawPacked/Generated/U000.lean', 'TransformerBridge/RawPacked/Generated/U001.lean')}
    require(generation['original_U_sources'] == wanted_sources, 'row0 canonical U layout/source hashes')
    negative = generation['negative']
    require(set(negative) == {'field', 'coordinate', 'old', 'new', 'delta', 'negative_sha256'} and
            negative['field'] == 'U' and negative['coordinate'] == [0, 0] and
            type(negative['old']) is int and type(negative['new']) is int and
            negative['new'] == negative['old'] + 1 and negative['delta'] == 1 and
            digest(data['changed-U.lean'].encode()) == negative['negative_sha256'], 'row0 actual coefficient control')
    # Only the independent false statement template is inspected; no production row evaluation.
    _, template = row0.row_sources([0] * 113)
    require(data['changed-U.lean'] == template, 'row0 false-control statement drift')
    previous_records = oldlock['packed_objects'] + oldlock['ci']['objects']
    require(accepted['restored_objects'] == previous_records and
            load('restored-union.json')['objects'] == previous_records and
            load('restored-union.json')['packed_zip_sha256'] == json.loads(previous.old.PIN_PATH.read_text())['zip_sha256'] and
            load('restored-union.json')['ci_zip_sha256'] == oldlock['ci']['zip_sha256'], 'row0 authentic 226-object prefix')
    verify_current_candidate(accepted['candidate'])
    for label, names in [('row0', row0.NAMES[:3]), ('control', row0.NAMES[3:]),
                         ('complete-U-row0', historical_names() + row0.NAMES)]:
        require(load(label + '-axioms.expected.json') == names, 'row0 expected audit inventory')
        require(check_correspondence_axioms(data[label + '-axioms.out'], names) == len(names), 'row0 complete strict audit')
    steps = [json.loads(s) for s in data['steps.jsonl'].splitlines()]
    require(len({s['name'] for s in steps}) == len(steps), 'duplicate row0 producer')
    def step(name):
        selected = [s for s in steps if s['name'] == name]
        require(len(selected) == 1, 'missing row0 producer: ' + name)
        return selected[0]
    for r in records:
        module = r['module']; stem = module.replace('.', '/')
        s = step('fresh_compile_' + module); cmd = s['command']
        require(s['exit'] == 0 and len(cmd) == 6 and cmd[:4] == ['lake', 'env', 'lean', '-o'] and
                cmd[4].endswith('/.lake/build/lib/lean/' + stem + '.olean') and cmd[5] == stem + '.lean', 'row0 compile producer')
        s = step('fresh_replay_' + module)
        require(s['exit'] == 0 and s['command'] == ['lake', 'env', 'leanchecker', module], 'row0 replay producer')
    for label in ('row0-axioms', 'control-axioms', 'complete-U-row0-axioms', 'negative-actual-U-change'):
        s = step(label); cmd = s['command']; negative_process = label.startswith('negative')
        file = 'changed-U.lean' if negative_process else label + '.lean'
        require(len(cmd) == 4 and cmd[:3] == ['lake', 'env', 'lean'] and
                cmd[3].endswith('/rawcu-out/' + file) and s['exit'] == (1 if negative_process else 0), 'row0 audit/control process')
    require(re.search(r'decide[\s\S]*false', data['negative-actual-U-change.out']) is not None, 'row0 negative diagnostic')
    return records


def check_overlaps(archives):
    """Check every physical overlap, including sources, objects and auxiliary paths."""
    seen = {}
    for archive in archives:
        for item in archive.infolist():
            if item.is_dir(): continue
            if item.filename in seen:
                earlier = seen[item.filename]
                require(item.file_size == earlier.getinfo(item.filename).file_size and
                        digest(archive.read(item.filename)) == digest(earlier.read(item.filename)), 'three-archive overlap mismatch: ' + item.filename)
            else: seen[item.filename] = archive


def restore(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, binaries):
    cloud_only()
    lock = pin(); oldlock = previous.pin(); packedlock = json.loads(previous.old.PIN_PATH.read_text())
    require(sha(previous.PIN_PATH) == lock['row0_checkpoint_sha256'] and
            sha(previous.old.PIN_PATH) == lock['packed_checkpoint_sha256'], 'earlier immutable checkpoint changed')
    require({name: sha(path) for name, path in binaries.items()} == lock['compiler_binary_sha256'], 'boundary compiler drift')
    require(sha(HERE / 'lean-toolchain') == lock['toolchain_sha256'] and
            sha(HERE / 'lake-manifest.json') == lock['lake_manifest_sha256'], 'boundary toolchain/manifest drift')
    for archive, api, identity in [(packed_archive, packed_api, packedlock), (ci_archive, ci_api, oldlock['ci']),
                                   (row0_archive, row0_api, lock['row0'])]:
        require(stream_sha(archive) == identity['zip_sha256'], 'boundary archive ZIP mismatch')
        previous.api_identity(json.loads(Path(api).read_text()), identity)
    base = HERE / '.lake/build/lib/lean'
    for project in ('Transformer', 'TransformerCore', 'TransformerBridge'):
        require(not list((base / project).rglob('*.olean')) and not (base / (project + '.olean')).exists(), 'preexisting boundary proof objects')
    with ExitStack() as stack:
        archives = [stack.enter_context(zipfile.ZipFile(path)) for path in (packed_archive, ci_archive, row0_archive)]
        for archive in archives: previous.old.archive_index(archive)
        a, b, c = archives
        metadata = previous.old.read_metadata(a, packedlock)
        packed, source, _ = previous.old.validate_metadata(metadata, packedlock)
        require(packed == oldlock['packed_objects'], 'packed object prefix changed')
        previous.verify_sources(source)
        ci_records = previous.validate_ci(previous.read_ci(b))
        new = validate_row0(read_row0(c)); records = packed + ci_records + new
        require(len(records) == 228 and len({r['module'] for r in records}) == 228, 'three-archive missing/duplicate objects')
        check_overlaps(archives)
        previous.verify_union_sources(archives, records)
        # All archive identities/imports/receipts have passed before writing any source/object.
        for r in records:
            stem = r['module'].replace('.', '/'); rel = stem + '.lean'
            sources = [z for z in archives if rel in z.namelist()]
            if sources: previous.old.write_exact(HERE / rel, sources[0].read(rel))
            obj = '.lake/build/lib/lean/' + stem + '.olean'
            found = [z for z in archives if obj in z.namelist()]
            require(found, 'missing three-archive object: ' + obj)
            previous.restore_object(found[0], obj, HERE / obj, r['olean_sha256'])
    return {'status': 'RESTORED_AUTHENTICATED_PACKED_CI_ROW0', 'objects': records,
            'archive_sha256': [packedlock['zip_sha256'], oldlock['ci']['zip_sha256'], lock['row0']['zip_sha256']]}
