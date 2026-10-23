"""Four-archive authenticated continuation; earlier validators remain authoritative."""
from contextlib import ExitStack
import json
from pathlib import Path
import re
import zipfile
import rawuboundary_restore as boundary
import rawuboundary_generate as row127
from rawpilot_data import HERE, ROOT, sha
from rawpilot_generate import cloud_only
from rawcorrespondence_runner import check_correspondence_axioms

base = boundary.previous
PIN_PATH = HERE / 'RawURange-checkpoint.json'
require = boundary.require
digest = boundary.digest
stream_sha = boundary.stream_sha


def pin():
    return json.loads(PIN_PATH.read_text())


def inverse_workflow(text):
    from rawcufull_restore import inverse_workflow as cu_inverse
    text = cu_inverse(text)
    rule = pin()['workflow_projection']
    require(digest(text.encode()) == rule['current_sha256'], 'unknown range workflow drift')
    for fragment in rule['insertions']:
        require(text.count(fragment) == 1, 'range workflow inverse occurrence')
        text = text.replace(fragment, '', 1)
    require(text.count(rule['exclusion']) == 3, 'range workflow exclusion count')
    text = text.replace(rule['exclusion'], '')
    require(digest(text.encode()) == rule['accepted_sha256'], 'b37 workflow inverse differs')
    return text


def project_current(path, data):
    from rawcufull_restore import project_current as cu_project
    data = cu_project(path, data)
    rule = pin()['nonproof_projections'].get(path)
    if rule is None: return data
    require(digest(data) == rule['current_sha256'], 'unknown range source drift: ' + path)
    for edit in rule['edits']:
        current, accepted = edit['current'].encode(), edit['accepted'].encode()
        require(data.count(current) == 1, 'range source inverse occurrence')
        data = data.replace(current, accepted, 1)
    require(digest(data) == rule['accepted_sha256'], 'b37 source inverse differs: ' + path)
    return data


def verify_candidate(candidate):
    require(candidate == pin()['row127']['candidate'], 'row127 candidate inventory')
    for rel, expected in candidate.items():
        path = (HERE / rel).resolve(); raw = path.read_bytes()
        if path == ROOT / '.github/workflows/transformer.yml': raw = inverse_workflow(raw.decode()).encode()
        else: raw = project_current(str(path.relative_to(ROOT)), raw)
        require(digest(raw) == expected, 'row127 source drift: ' + rel)


def read_row127(archive):
    base.old.archive_index(archive); result = {}
    for name, expected in pin()['row127']['metadata_sha256'].items():
        require(archive.getinfo(name).file_size < 1_000_000, 'oversized row127 metadata')
        raw = archive.read(name); require(digest(raw) == expected, 'row127 metadata hash: ' + name)
        result[Path(name).name] = raw.decode()
    return result


def validate_row127(data):
    load = lambda n: json.loads(data[n]); lock = pin()
    records = [json.loads(s) for s in data['compiled.jsonl'].splitlines()]
    require(records == lock['row127']['objects'] and data['compiled.jsonl'] == data['replayed.jsonl'] and
            [r['module'] for r in records] == row127.MODULES, 'row127 compile/replay inventory')
    accepted = load('U_ROW127_ACCEPTED.json'); generation = load('generation.json')
    require(accepted['kernel_verdict'] == 'KERNEL_ACCEPTED' and accepted['scope'] == row127.SCOPE and
            accepted['fresh_compiled_replayed'] == records and accepted['exact_production_audit_names'] == 2655 and
            accepted['negative_actual_U127_change'] == 'KERNEL_DECIDE_FALSE_EXIT_1' and accepted['fanout'] == 'NOT_AUTHORIZED', 'row127 acceptance boundary')
    require(sha(boundary.PIN_PATH) == accepted['checkpoint_sha256'] == lock['boundary_checkpoint_sha256'] and
            accepted['compiler_binary_sha256'] == lock['compiler_binary_sha256'] == boundary.pin()['compiler_binary_sha256'], 'row127 checkpoint/compiler drift')
    require(generation == accepted['generation'] and generation['scope'] == row127.SCOPE and
            generation['modules'] == row127.MODULES and generation['declarations'] == row127.NAMES and
            generation['kernel_verdict'] == 'KERNEL_NOT_RUN' and
            generation['outputs'] == {r['module'].replace('.', '/') + '.lean': r['source_sha256'] for r in records}, 'row127 generation/source identity')
    originals = {r['module'].replace('.', '/') + '.lean': r['source_sha256'] for r in base.pin()['packed_objects']}
    require(generation['original_U_sources'] == {p: originals[p] for p in (
        'TransformerBridge/RawPacked/Generated/U000.lean', 'TransformerBridge/RawPacked/Generated/U001.lean')}, 'row127 canonical U identity')
    negative = generation['negative']; _, template = row127.row_sources([0] * 113)
    require(set(negative) == {'field', 'coordinate', 'old', 'new', 'delta', 'negative_sha256'} and
            negative['field'] == 'U' and negative['coordinate'] == [127, 0] and
            type(negative['old']) is int and type(negative['new']) is int and negative['new'] == negative['old'] + 1 and
            negative['delta'] == 1 and data['changed-U127.lean'] == template and
            digest(template.encode()) == negative['negative_sha256'], 'row127 actual negative source/coefficient')
    previous = base.pin()['packed_objects'] + base.pin()['ci']['objects'] + boundary.pin()['row0']['objects']
    restored = load('restored-union.json')
    wanted_archives = [json.loads(base.old.PIN_PATH.read_text())['zip_sha256'], base.pin()['ci']['zip_sha256'], boundary.pin()['row0']['zip_sha256']]
    require(accepted['restored_objects'] == restored['objects'] == previous and len(previous) == 228 and
            restored['archive_sha256'] == wanted_archives, 'row127 authentic prefix')
    verify_candidate(accepted['candidate'])
    for label, names in [('row127', row127.NAMES[:3]), ('control', row127.NAMES[3:]),
                         ('complete-U-row127', boundary.historical_names() + boundary.row0.NAMES + row127.NAMES)]:
        require(load(label + '-axioms.expected.json') == names and
                check_correspondence_axioms(data[label + '-axioms.out'], names) == len(names), 'row127 exact strict audits')
    steps = [json.loads(s) for s in data['steps.jsonl'].splitlines()]
    require(len({s['name'] for s in steps}) == len(steps), 'duplicate row127 producer')
    def step(name):
        found = [s for s in steps if s['name'] == name]; require(len(found) == 1, 'missing row127 producer'); return found[0]
    for r in records:
        module = r['module']; stem = module.replace('.', '/'); s = step('fresh_compile_' + module); cmd = s['command']
        require(s['exit'] == 0 and len(cmd) == 6 and cmd[:4] == ['lake', 'env', 'lean', '-o'] and
                cmd[4].endswith('/.lake/build/lib/lean/' + stem + '.olean') and cmd[5] == stem + '.lean', 'wrong row127 compile')
        s = step('fresh_replay_' + module)
        require(s['exit'] == 0 and s['command'] == ['lake', 'env', 'leanchecker', module], 'wrong row127 replay')
    for label in ('row127-axioms', 'control-axioms', 'complete-U-row127-axioms', 'negative-actual-U127-change'):
        s = step(label); cmd = s['command']; neg = label.startswith('negative')
        name = 'changed-U127.lean' if neg else label + '.lean'
        require(len(cmd) == 4 and cmd[:3] == ['lake', 'env', 'lean'] and
                cmd[3].endswith('/rawuboundary-out/' + name) and s['exit'] == (1 if neg else 0), 'wrong row127 audit/control producer')
    require(re.search(r'decide[\s\S]*false', data['negative-actual-U127-change.out']) is not None, 'row127 negative diagnostic')
    return records


def restore(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, row127_archive, row127_api, binaries):
    cloud_only(); lock = pin(); oldlock = base.pin(); packedlock = json.loads(base.old.PIN_PATH.read_text())
    require(sha(boundary.PIN_PATH) == lock['boundary_checkpoint_sha256'] and
            sha(base.PIN_PATH) == lock['row0_checkpoint_sha256'] and sha(base.old.PIN_PATH) == lock['packed_checkpoint_sha256'], 'earlier lock drift')
    require({n: sha(path) for n, path in binaries.items()} == lock['compiler_binary_sha256'] and
            sha(HERE / 'lean-toolchain') == lock['toolchain_sha256'] and
            sha(HERE / 'lake-manifest.json') == lock['lake_manifest_sha256'], 'range compiler/toolchain drift')
    for archive, api, identity in [(packed_archive, packed_api, packedlock), (ci_archive, ci_api, oldlock['ci']),
            (row0_archive, row0_api, boundary.pin()['row0']), (row127_archive, row127_api, lock['row127'])]:
        require(stream_sha(archive) == identity['zip_sha256'], 'range archive ZIP drift')
        base.api_identity(json.loads(Path(api).read_text()), identity)
    for project in ('Transformer', 'TransformerCore', 'TransformerBridge'):
        folder = HERE / '.lake/build/lib/lean' / project
        require(not list(folder.rglob('*.olean')) and not folder.with_suffix('.olean').exists(), 'preexisting range proof objects')
    with ExitStack() as stack:
        archives = [stack.enter_context(zipfile.ZipFile(p)) for p in (packed_archive, ci_archive, row0_archive, row127_archive)]
        for z in archives: base.old.archive_index(z)
        a, b, c, d = archives
        packed, source, _ = base.old.validate_metadata(base.old.read_metadata(a, packedlock), packedlock)
        require(packed == oldlock['packed_objects'], 'range packed prefix')
        base.verify_sources(source)
        ci = base.validate_ci(base.read_ci(b)); r0 = boundary.validate_row0(boundary.read_row0(c)); r127 = validate_row127(read_row127(d))
        records = packed + ci + r0 + r127
        require(len(records) == 230 and len({r['module'] for r in records}) == 230, 'range union count/duplicates')
        boundary.check_overlaps(archives); base.verify_union_sources(archives, records)
        # Reuse the validated three-archive restoration implementation; no cold build.
        prefix = boundary.restore(packed_archive, packed_api, ci_archive, ci_api, row0_archive, row0_api, binaries)
        require(prefix['objects'] == records[:-2], 'restored prefix differs')
        for r in r127:
            stem = r['module'].replace('.', '/'); rel = stem + '.lean'
            base.old.write_exact(HERE / rel, d.read(rel))
            obj = '.lake/build/lib/lean/' + stem + '.olean'
            base.restore_object(d, obj, HERE / obj, r['olean_sha256'])
    return {'status': 'RESTORED_AUTHENTICATED_PACKED_CI_ROW0_ROW127', 'objects': records,
            'archive_sha256': prefix['archive_sha256'] + [lock['row127']['zip_sha256']]}
