"""Authenticated packed+CI union for the single U-row0 probe. No cold build."""
import hashlib
import json
from pathlib import Path
import re
import zipfile

import rawcorrespondence_restore as old
import rawcorrespondence_generate as ci
from rawcorrespondence_runner import check_correspondence_axioms
from rawpilot_generate import cloud_only
from rawpilot_data import HERE, ROOT, sha

PIN_PATH = HERE / 'RawCU-checkpoint.json'
require = old.require
digest = old.digest


def stream_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        while True:
            chunk = stream.read(1024 * 1024)
            if not chunk: break
            h.update(chunk)
    return h.hexdigest()


def pin():
    return json.loads(PIN_PATH.read_text())


def project_nonproof(path, data):
    """Restore exact accepted bytes, only for explicitly hash-bound harness changes."""
    rule = pin()['nonproof_projections'].get(path)
    if rule is None:
        return data
    require(digest(data) == rule['current_sha256'], 'unknown nonproof source drift: ' + path)
    for insertion in rule['insertions']:
        fragment = insertion.encode()
        require(data.count(fragment) == 1, 'nonproof inverse occurrence: ' + path)
        data = data.replace(fragment, b'', 1)
    require(digest(data) == rule['accepted_sha256'], 'nonproof inverse identity: ' + path)
    return data


def inverse_workflow(text):
    from rawuboundary_restore import inverse_workflow as boundary_inverse
    text = boundary_inverse(text)
    rules = pin()['workflow_projection']
    require(digest(text.encode()) == rules['current_sha256'], 'unknown workflow drift')
    for fragment in rules['insertions']:
        require(text.count(fragment) == 1, 'workflow inverse occurrence')
        text = text.replace(fragment, '', 1)
    # Three unrelated old jobs receive the same explicit exclusion.
    fragment = rules['exclusion']
    require(text.count(fragment) == 3, 'workflow inverse exclusion count')
    text = text.replace(fragment, '')
    require(digest(text.encode()) == rules['accepted_sha256'], 'accepted workflow inverse differs')
    return text


def verify_sources(source):
    for rel, expected in source['sources'].items():
        data = (ROOT / rel).read_bytes()
        if rel == '.github/workflows/transformer.yml':
            text = inverse_workflow(data.decode())
            start = text.index('  raw-correspondence-CI:\n'); end = text.index('  row0-finalize:\n', start)
            text = (text[:start] + text[end:]).replace('          - mathlib-raw-correspondence-CI\n', '')
            text = text.replace("inputs.core_mode == 'mathlib-raw-correspondence-CI' && '-mathlib-raw-correspondence-CI' || ", '')
            text = text.replace("inputs.core_mode != 'mathlib-raw-correspondence-CI' && ", '')
            text = text.split('\n  input-row1:\n', 1)[0].rstrip() + '\n'
            text = text.replace('          - mathlib-input-row1\n', '').replace('          - mathlib-input-grid\n', '').replace('          - mathlib-input-all\n', '')
            text = text.replace("inputs.core_mode == 'mathlib-input-grid' && '-mathlib-input-grid' || inputs.core_mode == 'mathlib-input-all' && '-mathlib-input-all' || inputs.core_mode == 'mathlib-input-row1' && '-mathlib-input-row1' || ", '')
            text = text.replace("inputs.core_mode != 'mathlib-input-grid' && inputs.core_mode != 'mathlib-input-all' && inputs.core_mode != 'mathlib-input-row1' && ", '')
            text = text.replace("      input_artifact_lock:\n        description: Parent-adjudicated JSON lock (row1 for grid; rows1..112 for all assembly)\n        type: string\n        default: ''\n", '')
            data = text.encode()
        else:
            data = project_nonproof(rel, data)
        # Preserve the earlier accepted-byte inverse and its immutable checkpoint.
        if rel == 'transformer/mathlib/test_rawpacked.py':
            rule = json.loads(old.PIN_PATH.read_text())['nonproof_source_compatibility'][rel]
            require(digest(data) == rule['current_sha256'], 'previous harness identity')
            inverse = rule['inverse_projection'].encode()
            require(data.count(inverse) == 1, 'previous inverse occurrence')
            data = data.replace(inverse, b'', 1)
        require(digest(data) == expected, 'accepted source drift: ' + rel)


def api_identity(api, lock):
    require(api.get('id') == lock['artifact_id'] and api.get('expired') is False and
            api.get('workflow_run', {}).get('id') == lock['source_run'] and
            api.get('workflow_run', {}).get('head_sha') == lock['source_sha'], 'wrong artifact producer')


def read_ci(archive):
    lock = pin()['ci']
    old.archive_index(archive)
    data = {}
    for name, expected in lock['metadata_sha256'].items():
        require(archive.getinfo(name).file_size < 1_000_000, 'oversized CI metadata')
        value = archive.read(name)
        require(digest(value) == expected, 'CI metadata identity: ' + name)
        data[Path(name).name] = value.decode()
    return data


def validate_ci(data):
    lock = pin()['ci']
    load = lambda n: json.loads(data[n])
    records = [json.loads(s) for s in data['compiled.jsonl'].splitlines()]
    require(records == lock['objects'] and data['compiled.jsonl'] == data['replayed.jsonl'],
            'CI compiled/replayed exact inventory')
    generation = load('generation.json')
    modules, names = ci.inventory()
    require(generation['modules'] == modules and generation['declarations'] == names and
            generation['scope'] == {'CI_components': 512, 'full_hT': False}, 'CI generation scope/inventory')
    require(generation['outputs'] == {m.replace('.', '/') + '.lean': digest(s.encode())
                                    for m, s in ci.sources().items()}, 'CI generator source identity')
    require(generation['negative_sha256'] == digest(ci.negative_source().encode()) and
            data['changed-bin.lean'] == ci.negative_source(), 'CI actual negative source')
    accepted = load('CI_ACCEPTED.json')
    require(accepted['kernel_verdict'] == 'KERNEL_ACCEPTED' and accepted['CI_components'] == 512 and
            accepted['full_hT'] is False and accepted['fresh_compiled_replayed'] == records and
            accepted['restored_previous_compiled_replayed'] == 218 and
            accepted['exact_production_audit_names'] == 2645 and
            accepted['new_support_audit_names'] == 15 and
            accepted['negative_actual_bin_change'] == 'KERNEL_REJECTED_EXIT_1', 'CI acceptance scope')
    import rawcorrespondence_runner as producer
    expected = [*producer.SCALAR_NAMES, *producer.PACKED_NAMES, *producer.old_inventory()[1],
                *ci.SUPPORT_NAMES, *ci.LINEAR_NAMES, *ci.FIXTURE_NAMES, *names]
    for label, wanted in [('complete-CI', expected), ('new-support', [*ci.SUPPORT_NAMES, *ci.LINEAR_NAMES, *ci.FIXTURE_NAMES]),
                          ('representative', [ci.NS + '.representative_affine'])]:
        require(load(label + '-axioms.expected.json') == wanted, 'CI exact audit inventory')
        require(check_correspondence_axioms(data[label + '-axioms.out'], wanted) == len(wanted), 'CI audit')
    provenance = load('provenance.json')
    require(provenance['current_github_sha'] == lock['source_sha'] and
            provenance['compiler_binary_sha256'] == pin()['compiler_binary_sha256'] and
            provenance['toolchain_sha256'] == pin()['toolchain_sha256'] and
            provenance['lake_manifest_sha256'] == pin()['lake_manifest_sha256'], 'CI compiler/provenance')
    for rel, expected_hash in provenance['candidate'].items():
        path = (HERE / rel).resolve()
        relroot = str(path.relative_to(ROOT))
        raw = path.read_bytes()
        if relroot == '.github/workflows/transformer.yml': raw = inverse_workflow(raw.decode()).encode()
        else: raw = project_nonproof(relroot, raw)
        require(digest(raw) == expected_hash, 'CI current source drift: ' + rel)
    steps = [json.loads(s) for s in data['steps.jsonl'].splitlines()]
    require(len({s['name'] for s in steps}) == len(steps), 'duplicate CI producer')
    for r in records:
        m = r['module']; stem = m.replace('.', '/')
        for phase, tail in [('fresh_compile_', ['-o', '.lake/build/lib/lean/' + stem + '.olean', stem + '.lean']),
                            ('fresh_replay_', [m])]:
            selected = [s for s in steps if s['name'] == phase + m]
            require(len(selected) == 1 and selected[0]['exit'] == 0, 'CI missing/failed producer')
            cmd = selected[0]['command']
            require(cmd[:3] == ['lake', 'env', 'lean' if phase == 'fresh_compile_' else 'leanchecker'], 'CI producer command')
            if phase == 'fresh_compile_':
                require(len(cmd) == 6 and cmd[3] == '-o' and cmd[4].endswith('/' + tail[1]) and cmd[5] == tail[2], 'CI compile output path')
            else: require(cmd[3:] == tail, 'CI replay command')
    for label in ('new-support-axioms', 'representative-axioms', 'complete-CI-axioms', 'negative-actual-bin-change'):
        s = next((s for s in steps if s['name'] == label), None)
        require(s is not None and s['command'][:3] == ['lake', 'env', 'lean'] and len(s['command']) == 4,
                'CI audit/control producer')
        filename = 'changed-bin.lean' if label.startswith('negative') else label + '.lean'
        require(s['command'][3].endswith('/rawcorrespondence-out/' + filename) and
                s['exit'] == (1 if label.startswith('negative') else 0), 'CI audit/control exit/path')
    require(re.search(r'decide[\s\S]*false', data['negative-actual-bin-change.out']) is not None,
            'CI negative was not false decision')
    restored = load('restored-previous.json')
    require(restored['archive_sha256'] == json.loads(old.PIN_PATH.read_text())['zip_sha256'] and
            restored['objects'] == pin()['packed_objects'], 'CI packed union provenance')
    return records


def check_imports(data, modules):
    for line in data.decode().splitlines():
        if re.match(r'\s*(?:(?:public|private|meta)\s+)?import\b', line):
            require(bool(re.fullmatch(r'import [A-Za-z0-9_.]+', line)), 'unsupported import')
            dep = line[7:]
            require(dep == 'Mathlib' or dep.startswith('Mathlib.') or dep in modules, 'unverified project import: ' + dep)


def verify_union_sources(archives, records):
    modules = {r['module'] for r in records}
    for r in records:
        rel = r['module'].replace('.', '/') + '.lean'
        values = [z.read(rel) for z in archives if rel in z.namelist()]
        if (HERE / rel).exists(): values.append((HERE / rel).read_bytes())
        require(values and all(digest(v) == r['source_sha256'] for v in values), 'union source/overlap identity: ' + rel)
        check_imports(values[0], modules)


def restore_object(archive, member, dest, expected):
    """Stream one selected proof object and enforce its exact accepted digest."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    h = hashlib.sha256()
    with archive.open(member) as src, dest.open('xb') as dst:
        while True:
            chunk = src.read(1024 * 1024)
            if not chunk: break
            h.update(chunk)
            dst.write(chunk)
    require(h.hexdigest() == expected, 'object drift: ' + member)


def restore(packed_archive, packed_api, ci_archive, ci_api, binaries):
    cloud_only()
    lock = pin(); packed_pin = json.loads(old.PIN_PATH.read_text())
    require(sha(old.PIN_PATH) == lock['packed_pin_sha256'], 'packed pin changed')
    require({n: sha(path) for n, path in binaries.items()} == lock['compiler_binary_sha256'], 'current compiler drift')
    require(sha(HERE / 'lean-toolchain') == lock['toolchain_sha256'] and
            sha(HERE / 'lake-manifest.json') == lock['lake_manifest_sha256'], 'toolchain/manifest drift')
    for archive, api, identity in [(packed_archive, packed_api, packed_pin), (ci_archive, ci_api, lock['ci'])]:
        require(stream_sha(archive) == identity['zip_sha256'], 'archive ZIP identity')
        api_identity(json.loads(Path(api).read_text()), identity)
    base = HERE / '.lake/build/lib/lean'
    for project in ('Transformer', 'TransformerCore', 'TransformerBridge'):
        require(not list((base / project).rglob('*.olean')) and not (base / (project + '.olean')).exists(), 'preexisting proof objects')
    with zipfile.ZipFile(packed_archive) as a, zipfile.ZipFile(ci_archive) as b:
        old.archive_index(a); old.archive_index(b)
        metadata = old.read_metadata(a, packed_pin)
        previous, source, _ = old.validate_metadata(metadata, packed_pin)
        require(previous == lock['packed_objects'], 'packed object lock')
        verify_sources(source)
        current = validate_ci(read_ci(b)); records = previous + current
        require(len(records) == 226 and len({r['module'] for r in records}) == 226, 'union module count/duplicates')
        # Any archive overlap, not just selected sources, must match exactly.
        overlap = set(a.namelist()) & set(b.namelist())
        for name in overlap:
            if not name.endswith('/'): require(a.read(name) == b.read(name), 'archive overlap differs: ' + name)
        verify_union_sources([a, b], records)
        for r in records:
            stem = r['module'].replace('.', '/'); rel = stem + '.lean'
            sources = [z for z in (a, b) if rel in z.namelist()]
            if sources: old.write_exact(HERE / rel, sources[0].read(rel))
            obj = '.lake/build/lib/lean/' + stem + '.olean'
            found = [z for z in (a, b) if obj in z.namelist()]
            require(found, 'missing union object: ' + obj)
            restore_object(found[0], obj, HERE / obj, r['olean_sha256'])
    return {'status': 'RESTORED_AUTHENTICATED_PACKED_AND_CI', 'objects': records,
            'packed_zip_sha256': packed_pin['zip_sha256'], 'ci_zip_sha256': lock['ci']['zip_sha256']}
