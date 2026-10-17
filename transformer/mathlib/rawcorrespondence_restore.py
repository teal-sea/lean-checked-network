"""Adjudicated accepted raw-packed prefix. Import and metadata audit do no Lean/numerics.

Only restore() writes proof objects, and it is guarded by public manual Actions.
The whole pinned ZIP authenticates ancillary bytes; every selected source/object
also has its actual compiled/replayed receipt checked. No Lake rebuild of old rows.
"""
import hashlib
import json
from pathlib import Path
import re
import zipfile

from rawpilot_data import HERE, ROOT, SUPPORT_NAMES as SCALAR_NAMES, sha, verify_pins
from rawpacked_data import (inventory, expected_coefficients, PREFIX, NS,
                            SUPPORT_NAMES as PACKED_NAMES, SHAPES)
from rawpilot_generate import cloud_only
from rawpacked_runner import ANALYTIC
from row0_receipt import check_axioms
import sync_core

PIN_PATH = HERE / 'RawCorrespondence-checkpoint.json'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def stream_sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def expected_modules():
    core = ['TransformerCore.Model', 'TransformerCore.Fast', 'TransformerCore.Equiv']
    support = [*core, *ANALYTIC, 'TransformerBridge.Bridge',
               'TransformerBridge.RawPilotSupport', 'TransformerBridge.RawPackedSupport',
               'TransformerBridge.RawPackedFixture']
    frozen = [m.replace('Transformer', 'TransformerCore', 1)
              for m, *_ in sync_core.inventory(raw_pilot=True)]
    return list(dict.fromkeys([*support, *frozen, *inventory()[0]]))


def archive_index(archive):
    items = archive.infolist()
    names = [i.filename for i in items]
    require(len(names) == len(set(names)), 'duplicate archive path')
    for item in items:
        path = Path(item.filename)
        require(not path.is_absolute() and '..' not in path.parts and '\\' not in item.filename,
                'unsafe archive path')
        require((item.external_attr >> 16) & 0o170000 != 0o120000, 'archive symlink')
    return set(names)


def read_metadata(archive, pin):
    names = archive_index(archive)
    result = {}
    for name, expected in pin['metadata_sha256'].items():
        require(name in names and archive.getinfo(name).file_size < 1_000_000,
                'missing/oversized retained metadata: ' + name)
        data = archive.read(name)
        require(digest(data) == expected, 'retained metadata hash mismatch: ' + name)
        result[name.removeprefix('rawpacked-out/')] = data.decode()
    return result


def validate_metadata(metadata, pin):
    """Strictly exercise the actual retained schemas; no convenient surrogate receipt."""
    load = lambda n: json.loads(metadata[n])
    modules = expected_modules()
    require(len(modules) == 218, 'accepted closure count differs')
    compiled = [json.loads(s) for s in metadata['compiled.jsonl'].splitlines()]
    replayed = [json.loads(s) for s in metadata['replayed.jsonl'].splitlines()]
    require(compiled == replayed and [r['module'] for r in compiled] == modules,
            'exact compiled/replayed ordered inventory mismatch')
    require(all(set(r) == {'module', 'source_sha256', 'olean_sha256'} and
                all(re.fullmatch('[0-9a-f]{64}', r[k]) for k in ('source_sha256', 'olean_sha256'))
                for r in compiled), 'wrong object receipt schema')
    accepted = load('ACCEPTED.json')
    require(accepted['kernel_verdict'] == 'KERNEL_ACCEPTED' and
            accepted['modules_compiled_and_replayed'] == 218 and
            accepted['production_declarations_audited'] == 2614 and
            accepted['support_declarations_audited'] == 21 and
            accepted['negative_changed_production_literal'] == 'KERNEL_REJECTED' and
            accepted['full_hT'] == 'NOT_PROVED', 'wrong historical acceptance scope')
    require(load('accepted-oleans.json') == {r['module']: r['olean_sha256'] for r in compiled},
            'accepted object hash inventory mismatch')
    source = load('sources.json')
    require(source['source_commit'] == pin['source_sha'], 'source SHA mismatch')
    generation = load('generation.json')
    ms, names = inventory()
    paths = [m.replace('.', '/') + '.lean' for m in ms]
    require(generation['modules'] == ms and generation['declarations'] == names and
            len(names) == len(set(names)) and set(generation['outputs']) == set(paths),
            'retained generated inventory mismatch')
    scope = {'head': 0, 'position': 0, 'token': 0, 'TI_components': 512}
    require(generation['scope'] == accepted['scope'] == scope, 'wrong-field retained scope')
    require(generation['coefficients'] == expected_coefficients() and
            generation['shapes'] == {k: list(v) for k, v in SHAPES.items()} and
            generation['pins'] == verify_pins(), 'canonical eleven-field/pin mismatch')
    require(all(generation['outputs'][r['module'].replace('.', '/') + '.lean'] == r['source_sha256']
                for r in compiled if r['module'] in ms), 'generated/compiled source hashes disagree')
    control = generation['negative']
    require(control['field'] == 'Win' and len(control['coordinate']) == 2 and
            0 <= control['coordinate'][0] < 128 and control['coordinate'][1] == 0 and
            control['target_component'] == 0 and control['new'] == control['old'] + 1 and
            control['nonzero_ovec'] != 0, 'retained changed coefficient control differs')
    support_names = [*SCALAR_NAMES, *PACKED_NAMES, *['TransformerBridge.RawPackedFixture.' + n
                     for n in ('carry_collision', 'signed_transport')]]
    production_names = [*SCALAR_NAMES, *PACKED_NAMES, *names]
    for label, expected in [('support', support_names), ('production', production_names)]:
        require(load(label + '-axioms.expected.json') == expected, 'historical exact audit names mismatch')
        require(check_axioms(metadata[label + '-axioms.out'], expected) == len(expected),
                'historical audit incomplete')
    steps = [json.loads(s) for s in metadata['steps.jsonl'].splitlines()]
    for module in modules:
        for phase, command in [('build_', ['lake', 'build', module]),
                               ('replay_', ['lake', 'env', 'leanchecker', module])]:
            found = [r for r in steps if r['name'] == phase + module]
            require(len(found) == 1 and found[0]['exit'] == 0 and found[0]['command'] == command,
                    'missing/duplicate/wrong historical producer: ' + phase + module)
    negative = [r for r in steps if r['name'] == 'negative-changed-production-literal']
    require(len(negative) == 1 and negative[0]['exit'] == 1 and negative[0]['command'] ==
            ['lake', 'env', 'lean', 'rawpacked-out/changed-production-literal.lean'],
            'retained real negative producer differs')
    compiler = load('compiler.json')
    require({k: v['sha256'] for k, v in compiler['binaries'].items()} == pin['compiler_binary_sha256'],
            'historical compiler differs')
    require(compiler['toolchain_sha256'] == sha(HERE / 'lean-toolchain') and
            compiler['lake_manifest_sha256'] == sha(HERE / 'lake-manifest.json'), 'toolchain/manifest drift')
    return compiled, source, compiler


def verify_current_sources(source):
    workflow = '.github/workflows/transformer.yml'
    path = 'transformer/mathlib/test_rawpacked.py'
    pin = json.loads(PIN_PATH.read_text())
    rules = pin['nonproof_source_compatibility']
    require(set(rules) == {path}, 'extra non-proof source exception')
    rule = rules[path]
    require(set(rule) == {'accepted_sha256', 'current_sha256', 'inverse_projection'} and
            rule['accepted_sha256'] == 'cb07a4b7f390225845bcd772aa023a7da643812b5ad7ce4fbf8d564c2206e395' and
            rule['current_sha256'] == '56f725bb4940d093698cf39096d36e268d82c86fdda11267a29fc655b230a611' and
            source['sources'][path] == rule['accepted_sha256'], 'non-proof source identities')
    for rel, expected in source['sources'].items():
        if rel == workflow:
            continue
        if rel == path:
            data = (ROOT / rel).read_bytes()
            require(digest(data) == rule['current_sha256'], 'unknown harness change')
            inverse = rule['inverse_projection'].encode()
            require(inverse and data.count(inverse) == 1 and
                    digest(data.replace(inverse, b'', 1)) == expected,
                    'harness inverse does not restore accepted bytes')
        else:
            require(sha(ROOT / rel) == expected, 'accepted load-bearing source changed: ' + rel)
    return {'path': workflow, 'accepted_sha256': source['sources'][workflow],
            'current_sha256': sha(ROOT / workflow), 'nonproof_source_compatibility': rules}


def write_exact(path, data):
    if path.exists():
        require(path.is_file() and path.read_bytes() == data, 'existing source differs: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def restore(archive_path, api_path, compiler_paths):
    cloud_only()
    pin = json.loads(PIN_PATH.read_text())
    require(stream_sha(archive_path) == pin['zip_sha256'], 'archive digest mismatch')
    api = json.loads(api_path.read_text())
    require(api.get('id') == pin['artifact_id'] and api.get('expired') is False and
            api.get('workflow_run', {}).get('id') == pin['source_run'] and
            api.get('workflow_run', {}).get('head_sha') == pin['source_sha'], 'artifact identity mismatch')
    require({k: sha(p) for k, p in compiler_paths.items()} == pin['compiler_binary_sha256'],
            'current compiler binary mismatch')
    for project in ('Transformer', 'TransformerCore', 'TransformerBridge'):
        base = HERE / '.lake/build/lib/lean'
        require(not list((base / project).rglob('*.olean')) and not (base / (project + '.olean')).exists(),
                'preexisting project proof objects: ' + project)
    with zipfile.ZipFile(archive_path) as archive:
        metadata = read_metadata(archive, pin)
        records, source, compiler = validate_metadata(metadata, pin)
        workflow = verify_current_sources(source)
        names = archive_index(archive)
        # Validate every source hash and closed project import before writing; objects are streamed and checked below.
        module_set = {r['module'] for r in records}
        for record in records:
            rel = record['module'].replace('.', '/') + '.lean'
            if rel in names:
                data = archive.read(rel)
            else:
                data = (HERE / rel).read_bytes()
            require(digest(data) == record['source_sha256'], 'retained source differs: ' + rel)
            for line in data.decode().splitlines():
                if re.match(r'^\s*(?:(?:public|private|meta)\s+)?import\b', line):
                    require(bool(re.fullmatch(r'import [A-Za-z0-9_.]+', line)), 'unsupported import: ' + rel)
                    dep = line[7:]
                    require(dep == 'Mathlib' or dep.startswith('Mathlib.') or dep in module_set,
                            'unverified project import: ' + dep)
        # Stream selected sources and objects. Never extractall or restore foreign paths/traces.
        for record in records:
            stem = record['module'].replace('.', '/')
            rel = stem + '.lean'
            if rel in names:
                write_exact(HERE / rel, archive.read(rel))
            obj = '.lake/build/lib/lean/' + stem + '.olean'
            dest = HERE / obj
            dest.parent.mkdir(parents=True, exist_ok=True)
            h = hashlib.sha256()
            with archive.open(obj) as src, dest.open('xb') as dst:
                while chunk := src.read(1024 * 1024):
                    h.update(chunk)
                    dst.write(chunk)
            require(h.hexdigest() == record['olean_sha256'], 'retained object differs: ' + obj)
        # Check exact original namespace mirrors against the untouched frozen sources.
        for _, _, rel, _, expected in sync_core.inventory(raw_pilot=True):
            require((HERE / rel).read_bytes() == expected, 'frozen/default-slot mirror differs: ' + rel)
    return {'status': 'RESTORED_PREVIOUS_COMPILED_REPLAYED', 'source_run': pin['source_run'],
            'source_sha': pin['source_sha'], 'objects': records, 'workflow_extension': workflow,
            'metadata_sha256': pin['metadata_sha256'], 'archive_sha256': pin['zip_sha256']}
