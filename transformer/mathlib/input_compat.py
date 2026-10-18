"""Narrow compatibility for the actual row1 run on a01a98c; never relabel its head."""
import hashlib
import json
from pathlib import Path
from input_source import require

OLD_POLICY = '973c59ef5ef51ab94a1d102a2daccf20f70c53a2b08591fb030ee492c05fdbd4'
OLD_HEAD = 'a01a98c7be5b37fce861cb44224d2b099bb8c49a'
OLD_RUN = 39076009834
GRID_RUN = 39077248982
DELTAS = {'../../.github/workflows/transformer.yml', 'row0_checkpoint.json',
          'test_rawpacked.py', 'test_row0_finalize.py', 'test_input_coverage.py',
          'test_input_harness.py', 'input_runner.py', 'input_artifacts.py'}
ADDITIONS = {'RawGRange-checkpoint.json', 'rawgrange_generate.py', 'rawgrange_restore.py', 'rawgrange_runner.py', 'rawgrange.sh', 'test_rawgrange.py', 'RawGPilot-checkpoint.json', 'rawgpilot_generate.py', 'rawgpilot_restore.py', 'rawgpilot_runner.py', 'rawgpilot.sh', 'test_rawgpilot.py', 'RawCUFull-checkpoint.json', 'rawcufull_generate.py', 'rawcufull_restore.py',
    'rawcufull_runner.py', 'rawcufull.sh', 'test_rawcufull.py', 'TransformerBridge/RawCUUpdate.lean', 'RawURange-checkpoint.json', 'rawurange_generate.py', 'rawurange_restore.py',
    'rawurange_runner.py', 'rawurange.sh', 'test_rawurange.py', 'RawUBoundary-checkpoint.json', 'rawuboundary_generate.py',
    'rawuboundary_restore.py', 'rawuboundary_runner.py', 'rawuboundary.sh', 'test_rawuboundary.py', 'RawCU-checkpoint.json', 'rawcu_generate.py', 'rawcu_restore.py',
    'rawcu_runner.py', 'rawcu.sh', 'test_rawcu.py', 'RawCorrespondence-checkpoint.json', 'rawcorrespondence_generate.py',
    'rawcorrespondence_restore.py', 'rawcorrespondence_runner.py', 'rawcorrespondence.sh',
    'test_rawcorrespondence.py', 'TransformerBridge/RawCorrespondenceSupport.lean',
    'TransformerBridge/RawCorrespondenceLinear.lean', 'TransformerBridge/RawCorrespondenceFixture.lean',
    'input_compat.py', 'test_input_compat.py', 'input_policy_a01a98c.json',
    'input_checkpoint_a01a98c.json'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def validate_row_policy(archive, receipt, item, here):
    here = Path(here)
    current_bytes = (here / 'input_policy.json').read_bytes()
    current = json.loads(current_bytes)
    require(set(current) == {'row0', 'sources', 'compatibility_sha256'}, 'current policy schema')
    for path, expected in current['sources'].items():
        require(digest((here / path).read_bytes()) == expected, 'current policy source drift: ' + path)
    # Actual upload-artifact LCA is transformer/mathlib: policy is at ZIP root.
    archived_bytes = archive.read('input_policy.json')
    archived_hash = digest(archived_bytes)
    require(receipt['policy_sha256'] == archived_hash, 'archived policy bytes/receipt mismatch')
    require(receipt['source_sha'] == item['source_sha'], 'receipt/lock head mismatch')
    raw = (here / 'input_policy_compatibility.json').read_bytes()
    require(digest(raw) == current['compatibility_sha256'], 'compatibility record identity')
    record = json.loads(raw)
    require(receipt['compiler'] == record['compiler'], 'row compiler identity')
    if archived_hash == digest(current_bytes):
        require(archived_bytes == current_bytes, 'current policy byte mismatch')
        return 'CURRENT_POLICY'
    require(archived_hash == OLD_POLICY and
            archived_bytes == (here / 'input_policy_a01a98c.json').read_bytes(), 'unknown archived policy')
    require(item['source_sha'] == OLD_HEAD and type(item['run']) is int and
            type(item['row']) is int and type(receipt['row']) is int and
            receipt['row'] == item['row'] and
            ((item['row'] == 1 and item['run'] == OLD_RUN) or
             (2 <= item['row'] <= 112 and item['run'] == GRID_RUN)), 'old policy limited to exact original row1 run/head')
    require(set(record) == {'old_policy_sha256', 'source_sha', 'runs', 'deltas', 'additions', 'compiler'} and
            record['old_policy_sha256'] == OLD_POLICY and record['source_sha'] == OLD_HEAD and
            record['runs'] == {'row1': OLD_RUN, 'rows2_112': GRID_RUN}, 'compatibility provenance')
    old = json.loads(archived_bytes)
    old_checkpoint_bytes = archive.read('row0_checkpoint.json')
    require(digest(old_checkpoint_bytes) == old['sources']['row0_checkpoint.json'] and
            old_checkpoint_bytes == (here / 'input_checkpoint_a01a98c.json').read_bytes(),
            'old checkpoint identity')
    old_checkpoint = json.loads(old_checkpoint_bytes)
    current_checkpoint = json.loads((here / 'row0_checkpoint.json').read_bytes())
    old_checkpoint['source_exceptions']['../../.github/workflows/transformer.yml']['candidate_sha256'] = \
        current_checkpoint['source_exceptions']['../../.github/workflows/transformer.yml']['candidate_sha256']
    require(old_checkpoint == current_checkpoint, 'checkpoint proof/compiler/object pins changed')
    require(set(old) == {'row0', 'sources'} and current['row0'] == old['row0'], 'shared frozen pins changed')
    require(set(record['deltas']) == DELTAS and set(record['additions']) == ADDITIONS,
            'unknown compatibility source change')
    expected = dict(old['sources'])
    for path, delta in record['deltas'].items():
        require(set(delta) == {'old_sha256', 'current_sha256'} and
                delta['old_sha256'] == expected[path] and
                delta['current_sha256'] != delta['old_sha256'], 'incorrect recorded source delta')
        expected[path] = delta['current_sha256']
    for path, value in record['additions'].items():
        require(path not in expected, 'addition overwrites original source')
        expected[path] = value
    require(expected == current['sources'], 'unrecorded source/pin delta')
    return 'PINNED_A01_ROW1_POLICY'
