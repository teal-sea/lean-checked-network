"""Public Actions artifact transport. Parent provides exact adjudicated artifact locks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import zipfile

from input_source import coverage, require
from input_compat import validate_row_policy
from row0_receipt import sha

HERE = Path(__file__).resolve().parent


def validate_lock(lock, full=False):
    require(type(lock) is list and [r.get('row') for r in lock] ==
            (list(range(1, 113)) if full else [1]), 'parent lock must cover exact requested rows')
    for item in lock:
        require(type(item['row']) is int, 'invalid lock row')
        require(set(item) == {'row', 'artifact_id', 'run', 'source_sha', 'zip_sha256'}, 'lock field inventory')
        require(all(type(item[k]) is int and item[k] > 0 for k in ('artifact_id', 'run')), 'invalid lock id')
        for field, n in (('source_sha', 40), ('zip_sha256', 64)):
            require(type(item[field]) is str and re.fullmatch('[0-9a-f]{' + str(n) + '}', item[field]),
                    'invalid lock digest')
    require(len({r['artifact_id'] for r in lock}) == len(lock), 'duplicate row artifact')
    return lock


def fetch(url, path):
    import subprocess
    with path.open('xb') as target:
        subprocess.run(['gh', 'api', url], stdout=target, check=True)


def download(lock, dest, full=False):
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and
            os.environ.get('GITHUB_REPOSITORY') == 'teal-sea/lean-checked-network', 'public Actions only')
    validate_lock(lock, full)
    dest.mkdir(parents=True, exist_ok=False)
    result = []
    for item in lock:
        base = f'https://api.github.com/repos/teal-sea/lean-checked-network/actions/artifacts/{item["artifact_id"]}'
        api, archive = dest / f'{item["row"]}.json', dest / f'{item["row"]}.zip'
        fetch(base, api)
        metadata = json.loads(api.read_text())
        require(metadata.get('id') == item['artifact_id'] and metadata.get('expired') is False and
                metadata.get('workflow_run', {}).get('id') == item['run'] and
                metadata.get('workflow_run', {}).get('head_sha') == item['source_sha'], 'artifact lock API mismatch')
        fetch(base + '/zip', archive)
        with archive.open('rb') as stream:
            require(hashlib.file_digest(stream, 'sha256').hexdigest() == item['zip_sha256'], 'artifact lock ZIP mismatch')
        with zipfile.ZipFile(archive) as z:
            require(len(z.namelist()) == len(set(z.namelist())), 'duplicate ZIP path')
            receipt = json.loads(z.read('input-out/ROW_ACCEPTED.json'))
            require(receipt['status'] == 'KERNEL_ACCEPTED' and receipt['row'] == item['row'] and
                    receipt['source_sha'] == item['source_sha'] and
                    receipt['all_input_coverage'] is False and receipt['fresh_compiled_replayed'] == 11,
                    'parent lock has no accepted complete row')
            validate_row_policy(z, receipt, item, HERE)
            coverage(receipt['pairs'], item['row'])
            if not full:
                measured = json.loads(z.read('input-out/throughput.json'))
                require(measured['throughput_acceptable'] is True and measured['literal_pairs'] == 113 and
                        measured['literal_compile_replay_seconds'] < 927.1758614700007 and
                        measured['literal_peak_rss_kb'] <= 5242880, 'row1 throughput not accepted for fanout')
        result.append({**item, 'archive': str(archive.resolve()), 'api_metadata': str(api.resolve())})
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lock', type=Path, required=True)
    p.add_argument('--dest', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--all', action='store_true')
    a = p.parse_args()
    a.out.write_text(json.dumps(download(json.loads(a.lock.read_text()), a.dest, a.all), indent=2) + '\n')
