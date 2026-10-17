"""Save/verify compiled stable prefix. Verification requires a separately trusted receipt hash.

No automatic restore: a downloaded artifact is untrusted until verify succeeds against
its parent-adjudicated run receipt. Sources, compiler binary, namespace and every olean
are checked; a matching cache key alone is never evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

from row0_receipt import sha

HERE = Path(__file__).resolve().parent


def identity():
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=HERE, text=True).strip()
    return {
        'namespace': 'TransformerCore',
        'compiler': subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=HERE, text=True).strip(),
        'compiler_binary_sha256': sha(Path(lean)),
        'toolchain_sha256': sha(HERE / 'lean-toolchain'),
        'lake_manifest_sha256': sha(HERE / 'lake-manifest.json'),
    }


def save(dest, modules, sources, steps):
    dest.mkdir(parents=True, exist_ok=True)
    record = {**identity(), 'scope': 'stable ROW0 shared prefix; no pair certificates',
              'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=HERE, text=True).strip(),
              'sources': {str(p): sha(HERE / p) for p in sources},
              'modules': [], 'acceptance': 'all listed modules compiled and replayed in this run'}
    for module in modules:
        if not {'build_' + module, 'replay_' + module} <= set(steps):
            raise ValueError('prefix lacks successful build/replay: ' + module)
        rel = Path('.lake/build/lib/lean') / (module.replace('.', '/') + '.olean')
        src = HERE / rel
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, target)
        record['modules'].append({'name': module, 'olean': str(rel), 'sha256': sha(target)})
    raw = (json.dumps(record, indent=2, sort_keys=True) + '\n').encode()
    (dest / 'receipt.json').write_bytes(raw)
    digest = hashlib.sha256(raw).hexdigest()
    (dest / 'receipt.sha256').write_text(digest + '  receipt.json\n')
    return digest


def verify(dest, trusted):
    if sha(dest / 'receipt.json') != trusted:
        raise ValueError('receipt does not match separately trusted run digest')
    record = json.loads((dest / 'receipt.json').read_text())
    if any(record.get(k) != v for k, v in identity().items()):
        raise ValueError('compiler/toolchain/namespace identity mismatch')
    for name, digest in record['sources'].items():
        if sha(HERE / name) != digest:
            raise ValueError('current source mismatch: ' + name)
    names = []
    for item in record['modules']:
        module = item['name']
        expected = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
        if item['olean'] != expected or sha(dest / expected) != item['sha256']:
            raise ValueError('compiled prefix hash/path mismatch: ' + module)
        names.append(module)
    if len(names) != len(set(names)) or not names:
        raise ValueError('bad prefix module inventory')
    return len(names)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifact', type=Path)
    parser.add_argument('--trusted-receipt-sha256', required=True)
    args = parser.parse_args()
    print('verified prefix modules=' + str(verify(args.artifact, args.trusted_receipt_sha256)))
