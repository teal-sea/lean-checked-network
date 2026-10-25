#!/usr/bin/env python3
"""Generate the same credential-free, unmounted Ubuntu gate for local runs and CI."""
import base64, shlex
from pathlib import Path
root=Path(__file__).resolve().parents[1]
print('set -euo pipefail\nexport HOME=/tmp/reader-home\nmkdir -p "$HOME" /input /reader\ncd /reader')
print('apt-get update -qq\nDEBIAN_FRONTEND=noninteractive apt-get install -y -qq ca-certificates curl git python3 zstd xz-utils build-essential')
for source,name in [(root/'VERIFY.md','VERIFY.md'),(root/'transformer/release-gate.py','gate.py')]:
    data=base64.b64encode(source.read_bytes()).decode()
    print('printf %s '+shlex.quote(data)+' | base64 -d > '+shlex.quote('/input/'+name))
print('exec /usr/bin/env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8 /usr/bin/python3 /input/gate.py')
