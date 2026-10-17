"""Tiny fixtures and FAKE build/replay commands. NEVER kernel proof evidence."""
import hashlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sync_core', HERE / 'sync_core.py')
sync = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sync)
spec = importlib.util.spec_from_file_location('check_bounds_audit', HERE / 'check_bounds_audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def rejected(text):
    try:
        audit.check(text)
    except ValueError:
        return
    raise AssertionError('bad audit accepted')


good = ''.join(f"'{name}' does not depend on any axioms\n" for name in audit.EXPECTED)
assert audit.check(good) == 10
rejected('\n'.join(good.splitlines()[:-1]))
rejected(good.replace(audit.EXPECTED[-1], audit.EXPECTED[0]))
rejected(good.replace(audit.EXPECTED[-1], 'Wrong.theorem'))
rejected(good.replace('does not depend on any axioms', 'depends on axioms: [False.intro]', 1))
rejected(good + 'unexpected output\n')
assert len(sync.inventory()) == 3
assert len(sync.inventory(support=True)) == 4
assert len(sync.inventory(True)) == 30
for _, _, _, source, target in sync.inventory(True):
    assert target == sync.re.sub(rb'\bTransformer\b', b'TransformerCore', source)
# Unsupported import must fail rather than silently grow the trusted input set.
original_base = sync.BASE
with tempfile.TemporaryDirectory() as tmp:
    sync.BASE = Path(tmp)
    (sync.BASE / 'Transformer').mkdir()
    (sync.BASE / 'Transformer/Model.lean').write_text('import Transformer.Net.Cached\n')
    try:
        sync.inventory()
    except ValueError as error:
        assert 'out-of-scope import' in str(error)
    else:
        raise AssertionError('unapproved import accepted')
sync.BASE = original_base


def run(failure=''):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        mathlib, lean, bin_dir = (root / p for p in ('transformer/mathlib', 'transformer/lean', 'bin'))
        for p in (mathlib, lean, bin_dir):
            p.mkdir(parents=True)
        for name in ('bounds.sh', 'bridge.sh', 'sync_core.sh', 'sync_core.py',
                     'bounds_axioms.lean', 'check_bounds_audit.py'):
            dst = mathlib / name
            dst.write_bytes((HERE / name).read_bytes())
            dst.chmod(0o755)
        scanner = lean / 'scan_sources.sh'
        scanner.write_bytes((HERE.parent / 'lean/scan_sources.sh').read_bytes())
        scanner.chmod(0o755)
        # Thirty very small fixtures retain only the actual modules' import graph.
        for module, _, _, source, _ in sync.inventory(True):
            p = lean / (module.replace('.', '/') + '.lean')
            p.parent.mkdir(parents=True, exist_ok=True)
            imports = [line for line in source.decode().splitlines() if line.startswith('import ')]
            p.write_text('\n'.join(imports) + '\ndef fixture := 1\n')
        frozen_names = [line.split()[1] for line in
                        (HERE.parent / 'lean/cached-inputs.sha256').read_text().splitlines()]
        for name in frozen_names:
            path = lean / name
            if not path.exists():
                path.write_text('fixture only\n')
        digest = ''.join(f'{hashlib.sha256((lean / name).read_bytes()).hexdigest()}  {name}\n'
                         for name in frozen_names)
        (lean / 'cached-inputs.sha256').write_text(digest)
        if failure == 'hash':
            (lean / frozen_names[0]).write_text('altered fixture\n')
        for name in ('TransformerBridge/Bridge.lean', 'TransformerBridge/Bounds.lean',
                     'TransformerBridge/FrozenBounds.lean',
                     'TransformerBridge.lean', 'TransformerCore.lean'):
            p = mathlib / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('def fixture := 1\n')
        if failure == 'scan':
            (mathlib / 'TransformerBridge/Bounds.lean').write_text('theorem fixture : True := by sorry\n')
        elif failure == 'missing':
            (mathlib / 'TransformerBridge/Bounds.lean').unlink()
        (root / '.github/workflows').mkdir(parents=True)
        (root / '.github/workflows/transformer.yml').write_text('fixture workflow only\n')
        (mathlib / 'test_bounds_harness.py').write_text('fixture harness only\n')
        scripts = {
            'python3': f'#!/bin/bash\nexec {sys.executable} "$@"\n',
            'timeout': '#!/bin/bash\nshift 5\nexec "$@"\n',
            'sha256sum': f'''#!{sys.executable}
import hashlib
from pathlib import Path
import sys
if sys.argv[1] == '-c':
    for line in Path(sys.argv[2]).read_text().splitlines():
        digest, name = line.split()
        if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
            sys.exit(1)
else:
    for name in sys.argv[1:]:
        print(hashlib.sha256(Path(name).read_bytes()).hexdigest() + '  ' + name)
''',
            'lake': r'''#!/bin/bash
printf '%s\n' "$*" >> "$TRACE"
if [ "$FAILURE" = generic-build ] && [ "$*" = 'build TransformerBridge.Bounds' ]; then exit 42; fi
if [ "$FAILURE" = build ] && [ "$*" = 'build TransformerCore.Net.Table' ]; then exit 42; fi
if [ "$FAILURE" = replay ] && [ "$*" = 'env leanchecker TransformerBridge.Bounds' ]; then exit 42; fi
if [ "$1 $2" = 'env lean' ]; then
  if [[ "$3" == *negative.lean ]]; then
    if [ "$FAILURE" = negative-success ]; then exit 0; fi
    if [ "$FAILURE" = negative-timeout ]; then exit 124; fi
    if [ "$FAILURE" = negative-import ]; then echo 'error: unknown module'; exit 1; fi
    echo "error: tactic 'decide' proved that the proposition is false (FAKE fixture)"; exit 1
  fi
  if [ "$3" = bounds_axioms.lean ] && [ "$FAILURE" = audit-exit ]; then exit 42; fi
  n=0
  while IFS= read -r line; do
    case "$line" in '#print axioms '*)
      n=$((n+1))
      if [ "$3" = bounds_axioms.lean ] && [ "$FAILURE" = short-audit ] && [ "$n" -eq 10 ]; then continue; fi
      printf "'%s' does not depend on any axioms\n" "${line#\#print axioms }" ;;
    esac
  done < "$3"
fi
exit 0
''',
        }
        for name, source in scripts.items():
            p = bin_dir / name
            p.write_text(source)
            p.chmod(0o755)
        env = {**os.environ, 'HOME': tmp, 'PATH': f'{bin_dir}:/usr/bin:/bin',
               'TRACE': str(root / 'trace'), 'FAILURE': failure,
               'LEAN_NUM_THREADS': '3' if failure == 'threads' else '2'}
        # No real numeric mirrors are generated by this harness.
        result = subprocess.run(['bash', str(mathlib / 'bounds.sh')], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=30)
        success = not failure
        assert (result.returncode == 0) == success, result.stdout
        accepted = 'bounds status=KERNEL_ACCEPTED selected-declarations=10/10 replayed=33/33'
        assert (accepted in result.stdout) == success, result.stdout
        if failure == 'generic-build':
            trace = (root / 'trace').read_text().splitlines()
            assert trace[-1] == 'build TransformerBridge.Bounds'
            assert not any('TransformerCore.Net.' in line for line in trace)
            assert not (mathlib / 'TransformerCore/Net').exists()
            assert not (mathlib / 'bounds-out/sync.tsv').exists()
        if success:
            trace = (root / 'trace').read_text().splitlines()
            assert len([line for line in trace if line.startswith('env leanchecker ')]) == 34
            generic = trace.index('build TransformerBridge.Bounds')
            for module, *_ in sync.inventory(support=True):
                assert trace.index('build ' + module.replace('Transformer', 'TransformerCore', 1)) < generic
            assert trace.index('build TransformerBridge.Bridge') < generic
            for module, *_ in sync.inventory(True):
                if '.Net.' in module:
                    assert generic < trace.index('build ' + module.replace('Transformer', 'TransformerCore', 1))
            # The library aggregate must see all numeric modules already built.
            aggregate = trace.index('build TransformerCore')
            for module, *_ in sync.inventory(True):
                renamed = module.replace('Transformer', 'TransformerCore', 1)
                assert trace.index('build ' + renamed) < aggregate
            assert 'env lean bounds-out/negative.lean' in trace
            assert 'selected-declarations=10/10 status=OK' in result.stdout
        return result.stdout


for failure in ('', 'hash', 'scan', 'missing', 'generic-build', 'build', 'replay', 'audit-exit',
                'short-audit', 'negative-success', 'negative-timeout', 'negative-import', 'threads'):
    run(failure)
print('ok: BOUNDS HARNESS ONLY (FAKE kernel commands): 13 paths; hash, scan/missing, build, replay, '
      'audit exit/short audit, negative success/timeout/import failure, thread cap; '
      'exact 10-declaration audit and 3/4/30-module byte-rename inventories; generic-before-numeric ordering. NO Lean acceptance evidence.')
