"""BRIDGE SCAN HARNESS: fake build/replay commands; no Lean proof evidence."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent / 'mathlib/bridge.sh'


def run_scan(case):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        mathlib = root / 'mathlib'
        lean = root / 'lean'
        bin_dir = root / 'bin'
        for directory in (mathlib / 'TransformerCore', mathlib / 'TransformerBridge', lean, bin_dir):
            directory.mkdir(parents=True)
        (mathlib / 'bridge.sh').write_bytes(BRIDGE.read_bytes())
        (lean / 'scan_sources.sh').write_bytes((HERE / 'scan_sources.sh').read_bytes())
        (lean / 'scan_sources.sh').chmod(0o755)
        for name in ('TransformerCore/Core.lean', 'TransformerBridge/Bridge.lean',
                     'TransformerCore.lean', 'TransformerBridge.lean'):
            (mathlib / name).write_text('def fixture := 1\n')
        if case == 'forbidden':
            (mathlib / 'TransformerCore/Core.lean').write_text('theorem fixture : True := by sorry\n')
        elif case == 'missing':
            (mathlib / 'TransformerBridge.lean').unlink()
        scripts = {
            mathlib / 'sync_core.sh': '#!/bin/bash\nexit 0\n',
            bin_dir / 'timeout': '#!/bin/bash\nshift 5\n"$@"\n',
            bin_dir / 'lake': r'''#!/bin/bash
printf '%s\n' "$*" >> "$TRACE"
if [ "$1 $2" = 'env lean' ]; then
  while IFS= read -r line; do
    case "$line" in '#print axioms '*) printf "'%s' does not depend on any axioms\n" "${line#\#print axioms }" ;; esac
  done < "$3"
fi
exit 0
''',
        }
        for path, source in scripts.items():
            path.write_text(source)
            path.chmod(0o755)
        env = {**os.environ, 'HOME': tmp, 'PATH': f'{bin_dir}:/usr/bin:/bin',
               'TRACE': str(root / 'trace')}
        result = subprocess.run(['bash', str(mathlib / 'bridge.sh')], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=10)
        scan = (mathlib / 'bridge-out/scan.out').read_text()
        trace = (root / 'trace').read_text()
        assert '4 of 4 theorems on standard axioms or none' in result.stdout
        assert 'env leanchecker TransformerBridge.Bridge' in trace
        assert result.returncode == (0 if case == 'clean' else 1), result.stdout
        assert ('none found' in result.stdout) == (case == 'clean'), result.stdout
        if case == 'forbidden':
            assert 'by sorry' in scan
        if case == 'missing':
            assert 'TransformerBridge.lean' in scan and scan.strip()


for case in ('clean', 'forbidden', 'missing'):
    run_scan(case)
print('ok: BRIDGE SCAN HARNESS (fake commands): clean scan 0 succeeds; forbidden 1 and missing/error 2 fail; four axiom checks and replay retained')


# VERIFY SCAN HARNESS: execute the actual sibling script with isolated FAKE
# commands. This checks shell gates only; it provides no Lean proof evidence.
def run_verify(case, failure=''):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        mathlib = root / 'mathlib'
        lean = root / 'lean'
        bin_dir = root / 'bin'
        for directory in (mathlib / 'Transformer', lean, bin_dir):
            directory.mkdir(parents=True)
        source = HERE.parent / 'mathlib'
        for name in ('verify.sh', 'axioms_all.lean', 'lean-toolchain'):
            (mathlib / name).write_bytes((source / name).read_bytes())
        (mathlib / 'lake-manifest.json').write_text('{"name": "mathlib", "rev": "fake"}\n')
        scanner = lean / 'scan_sources.sh'
        scanner.write_bytes((HERE / 'scan_sources.sh').read_bytes())
        scanner.chmod(0o755)
        modules = ['Transformer.ExpFix', 'Transformer.Program', 'Transformer.Logits',
                   'Transformer.Compose', 'Transformer.Raw']
        for module in modules:
            (mathlib / (module.replace('.', '/') + '.lean')).write_text('def fixture := 1\n')
        (mathlib / 'Transformer.lean').write_text('import Transformer.Raw\n')
        if case == 'forbidden':
            (mathlib / 'Transformer/Raw.lean').write_text('theorem fixture : True := by sorry\n')
        elif case == 'missing':
            (mathlib / 'Transformer.lean').unlink()
        scripts = {
            'flock': '#!/bin/bash\nshift\nexec "$@"\n',
            'lean': '#!/bin/bash\necho "FAKE lean version (harness only)"\n',
            'lake': r'''#!/bin/bash
printf '%s\n' "$*" >> "$TRACE"
if [ "$1" = build ]; then
  [ "$FAILURE" != build ] || exit 1
  echo 'Build completed (FAKE harness command)'
elif [ "$1 $2" = 'env leanchecker' ]; then
  [ "$FAILURE" != replay ] || exit 1
elif [ "$1 $2" = 'env lean' ]; then
  n=0
  while IFS= read -r line; do
    case "$line" in '#print axioms '*)
      n=$((n+1))
      if [ "$FAILURE" != short-audit ] || [ "$n" -ne 64 ]; then
        printf "'%s' does not depend on any axioms\n" "${line#\#print axioms }"
      fi ;;
    esac
  done < "$3"
fi
exit 0
''',
        }
        for name, script in scripts.items():
            path = bin_dir / name
            path.write_text(script)
            path.chmod(0o755)
        env = {**os.environ, 'HOME': tmp, 'PATH': f'{bin_dir}:/usr/bin:/bin',
               'LEAN_LOCK': str(root / 'fake.lock'), 'TRACE': str(root / 'trace'),
               'FAILURE': failure}
        result = subprocess.run(['bash', str(mathlib / 'verify.sh')], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=10)
        expected_scan = {'clean': 0, 'forbidden': 1, 'missing': 2}[case]
        assert f'source scan exit {expected_scan}' in result.stdout, result.stdout
        assert result.returncode == (0 if case == 'clean' and not failure else 1), result.stdout
        assert ('none found' in result.stdout) == (case == 'clean'), result.stdout
        trace = (root / 'trace').read_text().splitlines()
        assert trace == ([f'build {m}' for m in modules] + ['build Transformer']
                         + [f'env leanchecker {m}' for m in modules]
                         + ['env lean axioms_all.lean']), trace
        assert f'replayed {0 if failure == "replay" else 5} of 5 modules' in result.stdout
        count = 63 if failure == 'short-audit' else 64
        assert f'{count} of {count} theorems use only standard axioms or none (64 asked)' in result.stdout
        scan = (mathlib / 'scan.out').read_text()
        if case == 'forbidden':
            assert 'by sorry' in scan
        elif case == 'missing':
            assert 'Transformer.lean' in scan and scan.strip()
        else:
            assert not scan


for case in ('clean', 'forbidden', 'missing'):
    run_verify(case)
for failure in ('build', 'replay', 'short-audit'):
    run_verify('clean', failure)
print('ok: VERIFY SCAN HARNESS (FAKE commands, no Lean evidence): scan exits 0/1/2; '
      'five module builds/replays, root build, 64 axiom checks; build/replay/short-audit failures gated')
