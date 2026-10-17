"""Harness unit tests with fake commands. These are NEVER Lean proof evidence."""
import os
from pathlib import Path
import subprocess
import tempfile

SOURCE = Path(__file__).with_name('smoke.sh').read_text()
PAIRS = ['0_0', '0_112', '96_73']


def run(source=SOURCE, mode='pair-pilot', fail='', threads='2'):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        bin_dir = root / 'bin'
        bin_dir.mkdir()
        trace = root / 'trace'
        # GNU time and Linux monitoring are replaced only in this isolated fixture.
        source = source.replace('/usr/bin/time', str(bin_dir / 'fake-time'))
        source = source.replace('mon 2>&1 | tee -a "$out/monitor.log" &', 'true &')
        start = source.index('dump() {')
        end = source.index('# shellcheck disable=SC2329', start)
        source = source[:start] + 'dump() { :; }\n' + source[end:]
        (root / 'smoke.sh').write_text(source)
        (root / 'lean-toolchain').write_text('fixture only\n')
        (root / 'Transformer/Net/W').mkdir(parents=True)
        scripts = {
            'fake-time': '''#!/bin/bash
shift; shift; dest=$1; shift
"$@"; rc=$?
printf 'Elapsed (wall clock) time (h:mm:ss or m:ss): fixture\nMaximum resident set size (kbytes): 0\n' > "$dest"
exit "$rc"
''',
            'timeout': '''#!/bin/bash
printf '%s\n' "$*" >> "$TRACE"
shift 5
"$@"
''',
            'lake': r'''#!/bin/bash
if [ -n "$FAIL_COMMAND" ] && [[ "$*" == *"$FAIL_COMMAND" ]]; then exit 42; fi
if [ "$*" = 'env lean cache-red.lean' ]; then echo "error: decide rejected altered literal"; exit 1; fi
if [ "$1 $2" = 'env lean' ]; then
  while read -r line; do
    case "$line" in '#print axioms '*) printf "'%s' does not depend on any axioms\n" "${line#\#print axioms }" ;; esac
  done < "$3"
fi
exit 0
''',
            'lean': '#!/bin/bash\necho fixture-version\n',
            'sha256sum': '#!/bin/bash\nexit 0\n',
            'scan_sources.sh': '#!/bin/bash\nexit 0\n',
            'python3': '''#!/bin/bash
if [ -n "$FAIL_COMMAND" ] && [[ "$*" == *"$FAIL_COMMAND" ]]; then exit 42; fi
mkdir -p ci-out/cache-codegen
printf '%s\n' Transformer.Net.CachedUnits.Fixture_000 Transformer.Net.CachedUnits.Fixture Transformer.Net.Cached > ci-out/cache-codegen/modules.txt
printf '%s\n' Transformer/Net/Cached.lean > ci-out/cache-codegen/sources.txt
printf '%s\n' Transformer.Net.Cached.eq_fixture Transformer.Net.Cached.cache_eq > ci-out/cache-codegen/axioms.txt
''',
        }
        for name, text in scripts.items():
            path = (root if name == 'scan_sources.sh' else bin_dir) / name
            path.write_text(text)
            path.chmod(0o755)
        env = {**os.environ, 'PATH': f'{bin_dir}:/usr/bin:/bin', 'HOME': tmp,
               'TRACE': str(trace), 'FAIL_COMMAND': fail, 'CORE_MODE': mode, 'LEAN_NUM_THREADS': threads}
        result = subprocess.run(['bash', str(root / 'smoke.sh')], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=20)
        gates = trace.read_text().splitlines() if trace.exists() else []
        status = (root / 'ci-out/STATUS.txt').read_text() if (root / 'ci-out/STATUS.txt').exists() else ''
        return result.returncode, gates, status


def accepted(result):
    rc, gates, status = result
    assert rc == 0, (rc, gates, status)
    assert 'PAIR PILOT accepted; row0 remains unproved' in status
    assert not any('Rows' in g or 'AllInputs' in g for g in gates), gates
    assert [g for g in gates if 'lake build Transformer.Net.Pair' in g] == [
        f'-s TERM -k 20 300 lake build Transformer.Net.Pair{p}' for p in PAIRS]
    assert [g for g in gates if 'leanchecker Transformer.Net.Pair' in g] == [
        f'-s TERM -k 20 300 lake env leanchecker Transformer.Net.Pair{p}' for p in PAIRS]
    for target in ('Table', 'Cols'):
        assert any(f'leanchecker Transformer.Net.{target}' in g for g in gates)
    assert any('lake env lean ci-out/axioms.lean' in g for g in gates)


def assert_failed(result, failure):
    rc, gates, status = result
    assert rc != 0 and failure in gates[-1] and 'FAILED' in status, (failure, rc, gates, status)


accepted(run())
# Every failed proof/check must stop immediately, preserve failure, and withhold acceptance.
for failure in [f'build Transformer.Net.Pair{p}' for p in PAIRS] + [
        f'leanchecker Transformer.Net.Pair{p}' for p in PAIRS] + [
        'build Transformer.Net.Cols', 'env lean ci-out/axioms.lean',
        'leanchecker Transformer.Equiv', 'leanchecker Transformer.Net.Table', 'leanchecker Transformer.Net.Cols']:
    rc, gates, status = run(fail=failure)
    assert_failed((rc, gates, status), failure)
# Full-row mode is available explicitly; no pair module is used to discharge its row theorem.
rc, gates, status = run(mode='full-row')
assert rc == 0 and any('build Transformer.Net.Rows00' in g for g in gates)
assert any('leanchecker Transformer.Net.Rows00' in g for g in gates)
assert not any('Net.Pair' in g for g in gates)
assert 'rows 1..112 and all-input acceptance unproved' in status
assert run(mode='typo')[0] == 2
assert run(threads='3')[0] == 2
# Red controls: the acceptance oracle catches a skipped pilot and an accidental full row launch.
for broken in [SOURCE.replace('for pair in 0_0 0_112 96_73', 'for pair in 0_0 96_73'),
               SOURCE.replace('gate build_cols 900', 'gate unexpected_row 300 lake build Transformer.Net.Rows00 || stop\ngate build_cols 900')]:
    try:
        accepted(run(broken))
    except AssertionError:
        pass
    else:
        raise AssertionError('broken harness accepted')
# Red control: swallowing a pair exit must be rejected by the failure oracle.
swallowed = SOURCE.replace('"Transformer.Net.Pair$pair" || stop', '"Transformer.Net.Pair$pair" || true')
try:
    assert_failed(run(swallowed, fail='build Transformer.Net.Pair0_0'), 'build Transformer.Net.Pair0_0')
except AssertionError:
    pass
else:
    raise AssertionError('swallowed pair exit accepted')
print('ok: HARNESS UNIT TESTS (fake commands, no Lean evidence): pair budgets/order, replay, failure propagation, full-row mode, red controls')


def cached_accepted(result):
    rc, gates, status = result
    assert rc == 0 and 'CACHED PAIR PILOT accepted; row0 remains unproved' in status, result
    assert not any('Rows' in g or 'AllInputs' in g or 'Net.Pair' in g for g in gates)
    for target in ('Transformer.Cached', 'Transformer.CachedFixture',
                   'Transformer.Net.CachedUnits.Fixture_000', 'Transformer.Net.CachedUnits.Fixture',
                   'Transformer.Net.Cached'):
        assert any(g.endswith('lake build ' + target) for g in gates), target
        assert any(g.endswith('lake env leanchecker ' + target) for g in gates), target
    assert [g for g in gates if 'lake build Transformer.Net.CachedPair' in g] == [
        f'-s TERM -k 20 300 lake build Transformer.Net.CachedPair{p}' for p in PAIRS]
    assert [g for g in gates if 'leanchecker Transformer.Net.CachedPair' in g] == [
        f'-s TERM -k 20 300 lake env leanchecker Transformer.Net.CachedPair{p}' for p in PAIRS]
    assert gates.index('-s TERM -k 20 600 lake env leanchecker Transformer.Net.Cached') < gates.index(
        '-s TERM -k 20 300 lake build Transformer.Net.CachedPair0_0')
    assert any('lake env lean cache-red.lean' in g for g in gates)
    assert any('python3 gen_cached.py --out .' in g for g in gates)
    assert any(g.endswith('python3 gen_cached.py --out . --check') for g in gates)


cached_accepted(run(mode='cached-pair-pilot'))
for failure in ['build Transformer.Cached', 'leanchecker Transformer.Cached',
                'build Transformer.CachedFixture', 'leanchecker Transformer.CachedFixture',
                'gen_cached.py --out .', 'gen_cached.py --out . --check',
                'build Transformer.Net.CachedUnits.Fixture_000',
                'leanchecker Transformer.Net.CachedUnits.Fixture_000',
                'build Transformer.Net.CachedUnits.Fixture',
                'leanchecker Transformer.Net.CachedUnits.Fixture',
                'build Transformer.Net.Cached', 'leanchecker Transformer.Net.Cached'] + [
                f'build Transformer.Net.CachedPair{p}' for p in PAIRS] + [
                f'leanchecker Transformer.Net.CachedPair{p}' for p in PAIRS] + [
                'env lean ci-out/axioms.lean']:
    assert_failed(run(mode='cached-pair-pilot', fail=failure), failure)
# Expected rejection must never admit success, timeout, or a failed proof runner.
assert_failed(run(SOURCE.replace('cache-red.lean', 'cache-red-accepted.lean'),
                  mode='cached-pair-pilot'), 'env lean cache-red-accepted.lean')
assert_failed(run(mode='cached-pair-pilot', fail='env lean cache-red.lean'),
              'env lean cache-red.lean')
for broken in [SOURCE.replace('gate "replay_cache_$unit" 600 lake env leanchecker "$module" || stop', ':'),
               SOURCE.replace('for pair in 0_0 0_112 96_73', 'for pair in 0_0 96_73')]:
    try:
        cached_accepted(run(broken, mode='cached-pair-pilot'))
    except AssertionError:
        pass
    else:
        raise AssertionError('broken cached harness accepted')
print('ok: CACHED HARNESS UNIT TESTS (fake commands): support/certificate replay before three cached pairs; no direct pair/row launches; failure propagation')
