#!/usr/bin/env bash
# Verify authenticated evidence using an isolated module view.
# Usage: verify.sh [--toolchain DIR] [--packages DIR] [--full] [--controls]
#                  [--work DIR] [--threads N]   (default: 2, maximum: 4)
set -euo pipefail
# The host shell, Python, system utilities and OS loader are trusted bootstrap code.
# Bash itself has already been loaded by the host. Sanitize before loading Python.
for loader_variable in ${!LD_@} ${!DYLD_@}; do unset "$loader_variable"; done
unset GLIBC_TUNABLES
# Caller PATH is discovery data only, never an authenticated runtime override.
exec /usr/bin/env -i PATH=/usr/bin:/bin HOME="${HOME:-/tmp}" python3 - "$0" "${PATH:-}" "$@" <<'PY'
import argparse, hashlib, json, os, re, shutil, stat, subprocess, sys, tempfile, time
from pathlib import Path, PurePosixPath
if sys.version_info < (3, 11):
    sys.exit('FAIL: python3 >= 3.11 is required')

def fail(message):
    raise ValueError(message)

def digest(path):
    with open(path, 'rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def relative(path):
    if (not isinstance(path, str) or not path or '\\' in path or
        any(c.isspace() for c in path) or path.startswith('/') or
        any(p in ('', '.', '..') for p in path.split('/')) or
        str(PurePosixPath(path)) != path):
        fail('non-normalized relative path: ' + repr(path))
    return path

def regular(path):
    if not stat.S_ISREG(path.lstat().st_mode):
        fail('not a regular file: ' + str(path))

def directory(path):
    if not stat.S_ISDIR(path.lstat().st_mode):
        fail('not a real directory: ' + str(path))

def checked(path, want):
    regular(path)
    if not re.fullmatch('[0-9a-f]{64}', want) or digest(path) != want:
        fail('sha256 mismatch: ' + str(path))

def hashlist(path, modules=False):
    regular(path)
    rows, names = {}, set()
    for line in path.read_text().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (\S+)' + (r'  (\S+)' if modules else ''), line)
        if not match:
            fail('malformed hash list: ' + str(path))
        h, rel = match[1], relative(match[2])
        if rel in rows:
            fail('duplicate hash-list path: ' + rel)
        module = match[3] if modules else None
        if modules:
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', module):
                fail('malformed module name')
            if module in names:
                fail('duplicate module: ' + module)
            names.add(module)
        rows[rel] = (h, module)
    if not rows:
        fail('empty hash list: ' + str(path))
    return rows

def tree(root, tops, expected):
    # Inspect roots and every entry without following symlinks. Empty extra directories fail too.
    allowed_dirs = set(tops)
    for rel in expected:
        relative(rel)
        allowed_dirs.update(str(p) for p in PurePosixPath(rel).parents if str(p) != '.')
    present = set()
    def visit(path, rel):
        directory(path)
        if rel not in allowed_dirs:
            fail('unexpected directory namespace: ' + rel)
        with os.scandir(path) as entries:
            for entry in entries:
                child = rel + '/' + entry.name
                mode = entry.stat(follow_symlinks=False).st_mode
                if stat.S_ISDIR(mode):
                    visit(Path(entry.path), child)
                elif stat.S_ISREG(mode):
                    present.add(child)
                else:
                    fail('symlink or non-regular entry: ' + child)
    for top in tops:
        visit(root / top, top)
    if present != set(expected):
        fail('file set differs: extra ' + repr(sorted(present-set(expected))[:5]) +
             ', missing ' + repr(sorted(set(expected)-present)[:5]))
    for rel, h in expected.items():
        checked(root / rel, h)

# No inherited Lean, Lake, loader, compiler or runtime environment overrides.
base_env = {'PATH': '/usr/bin:/bin', 'HOME': os.environ.get('HOME', '/tmp'),
            'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}

def run(args, cwd, env=None, output=None):
    result = subprocess.run([str(a) for a in args], cwd=cwd, env=env or base_env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if output:
        output.write_text(result.stdout)
    return result

def check_control(item, source, result):
    expected = str(source) + item['diagnostic'] if item['negative'] else ''
    errors = len(re.findall(r':\d+:\d+: error:', result.stdout))
    warnings = len(re.findall(r':\d+:\d+: warning:', result.stdout))
    if (result.returncode != int(item['negative']) or result.stdout != expected or
        errors != int(item['negative']) or warnings != 0):
        fail('unexpected control diagnostic for ' + item['target'] + ':\n' + result.stdout)


def main():
    start = time.monotonic()
    here = Path(sys.argv[1]).absolute().parent
    parser = argparse.ArgumentParser(prog='verify.sh', description='Fail-closed Lean evidence verification')
    parser.add_argument('--toolchain', type=Path)
    parser.add_argument('--packages', type=Path)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--controls', action='store_true')
    parser.add_argument('--work', type=Path, default=here / 'verify-work')
    parser.add_argument('--threads', type=int, default=2, help='Lean worker threads, default 2, maximum 4')
    args = parser.parse_args(sys.argv[3:])
    if not 1 <= args.threads <= 4:
        fail('--threads must be between 1 and 4')
    def step(text):
        print('\n== ' + text, flush=True)
    step('1/6 bundle integrity and pinned Lake project')
    regular(here / 'MANIFEST.json')
    m = json.loads((here / 'MANIFEST.json').read_text())
    expected_lists = {'bundle-files.sha256', 'package-modules.sha256',
                      'toolchain-modules.sha256', 'toolchain-runtime.sha256', 'module-sidecars.sha256', 'toolchain-setup.sha256'}
    if set(m['hash_lists']) != expected_lists:
        fail('unexpected hash-list inventory')
    hashes = {'hashes/' + n: h for n, h in m['hash_lists'].items()}
    hashes['hashes/control-inventory.json'] = m['control_inventory_sha256']
    tree(here, ('hashes',), hashes)
    bundle = hashlist(here / 'hashes/bundle-files.sha256')
    pkg = hashlist(here / 'hashes/package-modules.sha256', True)
    core = hashlist(here / 'hashes/toolchain-modules.sha256', True)
    runtime = hashlist(here / 'hashes/toolchain-runtime.sha256')
    sidecars = hashlist(here / 'hashes/module-sidecars.sha256')
    setup = hashlist(here / 'hashes/toolchain-setup.sha256')
    if any(p.split('/')[0] not in ('lib', 'src', 'controls') for p in bundle):
        fail('unexpected bundle hash namespace')
    tree(here, ('lib', 'src', 'controls'), {p: h for p, (h, _) in bundle.items()})
    tree(here, ('lean-project',), {
        'lean-project/lakefile.toml': m['packages']['lakefile_sha256'],
        'lean-project/lake-manifest.json': m['packages']['lake_manifest_sha256'],
        'lean-project/lean-toolchain': m['packages']['lean_toolchain_sha256']})
    inventory = json.loads((here / 'hashes/control-inventory.json').read_text())
    pairs = [('final-negative-win00', 'final-positive-twin')]
    pairs += [(f'negative-{kind}-h{h}', f'positive-{kind}-h{h}')
              for kind in ('table', 'win') for h in range(4)]
    expected_controls = {n + '.lean': (other, negative)
        for neg, pos in pairs for n, other, negative in ((neg,pos,True),(pos,neg,False))}
    if (len(inventory) != 18 or {x['file'] for x in inventory} != set(expected_controls) or
        {p.removeprefix('controls/') for p in bundle if p.startswith('controls/')} != set(expected_controls)):
        fail('unexpected control inventory')
    for item in inventory:
        name = item['file']
        if (item['pair'], item['negative']) != expected_controls[name]:
            fail('incorrect control pairing: ' + name)
        source = (here / 'controls' / name).read_text()
        namespaces = re.findall(r'^namespace (\S+)$', source, re.M)
        declarations = re.findall(r'^theorem (\w+)', source, re.M)
        if len(namespaces) != 1 or len(declarations) != 1 or item['target'] != namespaces[0]+'.'+declarations[0]:
            fail('control declaration mismatch: ' + name)
        lines = source.splitlines()
        if lines[item['line']-1] != '  decide +kernel' or item['column'] != 2:
            fail('control source location mismatch: ' + name)
        diagnostic = item['diagnostic']
        if item['negative']:
            prefix = f":{item['line']}:2: error: Tactic `decide` proved that the proposition\n"
            if (not diagnostic.startswith(prefix) or not diagnostic.endswith('\nis false\n') or
                diagnostic.count(': error:') != 1 or ': warning:' in diagnostic):
                fail('malformed expected negative diagnostic')
        elif diagnostic:
            fail('positive diagnostic must be empty')
    # Cross-check project module hashes with the manifest, not just a free-standing list.
    project = {}
    for item in m['modules']:
        module, rel = item['module'], relative(item['olean'])
        if rel != 'lib/' + module.replace('.', '/') + '.olean' or module in project:
            fail('invalid project module mapping')
        if bundle.get(rel) != (item['olean_sha256'], None):
            fail('project module differs from manifest: ' + module)
        project[module] = (here / rel, item['olean_sha256'])
    if {p for p in bundle if p.startswith('lib/') and p.endswith('.olean')} != {x['olean'] for x in m['modules']}:
        fail('unrecorded project object')
    print(f'{len(bundle)} authenticated files; strict file and directory inventory', flush=True)
    args.work.mkdir(parents=True, exist_ok=True)
    work = args.work.resolve()
    # A private fresh view prevents stale work files from entering resolution.
    view = Path(tempfile.mkdtemp(prefix='authenticated-', dir=work))
    (view / 'cwd').mkdir()
    (view / 'home').mkdir()
    env = dict(base_env, HOME=str(view / 'home'), LEAN_NUM_THREADS=str(args.threads))
    step('2/6 toolchain launchers, runtime libraries and core objects')
    tc = args.toolchain
    if tc is None:
        # Do not execute a candidate Lean to discover its prefix. Elan's stable
        # environment selector works without version-specific `which` flags.
        discovery_path = sys.argv[2]
        lean = shutil.which('lean', path=discovery_path)
        checker = shutil.which('leanchecker', path=discovery_path)
        # Elan's Lean shims are symlinks or hardlinks to the same executable.
        if lean and checker and not os.path.samefile(lean, checker):
            lean = Path(lean).resolve(strict=True)
            checker = Path(checker).resolve(strict=True)
            if lean.parent != checker.parent:
                fail('PATH lean and leanchecker must belong to the same toolchain')
            tc = lean.parent.parent
        else:
            elan = shutil.which('elan', path=discovery_path)
            if elan is None:
                for candidate in (Path(base_env['HOME']) / '.elan/bin/elan',
                                  Path(base_env['HOME']) / '.cargo/bin/elan'):
                    if candidate.is_file():
                        elan = str(candidate)
                        break
            if not elan:
                fail('no --toolchain, PATH lean/leanchecker, or elan installation')
            r = run([elan, 'toolchain', 'install', 'leanprover/lean4:v4.35.0'], view / 'cwd')
            if r.returncode:
                fail('elan install failed: ' + r.stdout)
            discovery_env = dict(base_env, ELAN_TOOLCHAIN='leanprover/lean4:v4.35.0')
            r = run([elan, 'which', 'lean'], view / 'cwd', discovery_env)
            if r.returncode:
                fail('elan which failed: ' + r.stdout)
            tc = Path(r.stdout.strip()).parent.parent
    tc = tc.resolve(strict=True)
    isolated_tc = view / 'toolchain'
    def snapshot(src, dst, want, allowed=None):
        # Cache symlinks are allowed only to regular canonical targets inside that package.
        if allowed is not None:
            src = src.resolve(strict=True)
            if not src.is_relative_to(allowed):
                fail('cache target escapes authenticated package: ' + str(src))
        regular(src)
        dst.parent.mkdir(parents=True, exist_ok=True)
        with open(src, 'rb') as f, open(dst, 'xb') as out:
            h = hashlib.sha256()
            while data := f.read(1024 * 1024):
                h.update(data)
                out.write(data)
        if h.hexdigest() != want:
            fail('sha256 mismatch: ' + str(src))
        dst.chmod(0o500 if str(dst).endswith(('/bin/lean','/bin/leanchecker','/bin/lake')) else 0o400)
    required = {'bin/lean', 'bin/leanchecker', 'bin/lake'} | {'lib/lean/'+n for n in (
        'libInit_shared.so','libleanshared.so','libleanshared_1.so','libleanshared_2.so','libLake_shared.so')}
    if not required <= set(runtime):
        fail('runtime inventory incomplete')
    for rel, (h, _) in runtime.items():
        if not (rel.startswith('lib/') or rel in required):
            fail('unexpected runtime namespace')
        if rel.startswith('bin/') and h != m['toolchain']['binary_sha256'][rel[4:]]:
            fail('runtime launcher metadata mismatch')
        snapshot(tc / rel, isolated_tc / rel, h)
    # Check only authenticated runtime bytes, never execute the discovery candidate.
    r = run([isolated_tc / 'bin/lean', '--version'], view / 'cwd', env)
    if r.returncode or not re.fullmatch(r'Lean \(version 4\.35\.0, [^\n]+\)\n?', r.stdout):
        fail('expected Lean 4.35.0; got: ' + r.stdout.strip())
    print(r.stdout.strip(), flush=True)
    # Never execute ldd on untrusted input. Runtime closure was discovered by the producer.
    for rel, (h, module) in core.items():
        if rel != module.replace('.', '/') + '.olean':
            fail('invalid core module mapping')
        snapshot(tc / 'lib/lean' / rel, isolated_tc / 'lib/lean' / rel, h)
    for rel, (h, _) in sidecars.items():
        if not rel.startswith('toolchain/'):
            continue
        path = rel.removeprefix('toolchain/')
        base = re.sub(r'\.(?:olean\.(?:private|server)|ir(?:\.sig)?)$', '.olean', path)
        if base not in core:
            fail('sidecar outside authenticated core closure: ' + rel)
        snapshot(tc / 'lib/lean' / path, isolated_tc / 'lib/lean' / path, h)
    env['PATH'] = str(isolated_tc / 'bin') + ':/usr/bin:/bin'
    print(f'{len(runtime)} runtime files and {len(core)} core modules authenticated', flush=True)
    step('3/6 authenticated package modules and isolated import view')
    packages = args.packages
    if packages is None:
        setup_tc = view / 'setup-toolchain'
        for rel, (h, _) in setup.items():
            snapshot(tc / rel, setup_tc / rel, h, tc)
            # Native cache compilation may invoke the authenticated compiler and linker.
            if os.access(tc / rel, os.X_OK):
                (setup_tc / rel).chmod(0o500)
        lake_project = view / 'lake-project'
        for name, key in (('lakefile.toml','lakefile_sha256'),
                          ('lake-manifest.json','lake_manifest_sha256'),
                          ('lean-toolchain','lean_toolchain_sha256')):
            snapshot(here / 'lean-project' / name, lake_project / name, m['packages'][key])
        # Lake itself and its runtime are authenticated before this first invocation.
        setup_env = dict(env, PATH=str(setup_tc / 'bin') + ':/usr/bin:/bin')
        r = run([setup_tc / 'bin/lake', '--no-cache', 'exe', 'cache', 'get'], lake_project, setup_env, work / 'lake.out')
        if r.returncode:
            fail('lake exe cache get failed; see ' + str(work / 'lake.out'))
        packages = lake_project / '.lake/packages'
    packages = packages.resolve(strict=True)
    roots = m['packages']['ordered_roots']
    derived = sorted({p.split('/')[0] for p in pkg})
    if roots != derived or not set(roots) <= set(m['packages']['revisions']):
        fail('package allowlist differs from recorded dependency closure')
    # Unrecorded cache roots are rejected. Recorded unused packages stay outside the view.
    with os.scandir(packages) as entries:
        for entry in entries:
            candidate = Path(entry.path) / '.lake/build/lib/lean'
            if entry.name not in m['packages']['revisions'] and os.path.lexists(candidate):
                fail('unexpected package build root: ' + entry.name)
    modules = dict(project)
    owners = {}
    def claim(module, owner):
        namespace = module.split('.')[0]
        if namespace in owners and owners[namespace] != owner:
            fail('namespace collision: ' + namespace)
        owners[namespace] = owner
    for module in project:
        claim(module, 'project')
    for rel, (h, module) in core.items():
        if module in modules:
            fail('core module collision: ' + module)
        claim(module, 'core')
        modules[module] = (isolated_tc / 'lib/lean' / rel, h)
    ordered = [view / 'project']
    for module, (src, h) in project.items():
        snapshot(src, ordered[0] / (module.replace('.', '/') + '.olean'), h)
    for name in roots:
        relative(name)
        package_root = (packages / name).resolve(strict=True)
        # Resolve individual cache links below the canonical package, then snapshot their bytes.
        ordered.append(view / 'packages' / name)
        for rel, (h, module) in pkg.items():
            owner, path = rel.split('/', 1)
            if owner != name:
                continue
            if path != module.replace('.', '/') + '.olean' or module in modules:
                fail('package module collision or mapping mismatch: ' + module)
            claim(module, name)
            src = packages / name / '.lake/build/lib/lean' / path
            snapshot(src, ordered[-1] / path, h, package_root)
            modules[module] = (ordered[-1] / path, h)
    for rel, (h, _) in sidecars.items():
        if rel.startswith('toolchain/'):
            continue
        if not rel.startswith('packages/'):
            fail('unexpected sidecar namespace: ' + rel)
        name, path = rel.removeprefix('packages/').split('/', 1)
        base = re.sub(r'\.(?:olean\.(?:private|server)|ir(?:\.sig)?)$', '.olean', path)
        if name + '/' + base not in pkg:
            fail('sidecar outside authenticated package closure: ' + rel)
        snapshot(packages / name / '.lake/build/lib/lean' / path,
                 view / 'packages' / name / path, h, (packages / name).resolve(strict=True))
    for item in inventory:
        rel = 'controls/' + item['file']
        snapshot(here / rel, view / rel, bundle[rel][0])
    env['LEAN_PATH'] = ':'.join(str(p) for p in ordered)
    # Implicit core lookup uses the isolated executable prefix. No unlisted objects exist there.
    print(f'{len(pkg)} package modules; ordered roots: {", ".join(roots)}; isolated allowlisted files only', flush=True)
    step('4/6 theorem proposition and transitive axioms')
    theorem, statement = m['theorem'], m['statement']
    source = view / 'cwd/statement.lean'
    source.write_text(f'import {m["module"]}\nset_option autoImplicit false\nexample : {statement} := {theorem}\n#print axioms {theorem}\n')
    r = run([isolated_tc / 'bin/lean', source], view / 'cwd', env, work / 'statement.out')
    if r.returncode:
        fail('statement elaboration failed:\n' + r.stdout)
    flat = re.sub(r'\s+', ' ', r.stdout).strip()
    match = re.fullmatch(rf"'{re.escape(theorem)}' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", flat)
    if not match:
        fail('unexpected compiler output:\n' + r.stdout)
    axioms = set(filter(None, re.split(r',\s*', match[1] or '')))
    if not axioms <= {'propext','Classical.choice','Quot.sound'}:
        fail('non-standard axioms: ' + repr(axioms))
    print('theorem term proves manifest proposition; axioms: ' + ', '.join(sorted(axioms)), flush=True)
    step('5/6 independent kernel replay (leanchecker)')
    targets = ['Transformer','TransformerCore','TransformerBridge'] if args.full else ['TransformerBridge.Kronecker','TransformerBridge.FinalRaw']
    r = run([isolated_tc / 'bin/leanchecker', *targets], view / 'cwd', env, work / 'replay.out')
    if r.returncode:
        fail('leanchecker rejected a module:\n' + r.stdout[-4000:])
    print('leanchecker replay passed: ' + ('all project modules' if args.full else '20 new modules'), flush=True)
    step('6/6 explicitly paired controls and exact diagnostics')
    if args.controls:
        for item in inventory:
            source = view / 'controls' / item['file']
            r = run([isolated_tc / 'bin/lean', source], view / 'cwd', env,
                    work / ('control-' + item['file'] + '.out'))
            check_control(item, source, r)
            print(item['file'] + ': ' + ('rejected as false' if item['negative'] else 'passes'), flush=True)
    else:
        print('skipped (run with --controls)', flush=True)
    print(f'\nPASS: {theorem}\n  {statement}\nchecked in {time.monotonic()-start:.1f} s', flush=True)
    shutil.rmtree(view)

try:
    main()
except (OSError, ValueError, KeyError, TypeError, IndexError, subprocess.SubprocessError) as error:
    sys.exit('FAIL: ' + str(error))
PY
