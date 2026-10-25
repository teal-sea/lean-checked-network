#!/usr/bin/env python3
"""Fast discovery/bootstrap regressions; integration needs the release bundle/cache.

The Python payload is embedded in the standalone shell verifier. Parse that payload
and exercise its discovery and version gates without executing an untrusted Lean.
"""
import ast
import os
from pathlib import Path
from types import SimpleNamespace
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'verify-release.sh'
PAYLOAD = SCRIPT.read_text().split("<<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
TREE = ast.parse(PAYLOAD)
MAIN = next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
# Load definitions and clean bootstrap defaults, but do not invoke main().
NS = {}
exec(compile(ast.Module(body=TREE.body[:-1], type_ignores=[]), str(SCRIPT), 'exec'), NS)
DISCOVERY = next(n for n in MAIN.body if isinstance(n, ast.If) and ast.unparse(n.test) == 'tc is None')
VERSION = next(n for n in MAIN.body if isinstance(n, ast.If) and 'expected Lean 4.35.0' in ast.unparse(n))

class DiscoveryTests(unittest.TestCase):
    def discover(self, which, run=None, samefile=False, tc=None):
        scope = dict(NS, tc=tc, here=Path('/bundle'), view=Path('/private/view'),
                     sys=SimpleNamespace(argv=['-', '/bundle/verify.sh', '/caller/bin']),
                     base_env={'PATH':'/usr/bin:/bin','HOME':'/private/home'})
        if run is not None:
            scope['run'] = run
        with patch.object(NS['shutil'], 'which', side_effect=lambda name, path=None: which.get(name)), \
             patch.object(NS['os'].path, 'samefile', return_value=samefile), \
             patch.object(Path, 'resolve', lambda p, **kw:p), \
             patch.object(Path, 'is_file', return_value=False):
            exec(compile(ast.Module(body=[DISCOVERY], type_ignores=[]), '<discovery>', 'exec'), scope)
        return scope['tc']

    def test_elan_uses_only_stable_which_and_bundle_pin(self):
        calls=[]
        def run(args, cwd, env=None):
            calls.append((args,cwd,env))
            return SimpleNamespace(returncode=0,stdout='/tc/bin/lean\n')
        self.assertEqual(self.discover({'elan':'/bin/elan'},run),Path('/tc'))
        self.assertEqual(calls,[(['/bin/elan','which','lean'],Path('/bundle'),None)])

    def test_no_elan_is_actionable(self):
        with self.assertRaisesRegex(ValueError,'install elan and run lean --version'):
            self.discover({})

    def test_uninstalled_toolchain_is_actionable(self):
        with self.assertRaisesRegex(ValueError,'run lean --version in this bundle'):
            self.discover({'elan':'/bin/elan'},lambda *a:SimpleNamespace(returncode=1,stdout='not installed'))

    def test_explicit_toolchain_bypasses_discovery(self):
        self.assertEqual(self.discover({},tc=Path('/explicit')),Path('/explicit'))

class VersionTests(unittest.TestCase):
    def check(self,text,rc=0):
        scope=dict(NS,r=SimpleNamespace(returncode=rc,stdout=text))
        exec(compile(ast.Module(body=[VERSION],type_ignores=[]),'<version>','exec'),scope)

    def test_exact_pinned_version(self):
        self.check('Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit abc, Release)\n')

    def test_wrong_prerelease_and_malformed_versions_fail(self):
        for version in ('4.34.0','4.35.0-rc2','4.35.01','4.35.0-dev'):
            with self.subTest(version=version),self.assertRaisesRegex(ValueError,'expected Lean 4.35.0'):
                self.check(f'Lean (version {version}, linux, Release)\n')
        for text in ('','Lean (version 4.35.0, linux)\nextra\n'):
            with self.assertRaises(ValueError):self.check(text)

    def test_version_nonzero_rejects(self):
        with self.assertRaises(ValueError):
            self.check('Lean (version 4.35.0, linux)\n',1)

    def test_runtime_hashes_precede_version_execution(self):
        text=ast.unparse(MAIN)
        self.assertLess(text.index('snapshot(tc / rel, isolated_tc / rel, h)'), text.index("[isolated_tc / 'bin/lean', '--version']"))

class BootstrapTests(unittest.TestCase):
    def test_caller_python_never_runs_and_argument_parsing_survives(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parent) as temp:
            p=Path(temp)/'python3'; p.write_text('#!/bin/sh\nexit 89\n'); p.chmod(0o700)
            env=dict(os.environ, PATH=temp+':/usr/bin:/bin', PYTHONPATH='/untrusted', LEAN_PATH='/untrusted')
            done=subprocess.run(['/bin/bash',str(SCRIPT),'--help'],env=env,capture_output=True,text=True)
            self.assertEqual(done.returncode,0,done.stderr)
            self.assertIn('--toolchain',done.stdout)

if __name__=='__main__':
    unittest.main()
