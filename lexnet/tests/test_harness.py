"""Small tests for the generator entrypoint and the fail-closed checkers (stdlib unittest, no Lean needed).
Run from lexnet/:  python3 -m unittest discover -s tests"""
import hashlib, os, pathlib, re, shutil, stat, subprocess, sys, tempfile, unittest
sys.dont_write_bytecode = True

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import check_axioms, check_control, generate

REAL_AX = (ROOT / "verification/packaging/build/Axioms.log").read_text()
REAL_CTL = (ROOT / "verification/packaging/controls-mutant-Bwd.log").read_text()
BWD_ERR = [l for l in REAL_CTL.splitlines() if ": error:" in l][0]

class Axioms(unittest.TestCase):
    """Mutations of the real captured Axioms.log of the packaging run."""
    def rej(self, text):
        ok, msg = check_axioms.check(text)
        self.assertFalse(ok, msg)
    def test_accepts_real_log(self):
        self.assertTrue(check_axioms.check(REAL_AX)[0])
    def test_rejects_only_main_line(self):
        self.rej(REAL_AX.splitlines()[0] + "\n")
    def test_rejects_missing_helper(self):
        self.rej("\n".join(l for l in REAL_AX.splitlines() if "bwd_all" not in l) + "\n")
    def test_rejects_duplicate_garbage_and_error(self):
        self.rej(REAL_AX + REAL_AX.splitlines()[1] + "\nerror: boom\ngarbage\n")
    def test_rejects_unexpected_name(self):
        self.rej(REAL_AX + "'Evil.thm' depends on axioms: [propext]\n")
    def test_rejects_duplicate_main_with_extra_axiom(self):
        self.rej("'lexnet_correct' depends on axioms: [propext, Classical.choice, Quot.sound, Foo]\n" + REAL_AX)
    def test_rejects_sorry_warning(self):
        self.rej(REAL_AX + "lean/Full.lean:1:1: warning: declaration uses 'sorry'\n")
    def test_rejects_extra_axiom_in_helper(self):
        self.rej(REAL_AX.replace("'Lexnet.bwd_all' depends on axioms: [propext]", "'Lexnet.bwd_all' depends on axioms: [propext, Lean.ofReduceBool]"))
    def test_rejects_weaker_main_theorem(self):
        self.rej(REAL_AX.replace("'lexnet_correct' depends on axioms: [propext, Classical.choice, Quot.sound]", "'lexnet_correct' depends on axioms: [propext]"))
    def test_cli_exit_codes(self):
        with tempfile.TemporaryDirectory() as t:
            good = pathlib.Path(t) / "g.log"; good.write_text(REAL_AX)
            bad = pathlib.Path(t) / "b.log"; bad.write_text(REAL_AX + "garbage\n")
            self.assertEqual(subprocess.run([sys.executable, "-B", str(ROOT / "check_axioms.py"), str(good)], capture_output=True).returncode, 0)
            self.assertEqual(subprocess.run([sys.executable, "-B", str(ROOT / "check_axioms.py"), str(bad)], capture_output=True).returncode, 1)

class Control(unittest.TestCase):
    """Mutations of the real captured mutant-Bwd log."""
    def rej(self, pre, exit_, log):
        ok, msg = check_control.check(pre, exit_, log)
        self.assertFalse(ok, msg)
    def test_accepts_real_log_with_its_linter_warnings(self):
        self.assertIn("warning:", REAL_CTL)
        self.assertTrue(check_control.check([0, 0], 1, REAL_CTL)[0])
    def test_rejects_added_error(self):
        self.rej([0, 0], 1, REAL_CTL + "lean/Bwd.lean:5:1: error: unknown identifier 'x'\n")
    def test_rejects_added_error_in_other_file(self):
        self.rej([0, 0], 1, "lean/Other.lean:1:1: error: boom\n" + REAL_CTL)
    def test_rejects_phrase_only_spoof(self):
        self.rej([0, 0], 1, "Tactic `decide` proved that the proposition\nis false\n")
    def test_rejects_wrong_location(self):
        self.rej([0, 0], 1, REAL_CTL.replace("Bwd.lean:57:6", "Bwd.lean:58:6"))
    def test_rejects_wrong_file(self):
        self.rej([0, 0], 1, REAL_CTL.replace("lean/Bwd.lean:57:6", "lean/Hash.lean:57:6"))
    def test_rejects_other_error_text_at_location(self):
        self.rej([0, 0], 1, REAL_CTL.replace("Tactic `decide` proved that the proposition", "unknown identifier"))
    def test_rejects_missing_or_extra_prerequisites(self):
        self.rej([0], 1, REAL_CTL)
        self.rej([0, 0, 0], 1, REAL_CTL)
        self.rej([], 1, REAL_CTL)
    def test_rejects_failed_prerequisite(self):
        self.rej([0, 1], 1, REAL_CTL)
    def test_rejects_wrong_target_exit(self):
        self.rej([0, 0], 0, REAL_CTL)
        self.rej([0, 0], 124, REAL_CTL)
    def test_rejects_leading_garbage(self):
        self.rej([0, 0], 1, "panic\n" + REAL_CTL)
    def test_rejects_error_without_decide_body(self):
        self.rej([0, 0], 1, BWD_ERR + "\n  nothing\n")

STUB_LEAN = """#!/usr/bin/env bash
# TEST STUB, not Lean.  Records invocations; fails the module named in STUB_FAIL.
case "$1" in
  --version) echo "Lean (version 4.35.0-rc2, stub)"; exit 0;;
  --print-prefix) echo "$STUB_PREFIX"; exit 0;;
esac
mod=$(basename "${@: -1}" .lean)
[ "$mod" = "${STUB_FAIL:-}" ] && { echo "stub failure in $mod"; exit 1; }
[ "$mod" = "Axioms" ] && cat "$STUB_AXIOMS"
: > "${@: -3:1}"
exit 0
"""

def tree_hash(root):
    h = hashlib.sha256()
    for p in sorted(pathlib.Path(root).rglob("*")):
        if p.is_file() and not p.is_symlink():
            h.update(str(p.relative_to(root)).encode()); h.update(p.read_bytes())
    return h.hexdigest()

class WorkdirHarness(unittest.TestCase):
    """SYNTHETIC harness tests: `lean` and `leanchecker` are stubs. They test verify.sh orchestration and
    directory safety only; they are not proof evidence."""
    def setUp(self):
        self.t = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.t, True)
        self.pkg = self.t / "pkg"
        shutil.copytree(ROOT, self.pkg, ignore=shutil.ignore_patterns("verification", "tests", "__pycache__"))
        (self.pkg / "SENTINEL.txt").write_text("keep me")
        prefix = self.t / "prefix"; (prefix / "bin").mkdir(parents=True)
        for name, body in (("leanchecker", "#!/usr/bin/env bash\necho stub replay\nexit $(cat \"$(dirname \"$0\")/exitcode\" 2>/dev/null || echo 0)\n"),):
            f = prefix / "bin" / name; f.write_text(body); f.chmod(0o755)
        bindir = self.t / "bin"; bindir.mkdir()
        f = bindir / "lean"; f.write_text(STUB_LEAN); f.chmod(0o755)
        axl = self.t / "axioms.log"; axl.write_text(REAL_AX)
        self.env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", STUB_PREFIX=str(prefix), STUB_AXIOMS=str(axl))
        self.before = tree_hash(self.pkg)
    def run_verify(self, work=None, cwd=None, **extra):
        env = dict(self.env, **extra)
        if work is not None: env["LEXNET_WORK"] = work
        return subprocess.run(["bash", str(self.pkg / "verify.sh")], capture_output=True, text=True, env=env, cwd=cwd or self.t)
    def test_package_dir_as_work_is_refused_and_nothing_lost(self):
        r = self.run_verify(str(self.pkg / "."))
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertEqual(tree_hash(self.pkg), self.before)
        self.assertTrue((self.pkg / "lean" / "Full.lean").is_file())
    def test_subdirectory_of_package_is_refused(self):
        r = self.run_verify(str(self.pkg / "lean"))
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertEqual(tree_hash(self.pkg), self.before)
    def test_symlink_to_package_is_refused(self):
        (self.t / "link").symlink_to(self.pkg)
        r = self.run_verify(str(self.t / "link"))
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertEqual(tree_hash(self.pkg), self.before)
    def test_relative_parent_and_existing_files_survive(self):
        parent = self.t / "elsewhere"; parent.mkdir(); (parent / "sentinel").write_text("x")
        (parent / "lean").mkdir(); (parent / "lean" / "Reference.lean").write_text("mine")
        r = self.run_verify("elsewhere", cwd=self.t)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("VERIFY PASS", r.stdout)
        self.assertEqual((parent / "sentinel").read_text(), "x")
        self.assertEqual((parent / "lean" / "Reference.lean").read_text(), "mine")
        runs = list(parent.glob("run.*")); self.assertEqual(len(runs), 1)
        self.assertEqual(tree_hash(self.pkg), self.before)
    def test_two_runs_use_distinct_directories(self):
        parent = self.t / "w"
        for _ in range(2): self.assertEqual(self.run_verify(str(parent)).returncode, 0)
        self.assertEqual(len(list(parent.glob("run.*"))), 2)
    def test_module_failure_stops_and_keeps_sources(self):
        r = self.run_verify(str(self.t / "w"), STUB_FAIL="Hash")
        self.assertEqual(r.returncode, 1)
        self.assertIn("FAIL: Hash", r.stderr)
        self.assertNotIn("Flags exit", r.stdout)
        self.assertEqual(tree_hash(self.pkg), self.before)
    def test_replay_failure_fails(self):
        (self.t / "prefix" / "bin" / "exitcode").write_text("3")
        r = self.run_verify(str(self.t / "w"))
        self.assertEqual(r.returncode, 1)
        self.assertIn("FAIL: leanchecker", r.stderr)
    def test_bad_axiom_log_fails(self):
        (self.t / "axioms.log").write_text(REAL_AX + "garbage\n")
        r = self.run_verify(str(self.t / "w"))
        self.assertNotEqual(r.returncode, 0)
        self.assertNotIn("VERIFY PASS", r.stdout)
    def test_missing_lean_gives_actionable_error_before_any_directory(self):
        env = dict(os.environ, PATH="/usr/bin:/bin")
        work = self.t / "never"
        env["LEXNET_WORK"] = str(work)
        r = subprocess.run(["bash", str(self.pkg / "verify.sh")], capture_output=True, text=True, env=env, cwd=self.t)
        self.assertEqual(r.returncode, 2)
        self.assertIn("'lean' not found on PATH", r.stderr)
        self.assertFalse(work.exists())
    def test_no_bytecode_written_into_package(self):
        self.assertEqual(self.run_verify(str(self.t / "w")).returncode, 0)
        self.assertEqual([], list(self.pkg.rglob("__pycache__")))
        self.assertEqual(tree_hash(self.pkg), self.before)
    def test_controls_refuse_package_dir(self):
        env = dict(self.env, LEXNET_WORK=str(self.pkg))
        r = subprocess.run(["bash", str(self.pkg / "controls.sh")], capture_output=True, text=True, env=env, cwd=self.t)
        self.assertEqual(r.returncode, 2)
        self.assertEqual(tree_hash(self.pkg), self.before)

class Generators(unittest.TestCase):
    def test_check_passes_on_package(self):
        self.assertEqual(generate.main(["--check"]), 0)
    def test_check_fails_on_changed_lean_byte(self):
        with tempfile.TemporaryDirectory() as t:
            dst = pathlib.Path(t) / "pkg"
            shutil.copytree(ROOT, dst, ignore=shutil.ignore_patterns("verification", "tests", "__pycache__", "*.olean"))
            f = dst / "lean" / "Hash.lean"
            f.write_bytes(f.read_bytes() + b"\n")
            r = subprocess.run([sys.executable, str(dst / "generate.py"), "--check"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)
            self.assertIn("MISMATCH lean/Hash.lean", r.stdout)
    def test_check_fails_on_changed_weight_byte(self):
        with tempfile.TemporaryDirectory() as t:
            dst = pathlib.Path(t) / "pkg"
            shutil.copytree(ROOT, dst, ignore=shutil.ignore_patterns("verification", "tests", "__pycache__", "*.olean"))
            w = dst / "upstream/lexnet/lexnet_weights.bin"
            b = bytearray(w.read_bytes()); b[-1] ^= 1; w.write_bytes(bytes(b))
            r = subprocess.run([sys.executable, str(dst / "generate.py"), "--check"], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)

if __name__ == "__main__":
    unittest.main()
