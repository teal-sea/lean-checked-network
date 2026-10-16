"""Grade one Lean submission with the Lean kernel. No verifiers dependency, so it can be tested on its own.

The pipeline for one submission:

  1. take the Lean source out of the reply (last ```lean fenced block, else the whole reply)
  2. text guard: forbidden tokens and imports (a first filter; the kernel is the real check)
  3. fresh lake package: lean-toolchain, lakefile.toml, LeanCheckedNetwork/{Network,Weights,Submission}.lean
  4. lake build LeanCheckedNetwork.Submission           (time limited)
  5. lake env leanchecker LeanCheckedNetwork.Submission  (replays the module through the kernel)
  6. lake env lean Check.lean                            (statement check + #print axioms)

Reward 1.0 only when every step passes; otherwise 0.0 with the stage and the reason recorded.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import signal
import subprocess
import tempfile
import time
import uuid
from dataclasses import dataclass, field, asdict
from pathlib import Path

TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
NAMESPACE = "LeanCheckedNetwork.Net"
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Tokens that fail a submission before Lean is run. Matched as whole words anywhere in the
# file, comments included. `set_option` itself is allowed (maxRecDepth, maxHeartbeats are
# legitimate); the debug options are not.
FORBIDDEN_TOKENS = (
    "sorry", "admit", "native_decide", "ofReduceBool", "axiom", "opaque", "implemented_by",
    "extern", "unsafe", "partial", "skipKernelTC", "macro_rules", "macro", "elab", "elab_rules",
    "syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "initialize",
    "builtin_initialize", "Lean.Elab", "Lean.Meta", "Lean.Environment", "addDecl",
)
FORBIDDEN_PATTERNS = (
    r"\+\s*native",          # decide +native
    r"debug\.",              # set_option debug.*
    r"trace\.profiler",      # harmless, but no reason for it; keep the surface small
)
ALLOWED_IMPORTS = ("LeanCheckedNetwork.Network", "LeanCheckedNetwork.Weights")

STAGES = ("extract", "guard", "package", "build", "leanchecker", "check", "axioms", "ok")


@dataclass
class GradeResult:
    reward: float
    stage: str                      # the stage at which grading stopped ("ok" when it passed)
    reason: str                     # one line, why it stopped there
    timings: dict = field(default_factory=dict)
    outputs: dict = field(default_factory=dict)   # tail of each command's output
    axioms: list = field(default_factory=list)
    source_sha256: str = ""
    package_dir: str | None = None  # kept only when keep=True

    def as_dict(self) -> dict:
        return asdict(self)

    @property
    def stage_index(self) -> int:
        return STAGES.index(self.stage)


def extract_lean(reply: str) -> str:
    """The last ```lean fenced block, else the last ``` block, else the whole reply."""
    blocks = re.findall(r"```lean4?\s*\n(.*?)```", reply, re.S)
    if not blocks:
        blocks = re.findall(r"```\s*\n(.*?)```", reply, re.S)
    return (blocks[-1] if blocks else reply).strip() + "\n"


def text_guard(source: str) -> str | None:
    """A one-line reason when the source is refused before Lean runs, else None."""
    for tok in FORBIDDEN_TOKENS:
        if re.search(r"(?<![A-Za-z0-9_.'])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", source):
            return f"forbidden token: {tok}"
    for pat in FORBIDDEN_PATTERNS:
        if re.search(pat, source):
            return f"forbidden pattern: {pat}"
    for m in re.finditer(r"^\s*import\s+(.*)$", source, re.M):
        for mod in m.group(1).split():
            if mod not in ALLOWED_IMPORTS:
                return f"import not allowed: {mod}"
    return None


def lakefile_toml() -> str:
    return (
        'name = "lean-mod-add-proof"\n'
        'defaultTargets = ["LeanCheckedNetwork"]\n\n'
        '[[lean_lib]]\n'
        'name = "LeanCheckedNetwork"\n'
    )


def check_lean(theorem_name: str) -> str:
    # `Spec` is elaborated inside Weights.lean, before any submitted syntax exists, so a
    # submission cannot change what the required statement means. The term-mode proof below
    # type-checks only if the submitted theorem's type is (definitionally) that statement.
    return (
        "import LeanCheckedNetwork.Submission\n\n"
        f"theorem LeanModAddProofCheck.statement_matches : {NAMESPACE}.Spec := {theorem_name}\n\n"
        f"#print axioms {theorem_name}\n"
    )


def _run(cmd: list[str], cwd: Path, timeout: float, env: dict) -> tuple[int | None, str, float]:
    """Run cmd in its own process group; kill the group on timeout. Returns (rc, output, seconds)."""
    t0 = time.monotonic()
    proc = subprocess.Popen(
        cmd, cwd=str(cwd), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, start_new_session=True,
    )
    try:
        out, _ = proc.communicate(timeout=timeout)
        rc: int | None = proc.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, _ = proc.communicate()
        rc = None
    return rc, out or "", time.monotonic() - t0


def _tail(s: str, n: int = 4000) -> str:
    return s if len(s) <= n else "...[truncated]...\n" + s[-n:]


def parse_axioms(output: str, theorem_name: str) -> list[str] | None:
    """The axiom list printed by `#print axioms theorem_name`, [] when it depends on none,
    None when the line is missing."""
    name = re.escape(theorem_name)
    m = re.search(rf"'{name}' depends on axioms: \[([^\]]*)\]", output)
    if m:
        return [a.strip() for a in m.group(1).split(",") if a.strip()]
    if re.search(rf"'{name}' does not depend on any axioms", output):
        return []
    return None


def lean_env(lean_threads: int = 1) -> dict:
    env = dict(os.environ)
    elan = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan}:{env.get('PATH', '')}"
    env["LEAN_NUM_THREADS"] = str(lean_threads)
    return env


def grade(reply: str, **kw) -> GradeResult:
    """Grade `reply` (the model's whole message) against one task; see `_grade` for the options.
    Always records the total wall time, whichever stage grading stopped at."""
    t0 = time.monotonic()
    result = _grade(reply, **kw)
    result.timings["total_s"] = round(time.monotonic() - t0, 2)
    return result


def _grade(
    reply: str,
    *,
    network_lean: str,
    weights_lean: str,
    theorem_name: str,
    timeout_s: float = 300.0,
    axioms_mode: str = "subset",
    work_root: str | None = None,
    keep: bool = False,
    skip_text_guard: bool = False,
    lean_threads: int = 1,
) -> GradeResult:
    """The grading pipeline (call `grade`).

    axioms_mode: "subset" accepts any axiom set inside {propext, Classical.choice, Quot.sound}
    (a proof by `decide` may use none of them); "exact" demands all three and nothing else.
    skip_text_guard: for tests only; lets a forbidden file through to Lean to show that the
    kernel-level checks catch it on their own.
    lean_threads: LEAN_NUM_THREADS for the build (1 keeps concurrent rollouts predictable).
    """
    source = extract_lean(reply)
    sha = hashlib.sha256(source.encode()).hexdigest()
    res = GradeResult(reward=0.0, stage="extract", reason="", source_sha256=sha)
    if not source.strip():
        res.reason = "empty submission"
        return res

    res.stage = "guard"
    why = None if skip_text_guard else text_guard(source)
    if why:
        res.reason = why
        return res

    res.stage = "package"
    root = Path(work_root or os.environ.get("LEAN_GRADER_WORK_ROOT") or tempfile.gettempdir())
    root.mkdir(parents=True, exist_ok=True)
    pkg = root / f"pkg-{uuid.uuid4().hex[:12]}"
    lib = pkg / "LeanCheckedNetwork"
    lib.mkdir(parents=True)
    (pkg / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (pkg / "lakefile.toml").write_text(lakefile_toml())
    (pkg / "LeanCheckedNetwork.lean").write_text(
        "import LeanCheckedNetwork.Network\nimport LeanCheckedNetwork.Weights\n")
    (lib / "Network.lean").write_text(network_lean)
    (lib / "Weights.lean").write_text(weights_lean)
    (lib / "Submission.lean").write_text(source)
    (pkg / "Check.lean").write_text(check_lean(theorem_name))
    env = lean_env(lean_threads)
    deadline = time.monotonic() + timeout_s

    def remaining() -> float:
        return max(1.0, deadline - time.monotonic())

    try:
        res.stage = "build"
        rc, out, dt = _run(["lake", "build", "LeanCheckedNetwork.Submission"], pkg, remaining(), env)
        res.timings["build_s"] = round(dt, 2)
        res.outputs["build"] = _tail(out)
        if rc is None:
            res.reason = f"lake build timed out after {timeout_s:.0f} s"
            return res
        if rc != 0:
            res.reason = "lake build failed"
            return res

        res.stage = "leanchecker"
        rc, out, dt = _run(["lake", "env", "leanchecker", "LeanCheckedNetwork.Submission"], pkg, remaining(), env)
        res.timings["leanchecker_s"] = round(dt, 2)
        res.outputs["leanchecker"] = _tail(out)
        if rc is None:
            res.reason = "leanchecker timed out"
            return res
        if rc != 0:
            res.reason = "leanchecker rejected the module"
            return res

        res.stage = "check"
        rc, out, dt = _run(["lake", "env", "lean", "Check.lean"], pkg, remaining(), env)
        res.timings["check_s"] = round(dt, 2)
        res.outputs["check"] = _tail(out)
        if rc is None:
            res.reason = "statement check timed out"
            return res
        if rc != 0:
            res.reason = f"the theorem {theorem_name} is missing or its statement is not the required one"
            return res

        res.stage = "axioms"
        axioms = parse_axioms(out, theorem_name)
        if axioms is None:
            res.reason = "#print axioms produced no parseable line"
            return res
        res.axioms = axioms
        extra = sorted(set(axioms) - set(STANDARD_AXIOMS))
        if extra:
            res.reason = f"non-standard axioms: {extra}"
            return res
        if axioms_mode == "exact" and set(axioms) != set(STANDARD_AXIOMS):
            res.reason = f"axioms {axioms} are not exactly {list(STANDARD_AXIOMS)}"
            return res

        res.stage = "ok"
        res.reason = "kernel accepted; leanchecker replayed; statement matches; axioms standard"
        res.reward = 1.0
        return res
    finally:
        if keep:
            res.package_dir = str(pkg)
        else:
            shutil.rmtree(pkg, ignore_errors=True)
