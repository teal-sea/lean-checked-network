"""A verifiers v1 taskset: prove in Lean 4 that a frozen integer network adds mod p.

The model gets the network's definition (Network.lean), the weights (Weights.lean), and the
name and statement of the theorem it must prove. It answers with one Lean file. The reward is
1.0 when Lean's kernel accepts that file, `leanchecker` replays it, the theorem has the required
statement, and it uses only the standard axioms; otherwise 0.0. Nothing about the reward is
judged by a model.
"""

from __future__ import annotations

import asyncio
import json
from pathlib import Path

import verifiers.v1 as vf

from lean_mod_add_proof.grader import STAGES, GradeResult, grade

HERE = Path(__file__).resolve().parent
TASKS_DIR = HERE / "tasks"
NETWORK_LEAN = (HERE / "Network.lean").read_text()
INFO_KEY = "lean_grader"


def build_prompt(p: int, H: int, theorem_name: str, weights_lean: str) -> str:
    short = theorem_name.rsplit(".", 1)[1]
    return f"""You are given a small neural network that was trained to add two numbers modulo {p} and then frozen to whole-number weights. Prove in Lean 4 that it is right on every input pair.

The network: inputs a and b (each in 0..{p - 1}) select row a of E1 and row b of E2; the rows are added entry by entry, every entry is squared ({H} neurons), and a read-out table W2 gives each candidate answer c the score `dot (row c of W2) hidden`. The answer is the index of the highest score, the first one on a tie. This is defined in Lean below, in `LeanCheckedNetwork/Network.lean`, exactly as it will be compiled:

```lean
{NETWORK_LEAN.rstrip()}
```

The frozen weights, in `LeanCheckedNetwork/Weights.lean`, exactly as they will be compiled:

```lean
{weights_lean.rstrip()}
```

Your task: write a Lean 4 file that proves

```lean
theorem LeanCheckedNetwork.Net.{short} : ∀ a, a < {p} → ∀ b, b < {p} → LeanCheckedNetwork.Net.answer a b = (a + b) % {p}
```

The theorem must have exactly this name and this statement (it is the statement `LeanCheckedNetwork.Net.Spec` from Weights.lean; proving `{short} : Spec` is also accepted). You may add any helper definitions and lemmas you need in the same file.

How your file is checked:
- It is placed as `LeanCheckedNetwork/Submission.lean` in a fresh Lake package next to the two files above, toolchain `leanprover/lean4:v4.35.0-rc2`, no Mathlib, no other dependencies. Only `import LeanCheckedNetwork.Network` and `import LeanCheckedNetwork.Weights` are allowed.
- `lake build LeanCheckedNetwork.Submission` must succeed within the time limit, then `lake env leanchecker LeanCheckedNetwork.Submission` must accept the module (it re-checks every declaration with the kernel), then a file that states the required theorem and closes it with your theorem must elaborate, then `#print axioms` on your theorem must show nothing outside propext, Classical.choice and Quot.sound.
- Files containing any of these are rejected before Lean runs: sorry, admit, native_decide, decide +native, ofReduceBool, axiom, opaque, implemented_by, extern, unsafe, partial, set_option debug.*, macro, macro_rules, elab, elab_rules, syntax, notation, infix, prefix, postfix, initialize. `set_option maxRecDepth` and `set_option maxHeartbeats` are fine.
- The reward is 1.0 if everything passes and 0.0 otherwise. There is no partial credit and no human or model judgement.

Reply with exactly one ```lean code block containing the whole file. Text outside the block is ignored. Remember the kernel spends about the same time on every small arithmetic step, so larger p and more neurons may need a smarter route than checking every pair directly."""


class LeanProofData(vf.TaskData):
    task_id: str
    p: int
    H: int
    seed: int
    train_fraction: float
    """The fraction of the p*p pairs the network was trained on (1.0 = it saw every pair)."""
    split: str
    theorem_name: str
    weights_lean: str
    network_lean: str


class LeanProofTaskConfig(vf.TaskConfig):
    timeout_s: float = 300.0
    """Wall-clock budget for lake build + leanchecker + the statement check, in seconds."""
    axioms_mode: str = "subset"
    """"subset": any axiom set inside {propext, Classical.choice, Quot.sound}; "exact": all three."""
    work_root: str | None = None
    """Directory for the throwaway Lake packages (default: the system temp dir)."""
    keep_packages: bool = False
    """Keep each graded package on disk (for debugging)."""


class LeanProofTask(vf.Task[LeanProofData, vf.State, LeanProofTaskConfig]):
    async def _graded(self, trace: vf.Trace) -> GradeResult:
        cached = trace.info.get(INFO_KEY)
        if cached is not None:
            return GradeResult(**cached)
        result = await asyncio.to_thread(
            grade,
            trace.last_reply,
            network_lean=self.data.network_lean,
            weights_lean=self.data.weights_lean,
            theorem_name=self.data.theorem_name,
            timeout_s=self.config.timeout_s,
            axioms_mode=self.config.axioms_mode,
            work_root=self.config.work_root,
            keep=self.config.keep_packages,
        )
        # Why it passed or failed, with the command outputs: serialized with the trace.
        trace.info[INFO_KEY] = result.as_dict()
        return result

    @vf.metric(priority=10)
    async def lean_stages(self, trace: vf.Trace) -> dict[str, float]:
        """Which stage the submission reached (metrics run before rewards, so this grades once)."""
        r = await self._graded(trace)
        i = r.stage_index
        return {
            "guard_passed": float(i > STAGES.index("guard")),
            "build_passed": float(i > STAGES.index("build")),
            "leanchecker_passed": float(i > STAGES.index("leanchecker")),
            "statement_passed": float(i > STAGES.index("check")),
            "axioms_passed": float(i > STAGES.index("axioms")),
            "grader_seconds": float(r.timings.get("total_s", 0.0)),
        }

    @vf.reward
    async def kernel_accepts(self, trace: vf.Trace) -> float:
        """1.0 only when the Lean kernel accepts the required theorem under the rules."""
        return (await self._graded(trace)).reward


class LeanProofConfig(vf.TasksetConfig):
    split: str = "train"
    """"train", "eval" or "all"."""
    max_p: int | None = None
    """Keep only tasks with p <= max_p."""
    tasks_dir: str | None = None
    """Override the bundled tasks directory (a tasks.jsonl plus one folder per task)."""
    task: LeanProofTaskConfig = LeanProofTaskConfig()


class LeanProofTaskset(vf.Taskset[LeanProofTask, LeanProofConfig]):
    def load(self) -> list[LeanProofTask]:
        root = Path(self.config.tasks_dir) if self.config.tasks_dir else TASKS_DIR
        rows = [json.loads(line) for line in (root / "tasks.jsonl").read_text().splitlines() if line.strip()]
        tasks = []
        for row in rows:
            if self.config.split != "all" and row["split"] != self.config.split:
                continue
            if self.config.max_p is not None and row["p"] > self.config.max_p:
                continue
            weights = (root / row["task_id"] / "Weights.lean").read_text()
            data = LeanProofData(
                id=row["task_id"],
                name=row["task_id"],
                task_id=row["task_id"],
                p=row["p"], H=row["H"], seed=row["seed"],
                train_fraction=row["train_fraction"],
                split=row["split"],
                theorem_name=row["theorem_name"],
                weights_lean=weights,
                network_lean=NETWORK_LEAN,
                prompt=build_prompt(row["p"], row["H"], row["theorem_name"], weights),
            )
            tasks.append(LeanProofTask(data, self.config.task))
        return tasks
