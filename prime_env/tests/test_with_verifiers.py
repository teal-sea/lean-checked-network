"""Score submissions through the real verifiers v1 objects: build the taskset, pick a task,
make a Trace whose reply is the submission, call Task.score(trace), print rewards/metrics/info.
Usage: test_with_verifiers.py TASK_ID REPLY_FILE [REPLY_FILE ...]"""
import asyncio
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean_mod_add_proof"))
import verifiers.v1 as vf
from lean_mod_add_proof.taskset import LeanProofConfig, LeanProofTaskset, LeanProofTaskConfig


async def main(task_id: str, replies: list[str]) -> None:
    cfg = LeanProofConfig(split="all", task=LeanProofTaskConfig(timeout_s=600, work_root=str(Path(__file__).resolve().parent / "work")))
    taskset = LeanProofTaskset(cfg)
    tasks = {t.data.task_id: t for t in taskset}
    print(f"taskset loaded: {len(tasks)} tasks; config {cfg.model_dump()}")
    task = tasks[task_id]
    print(f"task {task_id}: p={task.data.p} H={task.data.H} theorem {task.data.theorem_name}; prompt {len(task.data.prompt)} chars")
    for reply_file in replies:
        reply = Path(reply_file).read_text()
        trace = vf.Trace(
            task=vf.TraceTask(type=type(task).__name__, data=task.data, key=task.key, hash=task.hash),
            agent=vf.AgentInfo(config=vf.AgentConfig()),
            root_reply=reply,
        )
        await task.score(trace)
        g = trace.info["lean_grader"]
        print(json.dumps({
            "reply": Path(reply_file).name,
            "rewards": {k: (v.model_dump() if v is not None else None) for k, v in trace.rewards.items()},
            "metrics": trace.metrics,
            "grader": {k: g[k] for k in ("stage", "reason", "axioms", "timings")},
        }, indent=1))


if __name__ == "__main__":
    asyncio.run(main(sys.argv[1], sys.argv[2:]))
