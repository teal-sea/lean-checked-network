"""Run the grader on one reply file against one task dir.
Usage: run_grade.py TASK_DIR REPLY_FILE [--timeout N] [--keep] [--no-guard] [--threads N]"""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean_mod_add_proof"))
from lean_mod_add_proof.grader import grade
args = sys.argv[1:]
def opt(name, default=None):
    if name in args:
        i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
    return default
timeout = float(opt("--timeout", 300)); threads = int(opt("--threads", 1))
keep = "--keep" in args; noguard = "--no-guard" in args
args = [a for a in args if not a.startswith("--")]
task = Path(args[0]); reply = Path(args[1]).read_text()
meta = json.loads((task / "meta.json").read_text())
net = Path(__file__).resolve().parent.parent / "lean_mod_add_proof/lean_mod_add_proof/Network.lean"
r = grade(reply, network_lean=net.read_text(), weights_lean=(task / "Weights.lean").read_text(),
          theorem_name=meta["theorem_name"], timeout_s=timeout, keep=keep, skip_text_guard=noguard,
          lean_threads=threads, work_root=str(Path(__file__).resolve().parent / "work"))
d = r.as_dict()
print(json.dumps({k: d[k] for k in ("reward", "stage", "reason", "axioms", "timings", "package_dir")}, indent=1))
for k, v in d["outputs"].items():
    print(f"--- {k} output ---"); print(v.rstrip()[-1500:] or "(empty)")
