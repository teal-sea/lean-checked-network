"""Write a task folder from a network that is WRONG on some pairs (for test vi). Usage: make_wrong_task.py RUN.npz OUT_DIR"""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean_mod_add_proof"))
from lean_mod_add_proof.gen_dataset import weights_lean, check_network
net = np.load(sys.argv[1]); out = Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
p, H, seed = int(net["p"]), int(net["H"]), int(net["seed"])
E1, E2, W2 = (net[k].astype(np.int64) for k in ("E1q", "E2q", "W2q"))
wrong, ties = check_network(E1, E2, W2)
(out / "Weights.lean").write_text(weights_lean(p, H, E1, E2, W2, f"WRONG network for tests: {Path(sys.argv[1]).name}"))
(out / "meta.json").write_text(json.dumps({"task_id": out.name, "p": p, "H": H, "seed": seed, "theorem_name": f"LeanCheckedNetwork.Net.adds_mod_{p}", "wrong": wrong, "ties": ties}, indent=1))
print(f"wrote {out}: p={p} H={H} wrong on {wrong} of {p*p} pairs, ties {ties}")
