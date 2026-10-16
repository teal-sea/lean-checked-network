"""Turn frozen networks (train.py .npz files) into tasks for the environment.

Usage: python3 gen_dataset.py OUT_DIR RUN.npz [RUN.npz ...]

Each .npz is re-checked in numpy exactly as Network.lean evaluates (highest score, first index
on a tie). Only networks right on every pair become tasks. For each kept network this writes
OUT_DIR/<task_id>/Weights.lean and OUT_DIR/<task_id>/meta.json, and OUT_DIR/tasks.jsonl listing
them with their split. The split is by seed: seed 2 is eval, the rest train (set in SPLIT_SEED).
"""

import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
NETWORK_LEAN = (HERE / "Network.lean").read_text()
EVAL_SEEDS = {2}


def lit(x: int) -> str:
    """An Int literal as a constructor, like the repo's gen_lean.py."""
    return f"(.ofNat {x})" if x >= 0 else f"(.negSucc {-x - 1})"


def table(m) -> str:
    return "[\n" + ",\n".join("  [" + ", ".join(lit(int(x)) for x in row) + "]" for row in m) + "]"


def weights_lean(p: int, H: int, E1, E2, W2, origin: str) -> str:
    return f"""import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod {p}

{p} possible inputs per side, {H} neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: {origin.replace("/-", "/ -").replace("-/", "- /")}.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := {p}

def E1 : List (List Int) := {table(E1)}

def E2 : List (List Int) := {table(E2)}

def W2 : List (List Int) := {table(W2)}

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < {p} → ∀ b, b < {p} → answer a b = (a + b) % {p}

end LeanCheckedNetwork.Net
"""


def check_network(E1, E2, W2) -> tuple[int, int]:
    """(wrong pairs, ties) evaluated as Network.lean does; int64 is exact for these sizes."""
    p = E1.shape[0]
    a, b = np.divmod(np.arange(p * p), p)
    z = E1[a] + E2[b]
    S = (z * z) @ W2.T
    pred = S.argmax(1)
    top2 = np.sort(S, 1)[:, -2:]
    return int((pred != (a + b) % p).sum()), int((top2[:, 0] == top2[:, 1]).sum())


def main(out_dir: str, runs: list[str]) -> None:
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for run in runs:
        net = np.load(run)
        p, H, seed = int(net["p"]), int(net["H"]), int(net["seed"])
        E1, E2, W2 = (net[k].astype(np.int64) for k in ("E1q", "E2q", "W2q"))
        assert all(np.abs(t).max() <= 127 for t in (E1, E2, W2))
        wrong, ties = check_network(E1, E2, W2)
        if wrong or ties:
            print(f"skip {run}: wrong {wrong}, ties {ties}")
            continue
        task_id = f"p{p}_h{H}_s{seed}"
        d = out / task_id
        d.mkdir(exist_ok=True)
        origin = (f"train.py p={p} H={H} seed={seed} lr={float(net['lr'])} wd={float(net['wd'])} "
                  f"train_fraction={float(net['frac'])} steps={int(net['steps'])}")
        (d / "Weights.lean").write_text(weights_lean(p, H, E1, E2, W2, origin))
        meta = {
            "task_id": task_id, "p": p, "H": H, "seed": seed,
            "train_fraction": float(net["frac"]), "steps": int(net["steps"]), "wd": float(net["wd"]),
            "theorem_name": f"LeanCheckedNetwork.Net.adds_mod_{p}",
            "split": "eval" if seed in EVAL_SEEDS else "train",
            "pairs": p * p, "wrong": wrong, "ties": ties,
        }
        (d / "meta.json").write_text(json.dumps(meta, indent=1))
        rows.append(meta)
        print(f"task {task_id}: {meta['split']}, {p*p} pairs all right")
    rows.sort(key=lambda r: (r["p"], r["H"], r["seed"]))
    (out / "tasks.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    print(f"{len(rows)} tasks written to {out}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
