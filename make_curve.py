"""Turn the checkpoints of a training run into count theorems: a learning curve whose every point is a theorem.

Usage: python3 make_curve.py RUN_PREFIX NAME_PREFIX STEP1,STEP2,...
  e.g. python3 make_curve.py /path/runs/p113_h64 H64Step 2000,4000,6000,8000,10000,12000

For each step: copies RUN_PREFIX_step{STEP}.npz into network/, writes the weights and table with
gen_lean.py (no row proofs: the network need not be right everywhere), and the count theorems with
gen_count.py. Prints the numpy count for each checkpoint, which the kernel then has to agree with.
"""
import subprocess, sys, shutil
from pathlib import Path
import numpy as np

run, prefix, steps = sys.argv[1], sys.argv[2], [int(s) for s in sys.argv[3].split(",")]
for step in steps:
    src = Path(f"{run}_step{step}.npz")
    dst = Path("network") / f"{Path(run).name}_step{step}.npz"
    shutil.copy(src, dst)
    net = np.load(dst)
    p = int(net["p"]); a, b = np.divmod(np.arange(p * p), p)
    E1, E2, W2 = net["E1q"], net["E2q"], net["W2q"]
    right = int((((E1[a] + E2[b]) ** 2 @ W2.T).argmax(1) == (a + b) % p).sum())
    name = f"{prefix}{step}"
    subprocess.run([sys.executable, "gen_lean.py", str(dst), name, "4", "norows"], check=True)
    subprocess.run([sys.executable, "gen_count.py", str(dst), name, "8"], check=True)
    print(f"step {step}: {name}, right on {right} of {p * p} (numpy); train pairs {len(net['train_idx'])}")
