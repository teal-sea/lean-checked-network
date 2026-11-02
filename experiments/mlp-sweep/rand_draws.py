"""Ten fresh random-frequency draws on two retrained checkpoints (eleventh batch follow-up, 2026-11-02).

filters.py's `rand` reading uses one draw per run (generator 1000 + the run's seed). This script retrains two
cells with train_act.py (deterministic: x^2, p 97, frac 0.3, lr 0.01, weight decay 0; H 4096 seed 0 to step 1,
H 2048 seed 0 to step 5), draws each neuron's frequency uniformly from 1..(p-1)/2 with generators 50,000 to
50,009, keeps DFT rows k and p - k of each neuron's float columns and counts wrong pairs on all p^2, exactly as
filters.py's `rand` reading does.

Usage: python3 rand_draws.py OUTDIR  -> OUTDIR/rand_draws.txt (the two checkpoints are written under OUTDIR).
"""
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import filters as F  # noqa: E402

CELLS = (("H4096_s0_step1", 4096, 1), ("H2048_s0_step5", 2048, 5))


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    lines = []
    for name, H, steps in CELLS:
        run = os.path.join(out, name)
        env = dict(os.environ, EXTRA_STEPS=str(steps), OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
        subprocess.run([sys.executable, os.path.join(HERE, "train_act.py"), "sq", "97", str(H), "0", "1e-2", "0.0",
                        "0.30", str(steps), run], env=env, check=True, stderr=subprocess.DEVNULL)
        d = np.load(os.path.join(run, "final.npz"))
        p = int(d["p"])
        spec = F.spectra([d[k] for k in F.FLOATS])
        draws = [F.wrong(*F.keep(spec, p, np.random.default_rng(50_000 + g).integers(1, (p - 1) // 2 + 1, H)), p,
                         F.ACTS["sq"])[0] for g in range(10)]
        lines.append(f"{name}: wrong pairs of {p * p:,} for generators 50000 to 50009: {draws}")
        print(lines[-1], flush=True)
    with open(os.path.join(out, "rand_draws.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
