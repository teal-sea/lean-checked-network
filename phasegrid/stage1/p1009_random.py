"""The random-S cases at p = 1009 (the main run stopped at the S = {1} int64 assertion before them)."""
import sys, numpy as np
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
from rounding2 import run_case
p = 1009; rng = np.random.default_rng(p); top = (p - 1) // 2
for d in (3, 5):
    Sr = sorted(rng.choice(np.arange(1, top + 1), size=d, replace=False).tolist())
    run_case(p, Sr, f"random {d}", 30)
