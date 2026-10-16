"""Write grid.json: the first sweep (130 points in five blocks), with a cost estimate per point.

Usage: python3 make_grid.py [OUT.json]

Cost model (see README.md). Kernel time per network is proportional to p^2 (H + p): p rows, p
inputs per row, and per input the fast evaluator does about H big-number steps plus about p
steps to unpack and compare the scores. The constant comes from the repo's own figure
(README.md, 'both networks checked in 26 minutes on a 4-core machine'; lean_run.log itself
records a cached build of 0 s and a 21-minute replay): both networks at p=113, H=128 built in 26 minutes on 4 cores, so one network
is about 3,120 core-seconds, and 3120 / (113^2 * 241) = 1.01e-3 core-seconds per unit.
The leanchecker replay re-does the kernel work (21 minutes against 26 in the repo's log): 0.8x.
Training (train.py, one numpy thread) is 20 minutes at p=113, H=128, 6,384 training pairs,
20,000 steps: 7.3e-8 seconds per (step x training pair x neuron). On Modal a container is
billed for what it requests, so training on one thread still pays for 4 cores and 16 GiB.
"""
import json
import sys

K_KERNEL = 3120 / (113 ** 2 * (128 + 113))   # core-seconds per unit of p^2 (H + p), one network, lake build
REPLAY = 0.8                                  # leanchecker replay relative to the build
K_TRAIN = 1200 / (20000 * 6384 * 128)         # seconds per step x training pair x neuron, one thread
CPU_PRICE = 0.0000131                         # USD per physical core per second, modal.com/pricing, read 2026-10-16
MEM_PRICE = 0.00000222                        # USD per GiB per second, same page
CORES, MEM_GIB = 4, 16


def estimate(p, H, frac, steps):
    n_train = round(frac * p * p)
    train_wall = K_TRAIN * steps * n_train * H
    build_core = 2 * K_KERNEL * p * p * (H + p)          # two networks
    replay_core = REPLAY * build_core
    replay_jobs = 4 if H <= 128 else 2
    wall = train_wall + build_core / CORES + replay_core / replay_jobs
    billed_core_h = CORES * wall / 3600                   # requested cores are billed for the whole run
    usd = wall * (CORES * CPU_PRICE + MEM_GIB * MEM_PRICE)
    return {"est_train_min": round(train_wall / 60, 1), "est_kernel_core_h": round((build_core + replay_core) / 3600, 2),
            "est_wall_h": round(wall / 3600, 2), "est_billed_core_h": round(billed_core_h, 2), "est_usd": round(usd, 3)}


points = []
STEPS = 20000
# The grid crosses the boundaries the literature reports for this architecture (sources read
# 2026-10-16: Doshi, Das, He, Gromov, ICLR 2024, Fig. 3a and Fig. 29, the only published fraction x
# weight-decay map for a two-layer quadratic network, p = 97: generalisation starts between about 0.23
# and 0.33 of the pairs depending on weight decay, with a collapse regime at high decay; Gromov 2023
# Fig. 4a: AdamW pushes the boundary to about 0.15 to 0.18 with long training, and Fig. 4b: width
# above about 50 does not move it at p = 97; Nanda et al. 2023 Fig. 20 and Fig. 24: at p = 113 a
# transformer groks at 0.3 and not at 0.2, and p = 53 needs weight decay 5 instead of 1; Varma et
# al. 2023: semi-grokking between 12 and 16 percent of pairs only after about 1e7 epochs). Weight
# decay values do not transfer between papers (parametrisation and loss differ), only their order;
# train.py is cross-entropy with decoupled weight decay in standard parametrisation.
def add(p, H, seed, frac, wd, steps=STEPS, block=""):
    points.append({"p": p, "H": H, "seed": seed, "frac": frac, "wd": wd, "steps": steps, "block": block})
# A. The main plane at p = 97, H = 128: 8 fractions crossing the boundary x 4 decays x 3 seeds.
for frac in [0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.50, 0.70]:
    for wd in [0.0, 0.1, 1.0, 3.0]:
        for seed in [0, 1, 2]:
            add(97, 128, seed, frac, wd, block="A main plane")
# B. Width at the canonical point (fraction 0.3, decay 1): 24 is below the width Gromov reports as
# enough, 48 = (p - 1) / 2 is one neuron per frequency, 96 = p - 1, 192 and 256 above; 256 is the
# largest the fast evaluator's digit bound allows (H <= 261), so Morwani's 4(p - 1) = 384 is out.
for H in [24, 48, 96, 192, 256]:
    for seed in [0, 1, 2]:
        add(97, H, seed, 0.30, 1.0, block="B width")
# C. Other primes at fraction 0.3, H = 128: 113 (the repo's prime), and 53, which Nanda et al.
# report needs a larger decay than 1.
for seed in [0, 1, 2]:
    add(113, 128, seed, 0.30, 1.0, block="C prime 113")
    for wd in [1.0, 5.0]:
        add(53, 128, seed, 0.30, wd, block="C prime 53")
# D. The collapse probe: very large decay at a fraction that otherwise generalises, where
# integer freezing is expected to fail first (tiny weights lose resolution under a 127 scale).
for wd in [10.0, 20.0]:
    for seed in [0, 1]:
        add(97, 128, seed, 0.50, wd, block="D collapse probe")
# E. The long tail: fractions below the boundary with ten times the steps, where Varma et al.
# found grokking only after very long training.
for frac in [0.10, 0.125, 0.15]:
    for seed in [0, 1]:
        add(97, 128, seed, frac, 1.0, steps=10 * STEPS, block="E long tail")
for pt in points:
    pt.update(estimate(pt["p"], pt["H"], pt["frac"], pt["steps"]))
tot = {k: round(sum(pt[k] for pt in points), 2) for k in ["est_kernel_core_h", "est_wall_h", "est_billed_core_h", "est_usd"]}
tot["points"] = len(points)
tot["largest_point_wall_h"] = max(pt["est_wall_h"] for pt in points)
meta = {"written": "2026-10-16", "cost_model": "see make_grid.py and README.md",
        "prices": {"cpu_usd_per_core_s": CPU_PRICE, "mem_usd_per_gib_s": MEM_PRICE, "source": "modal.com/pricing, read 2026-10-16"},
        "container": {"cpu": CORES, "memory_gib_requested": MEM_GIB}, "totals": tot}
out = sys.argv[1] if len(sys.argv) > 1 else "grid.json"
json.dump({"meta": meta, "points": points}, open(out, "w"), indent=1)
print(json.dumps(tot, indent=1))
by = {}
for pt in points:
    by.setdefault((pt["block"], pt["p"], pt["H"]), []).append(pt)
for (block, p, H), pts in sorted(by.items()):
    print(f"[{block}] ", end="")
    print(f"p={p:3d} H={H:3d}: {len(pts):3d} points, per point wall {pts[0]['est_wall_h']} h (train {pts[0]['est_train_min']} min at frac {pts[0]['frac']}), "
          f"kernel {pts[0]['est_kernel_core_h']} core-h, ${pts[0]['est_usd']}; subtotal ${round(sum(x['est_usd'] for x in pts), 2)}")
