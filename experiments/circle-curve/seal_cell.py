"""Kernel-check a trained network and its clock-plus-bias reduction, through the sweep's own stages.

Usage: python3 seal_cell.py final.npz OUTDIR [--repo DIR] [--jobs N] [--build-jobs N] [--energy-permille X]

Stages, as in sweep/run_one.py (whose functions this script imports): numpy evaluation of both
networks; generation of a fresh Lean package (Network.lean, Fast.lean, WrongSet.lean, and
experiments/circle-curve/Bridge.lean); lake build; leanchecker replay of every module; #print axioms;
the forbidden-token scan. Exit code is non-zero if any stage fails.

The reduction: per neuron, the dominant Fourier wave of each weight column (E1, E2, W2), rounded;
plus n constant neurons (E1 = 127, E2 = 0) whose read-out columns carry
    bias[c] = (W2 - W2_wave) . mean_pairs((E1_wave[a] + E2_wave[b])^2)
split into entries in [-127, 127]. The kernel checks, besides "wrong on exactly k pairs" for both
networks: shapes; the first H columns of the reduction are within --energy-permille of the trained
tables' energy (per table, exact integers); the extra E1 columns are 127 and the extra E2 columns 0.
The choice of wave and the bias construction are the measured step and are not checked.
"""
import argparse, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "sweep"))
from run_one import evaluate, write_network, run, STANDARD_AXIOMS, FORBIDDEN, table  # noqa: E402


def clock_bias(E1, E2, W2, p, H):
    half = (p - 1) // 2
    cols = [E1, E2, W2]
    one = [np.zeros(c.shape, dtype=np.int64) for c in cols]
    for h in range(H):
        Fs = [np.fft.fft(c[:, h]) for c in cols]
        k = int(np.argmax(sum(np.abs(F) ** 2 for F in Fs)[1:half + 1])) + 1
        for F, o in zip(Fs, one):
            G = np.zeros_like(F); G[k] = F[k]; G[p - k] = F[p - k]
            o[:, h] = np.round(np.fft.ifft(G).real).astype(np.int64)
    a = np.repeat(np.arange(p), p); b = np.tile(np.arange(p), p)
    act = (one[0][a] + one[1][b]) ** 2
    bias = (W2 - one[2]) @ act.mean(0)
    m = 127
    col = np.round(bias / (m * m)).astype(np.int64)
    n = int(np.ceil(np.abs(col).max() / 127))
    W2x = np.zeros((p, n), dtype=np.int64); rem = col.copy()
    for j in range(n):
        take = np.clip(rem, -127, 127); W2x[:, j] = take; rem = rem - take
    assert (rem == 0).all()
    E1r = np.concatenate([one[0], np.full((p, n), m, dtype=np.int64)], 1)
    E2r = np.concatenate([one[1], np.zeros((p, n), dtype=np.int64)], 1)
    W2r = np.concatenate([one[2], W2x], 1)
    energy = [float(((T - P) ** 2).sum() / (T ** 2).sum()) for T, P in zip(cols, one)]
    return (E1r, E2r, W2r), n, energy, bias


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("npz"); ap.add_argument("outdir")
    ap.add_argument("--repo", default=str(HERE.parent.parent))
    ap.add_argument("--jobs", type=int, default=2); ap.add_argument("--build-jobs", type=int, default=0)
    ap.add_argument("--energy-permille", type=int, default=0, help="bound stated per table; 0 = measured, rounded up")
    ap.add_argument("--pure-clock", action="store_true", help="seal the one-wave projection alone, no bias neurons")
    ap.add_argument("--chunks", type=int, default=16, help="row modules per network (default 16, as in every earlier seal); "
                    "more, smaller modules lower the memory of each Lean process for wide networks")
    ap.add_argument("--max-heartbeats", type=int, default=None, help="add `set_option maxHeartbeats N` to the generated "
                    "Weights files (an elaboration resource limit; the default 200000 is too small for 512-wide tables)")
    args = ap.parse_args()
    repo = Path(args.repo).resolve(); out = Path(args.outdir).resolve(); out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, OMP_NUM_THREADS="1"); env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    d = np.load(args.npz)
    p, H = int(d["p"]), int(d["H"])
    E1, E2, W2 = (d[k].astype(np.int64) for k in ["E1q", "E2q", "W2q"])
    (E1r, E2r, W2r), n, energy, bias = clock_bias(E1, E2, W2, p, H)
    if args.pure_clock:
        E1r, E2r, W2r, n, bias = E1r[:, :H], E2r[:, :H], W2r[:, :H], 0, np.zeros(p)
    permille = [args.energy_permille or int(np.ceil(e * 1000)) for e in energy]
    np.savez(out / "clock_bias.npz", E1q=E1r, E2q=E2r, W2q=W2r, bias=bias, n_bias_neurons=n, energy=np.array(energy), p=p, H=H)
    nets = {"trained": (E1, E2, W2), "clock_bias": (E1r, E2r, W2r)}
    evals = {k: evaluate(*v) for k, v in nets.items()}
    rc, commit, _ = run(["git", "rev-parse", "HEAD"], repo)
    result = {"source": str(Path(args.npz).resolve()), "config": {k: (d[k].item() if d[k].shape == () else None) for k in ["p", "H", "seed", "lr", "wd", "frac", "steps"]},
              "repo_commit": commit.strip() if rc == 0 else None, "lean_toolchain": (repo / "lean" / "lean-toolchain").read_text().strip(),
              "reduction": {"n_bias_neurons": n, "energy_outside_wave": energy, "energy_permille_stated": permille},
              "networks": {k: {kk: vv for kk, vv in ev.items() if kk != "wrong_pairs"} for k, ev in evals.items()},
              "stages": {}, "seconds": {}, "ok": False, "failures": []}
    def fail(stage, why): result["failures"].append({"stage": stage, "why": why}); print(f"FAIL [{stage}] {why}", file=sys.stderr)
    def save(): (out / "result.json").write_text(json.dumps(result, indent=1))
    for k, ev in evals.items():
        if not ev["w2_in_fast_range"]: fail("numpy", f"{k}: W2 outside [-128, 127]")
        if not ev["fast_digit_bound_ok"]: fail("numpy", f"{k}: digit bound")
    if result["failures"]: save(); sys.exit(1)

    # generate
    t0 = time.time()
    ldir = out / "lean"
    if ldir.exists(): shutil.rmtree(ldir)
    (ldir / "LeanCheckedNetwork").mkdir(parents=True)
    for f in ["lakefile.toml", "lean-toolchain"]: shutil.copy(repo / "lean" / f, ldir / f)
    for f in ["Network.lean", "Fast.lean"]: shutil.copy(repo / "lean" / "LeanCheckedNetwork" / f, ldir / "LeanCheckedNetwork" / f)
    shutil.copy(repo / "sweep" / "WrongSet.lean", ldir / "LeanCheckedNetwork" / "WrongSet.lean")
    shutil.copy(HERE / "Bridge.lean", ldir / "LeanCheckedNetwork" / "Bridge.lean")
    tag = re.sub(r"[^A-Za-z0-9]", "_", Path(args.npz).stem)
    tag = "C_" + tag
    lib = f"LeanCheckedNetwork.Seal.{tag}"
    root = ldir / "LeanCheckedNetwork" / "Seal" / tag
    chunks = min(p, args.chunks)
    desc = json.dumps(result["config"])
    modules = ["LeanCheckedNetwork.Network", "LeanCheckedNetwork.Fast", "LeanCheckedNetwork.WrongSet", "LeanCheckedNetwork.Bridge"]
    main_theorems = {}
    for name, key, net_desc, Hn in [("Trained", "trained", "the trained network, weights frozen to whole numbers", H),
                                    ("ClockBias", "clock_bias", (f"the clock-plus-bias reduction: one wave per neuron plus {n} constant bias neurons" if n else "the one-wave reduction: each neuron reduced to its dominant wave, no bias neurons"), H + n)]:
        wrong_rows = [[] for _ in range(p)]
        for a, b in evals[key]["wrong_pairs"]: wrong_rows[a].append(b)
        mods, k = write_network(root, lib, name, desc, net_desc, *nets[key], wrong_rows, chunks, p, Hn, Path(args.npz).name)
        if args.max_heartbeats is not None:
            wf = root / name / "Weights.lean"; t = wf.read_text()
            assert t.count("set_option maxRecDepth 100000\n") == 1
            wf.write_text(t.replace("set_option maxRecDepth 100000\n", f"set_option maxRecDepth 100000\nset_option maxHeartbeats {args.max_heartbeats}\n"))
        modules += mods
        main_theorems[key] = [f"{lib}.{name}.answer_iff_not_wrong"] + ([f"{lib}.{name}.adds_mod_{p}"] if k == 0 else [f"{lib}.{name}.wrongPairs_length", f"{lib}.{name}.wrongPairs_nodup", f"{lib}.{name}.wrongPairs_in_range"])
    (root / "Bridge.lean").write_text(f"""import LeanCheckedNetwork.Bridge
import {lib}.Trained.Weights
import {lib}.ClockBias.Weights

/-! How the clock-plus-bias tables relate to the trained tables, in exact integer arithmetic. -/

namespace {lib}

open LeanCheckedNetwork

theorem shape_E1 : shapeOk Trained.E1 ClockBias.E1 {p} {H} {n} = true := by decide +kernel
theorem shape_E2 : shapeOk Trained.E2 ClockBias.E2 {p} {H} {n} = true := by decide +kernel
theorem shape_W2 : shapeOk Trained.W2 ClockBias.W2 {p} {H} {n} = true := by decide +kernel

/-- The first {H} columns of the reduction's `E1` are within {permille[0]}/1000 of the trained `E1`'s energy. -/
theorem energy_E1 : energyWithin Trained.E1 ClockBias.E1 {H} {permille[0]} 1000 = true := by decide +kernel
theorem energy_E2 : energyWithin Trained.E2 ClockBias.E2 {H} {permille[1]} 1000 = true := by decide +kernel
theorem energy_W2 : energyWithin Trained.W2 ClockBias.W2 {H} {permille[2]} 1000 = true := by decide +kernel

/-- The {n} extra neurons are constant: `E1` entries 127, `E2` entries 0. -/
theorem extra_E1 : extraColsConst ClockBias.E1 {H} (.ofNat 127) = true := by decide +kernel
theorem extra_E2 : extraColsConst ClockBias.E2 {H} (.ofNat 0) = true := by decide +kernel

end {lib}
""")
    modules.append(f"{lib}.Bridge")
    main_theorems["bridge"] = [f"{lib}.{t}" for t in ["shape_E1", "shape_E2", "shape_W2", "energy_E1", "energy_E2", "energy_W2", "extra_E1", "extra_E2"]]
    (ldir / "LeanCheckedNetwork.lean").write_text(f"import {lib}.Trained.AllInputs\nimport {lib}.ClockBias.AllInputs\nimport {lib}.Bridge\n")
    result["seconds"]["gen"] = round(time.time() - t0, 1); result["stages"]["gen"] = {"modules": modules, "main_theorems": main_theorems}; save()

    # build
    build_env = dict(env, LEAN_NUM_THREADS=str(args.build_jobs)) if args.build_jobs else env
    rc, log, dt = run(["lake", "build", "LeanCheckedNetwork"], ldir, env=build_env, log=out / "build.log")
    result["seconds"]["build"] = round(dt, 1)
    build_ok = rc == 0 and "Build completed successfully" in log
    sorry_w = log.count("declaration uses 'sorry'") + log.count("declaration uses `sorry`")
    result["stages"]["build"] = {"exit": rc, "completed": build_ok, "sorry_warnings": sorry_w, "errors": [l for l in log.splitlines() if "error" in l][:20]}
    if not build_ok: fail("build", f"lake build exit {rc}")
    if sorry_w: fail("build", "a declaration uses sorry")
    save()

    # replay
    replay = {}; t0 = time.time()
    if build_ok:
        pending = list(modules); procs = []
        while pending or procs:
            while pending and len(procs) < args.jobs:
                m = pending.pop(0); lg = open(out / f"leanchecker.{m}.log", "w")
                procs.append((m, subprocess.Popen(["lake", "env", "leanchecker", m], cwd=ldir, env=env, stdout=lg, stderr=subprocess.STDOUT), lg, time.time()))
            time.sleep(0.5); still = []
            for m, pr, lg, ts in procs:
                if pr.poll() is None: still.append((m, pr, lg, ts))
                else: lg.close(); replay[m] = {"exit": pr.returncode, "seconds": round(time.time() - ts, 1)}
            procs = still
        bad = [m for m, r in replay.items() if r["exit"] != 0]
        if bad: fail("replay", f"leanchecker failed on {bad}")
    result["seconds"]["replay"] = round(time.time() - t0, 1); result["stages"]["replay"] = {"ok": sum(1 for r in replay.values() if r["exit"] == 0), "of": len(modules), "modules": replay}; save()

    # axioms
    axioms = {}
    if build_ok:
        src = "import LeanCheckedNetwork\n" + "".join(f"#print axioms {t}\n" for ts in main_theorems.values() for t in ts)
        (ldir / "Axioms.lean").write_text(src)
        rc, log, dt = run(["lake", "env", "lean", "Axioms.lean"], ldir, env=env, log=out / "axioms.log")
        # Lean wraps a long axiom list over several lines; join them before matching
        joined = re.sub(r",\s*\n\s*", ", ", log)
        for line in joined.splitlines():
            mm = re.match(r"'(.+)' depends on axioms: \[(.*)\]", line)
            if mm: axioms[mm.group(1)] = [x.strip() for x in mm.group(2).split(",") if x.strip()]
            elif "does not depend on any axioms" in line: axioms[line.split("'")[1]] = []
        expected = [t for ts in main_theorems.values() for t in ts]
        for t in expected:
            if t not in axioms: fail("axioms", f"no axiom report for {t}")
            elif not set(axioms[t]) <= set(STANDARD_AXIOMS): fail("axioms", f"{t} uses {axioms[t]}")
    result["stages"]["axioms"] = axioms

    # scan
    hits = []
    for f in ldir.rglob("*.lean"):
        txt = f.read_text()
        for w in FORBIDDEN:
            if w in txt: hits.append(f"{f.relative_to(ldir)}: {w}")
    if hits: fail("scan", f"forbidden tokens: {hits[:10]}")
    result["stages"]["scan"] = {"hits": hits}
    result["ok"] = not result["failures"]
    save()
    print(json.dumps({k: result[k] for k in ["ok", "failures", "seconds", "reduction"]}, indent=1))
    sys.exit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
