"""Run the sweep on Modal: one container per grid point, each calling sweep/run_one.py.

NOT RUN HERE: this file was written in a container with no Modal token. Everything that does
work is in run_one.py, which was tested locally; this file only ships the repo into an image,
calls run_one.py, and copies the results to a Volume.

From a machine with a Modal token (pip install modal; modal setup), from the repo root:

    modal run sweep/modal_sweep.py --grid sweep/grid.json

Options: --limit N runs only the first N points; --force reruns points that already have a
result.json on the Volume. Results land on the Volume "lean-checked-network-sweep" as
<tag>/result.json plus the logs and the generated Lean sources (without .lake). Fetch them with

    modal volume get lean-checked-network-sweep / sweep-results
    python3 sweep/summarise.py sweep-results

Modal API used (read 2026-10-16 from modal.com/docs/guide/images, /guide/volumes,
/guide/resources, /guide/scale, /guide/apps, /guide/retries, /guide/timeouts and
/docs/reference/modal.Retries):
  modal.Image.debian_slim(python_version=...).apt_install(...).pip_install(...)
       .run_commands(...).env({...}).add_local_dir(path, remote_path=..., copy=True, ignore=[...])
  modal.Volume.from_name(name, create_if_missing=True); volumes={"/results": vol}; vol.commit()
  @app.function(cpu=4.0, memory=(request_mib, limit_mib), timeout=seconds, retries=modal.Retries(...))
  Function.map(inputs, return_exceptions=True); @app.local_entrypoint() with typed CLI options.
"""
import json
import os
import shutil
import sys
from pathlib import Path

import modal

TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
REPO = Path(__file__).resolve().parent.parent    # the lean-checked-network checkout, sweep/ inside it
VOLUME_NAME = "lean-checked-network-sweep"

# The toolchain is installed at image build, so every container starts with Lean ready.
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "git", "ca-certificates")
    .pip_install("numpy==2.5.3")   # the version the local tests ran with
    .run_commands(
        "curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
        f" | sh -s -- -y --default-toolchain {TOOLCHAIN}",
        "/root/.elan/bin/lean --version",
    )
    .env({"PATH": "/root/.elan/bin:/usr/local/bin:/usr/bin:/bin", "OMP_NUM_THREADS": "1"})
    .add_local_dir(str(REPO), remote_path="/root/lcn", copy=True,
                   ignore=["**/.lake/**", ".git/**", "**/__pycache__/**", "runs/*.npz", "bench/**", "sweep-results/**"])
    # fail at image build, not at run time, if the toolchain and the package do not agree
    .run_commands("cd /root/lcn/lean && lake build LeanCheckedNetwork.Fast && cat lean-toolchain")
)

vol = modal.Volume.from_name(VOLUME_NAME, create_if_missing=True)
app = modal.App("lean-checked-network-sweep", image=image)


def tag_of(pt):
    """Same configuration tag as run_one.py's Lean namespace, used as the result directory."""
    def num(x):
        return f"{x:g}".replace("-", "m").replace(".", "p").replace("+", "")
    return f"P{pt['p']}_H{pt['H']}_S{pt['seed']}_F{num(pt['frac'])}_WD{num(pt['wd'])}_ST{pt['steps']}"


@app.function(
    cpu=4.0,
    # lake build is capped at 4 Lean processes by --build-jobs (about 2 GB each at p=113, H=128; more at H=256),
    # and the replay runs 2 leanchecker processes at once: 16 GiB requested, 24 GiB hard limit.
    memory=(16384, 24576),
    timeout=4 * 3600,          # the largest grid point is estimated under 2 h on 4 cores
    retries=modal.Retries(max_retries=2, initial_delay=10.0, backoff_coefficient=2.0),
    volumes={"/results": vol},
)
def run_point(pt: dict) -> dict:
    import subprocess
    tag = tag_of(pt)
    dest = Path("/results") / tag
    if not pt.get("force") and (dest / "result.json").exists():
        r = json.loads((dest / "result.json").read_text())
        return {"tag": tag, "skipped": True, "ok": r.get("ok"), "kernel": r.get("kernel"), "seconds": r.get("seconds")}
    work = Path("/tmp/work") / tag
    if work.exists():
        shutil.rmtree(work)
    cmd = [sys.executable, "/root/lcn/sweep/run_one.py", str(pt["p"]), str(pt["H"]), str(pt["seed"]), str(pt["frac"]),
           str(pt["wd"]), str(pt["steps"]), str(work), "--repo", "/root/lcn",
           # replay 4 modules at once (about 2 GB each at H <= 128), 2 at once for the larger networks;
           # the build gets the same cap, because the container reports 20 cores, not the 4 requested
           "--jobs", "4" if pt["H"] <= 128 else "2",
           "--build-jobs", "4" if pt["H"] <= 128 else "2"]
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    # keep everything except the compiled .lake tree and the negative-control copy
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(work, dest, ignore=shutil.ignore_patterns(".lake", "negative_control"))
    (dest / "run_one.stdout.log").write_text(r.stdout)
    vol.commit()
    out = {"tag": tag, "skipped": False, "exit": r.returncode, "ok": False, "kernel": None, "seconds": None}
    if (work / "result.json").exists():
        res = json.loads((work / "result.json").read_text())
        out.update(ok=res.get("ok"), kernel=res.get("kernel"), seconds=res.get("seconds"), failures=res.get("failures"))
    else:
        out["stdout_tail"] = r.stdout[-2000:]
    return out


@app.local_entrypoint()
def main(grid: str = "sweep/grid.json", limit: int = 0, force: bool = False):
    points = json.loads(Path(grid).read_text())["points"]
    if limit:
        points = points[:limit]
    print(f"{len(points)} points from {grid}; results go to Volume {VOLUME_NAME}")
    rows = []
    inputs = [dict(pt, force=force) for pt in points]
    for pt, res in zip(points, run_point.map(inputs, return_exceptions=True)):
        if isinstance(res, Exception):
            rows.append((tag_of(pt), "EXCEPTION", str(res)[:80], "", ""))
            continue
        k = res.get("kernel") or {}
        def v(key):
            e = k.get(key) or {}
            return ("pass" if e.get("status") == "pass" else "FAIL") + f" wrong={e.get('wrong_count')}"
        s = res.get("seconds") or {}
        rows.append((res["tag"], "skipped" if res.get("skipped") else ("ok" if res.get("ok") else "FAIL"),
                     v("trained"), v("circle_only"), f"{s.get('total', '')}s"))
        print(f"{rows[-1][0]:40s} {rows[-1][1]:8s} trained {rows[-1][2]:18s} circle {rows[-1][3]:18s} {rows[-1][4]}", flush=True)
    print()
    print(f"{'tag':40s} {'run':8s} {'trained':20s} {'circle-only':20s} seconds")
    for r in rows:
        print(f"{r[0]:40s} {r[1]:8s} {r[2]:20s} {r[3]:20s} {r[4]}")
    n_ok = sum(1 for r in rows if r[1] in ("ok", "skipped"))
    print(f"\n{n_ok} of {len(rows)} points have a result; fetch with: modal volume get {VOLUME_NAME} / sweep-results")
