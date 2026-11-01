"""Run seal_cell.py and seal_negative_control.py on e2b sandboxes, one sandbox per job.

Usage (API key in the environment as E2B_API_KEY, or as `e2b` when run under with-secrets):
    python3 e2b_seal.py build                 # build the template once (Lean toolchain + repo files)
    python3 e2b_seal.py run JOBS.json OUT_DIR # one sandbox per job, results downloaded to OUT_DIR

JOBS.json: a list of {"name": ..., "kind": "seal" | "negative", ...}:
  seal:     {"npz": local path, "pure_clock": bool}
  negative: {"seal_dir": local seals/<cell> directory (its lean/ sources and result.json are uploaded),
             "only": optional, one of positive | drop_pair | energy_bound | extra_entry | shape}
Each sandbox gets CPU_COUNT cores and MEMORY_MB of memory (the template's size); the seal runs with
--jobs REPLAY_JOBS --build-jobs BUILD_JOBS (3 Lean processes fit in 8 GiB). E2B_DOMAIN in the environment
points the same script at an E2B-compatible provider (Novita: sandbox.novita.ai). Results: OUT_DIR/<name>/ holds result.json, logs and the generated
Lean sources (no .lake), exactly as seal_cell.py writes them; OUT_DIR/<name>.log is the sandbox's
stdout. Nothing is printed that could contain the key."""
import io, json, os, sys, tarfile, time, shutil, threading
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
ALIAS = "lcn-seal"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
CPU_COUNT = int(os.environ.get("E2B_CPU", "8"))
MEMORY_MB = int(os.environ.get("E2B_MEM_MB", "8192"))
BUILD_JOBS = int(os.environ.get("E2B_BUILD_JOBS", "3" if MEMORY_MB <= 8192 else "6"))   # about 2 GB per Lean process on these tables
REPLAY_JOBS = int(os.environ.get("E2B_REPLAY_JOBS", "2"))
SANDBOX_TIMEOUT = int(os.environ.get("E2B_TIMEOUT", str(3 * 3600)))

if "E2B_API_KEY" not in os.environ and os.environ.get("e2b"):
    os.environ["E2B_API_KEY"] = os.environ["e2b"]
from e2b import Sandbox, Template  # noqa: E402


def bundle_dir():
    """The files the sandbox needs, laid out as in the repo."""
    b = HERE / ".e2b_bundle"
    if b.exists(): shutil.rmtree(b)
    (b / "lean").mkdir(parents=True); (b / "sweep").mkdir(); (b / "experiments" / "circle-curve").mkdir(parents=True)
    shutil.copytree(REPO / "lean", b / "lean", dirs_exist_ok=True, ignore=shutil.ignore_patterns(".lake"))
    for f in ["run_one.py", "WrongSet.lean"]: shutil.copy(REPO / "sweep" / f, b / "sweep" / f)
    for f in ["seal_cell.py", "Bridge.lean", "seal_verdict.py", "seal_negative_control.py", "unmask.py"]:
        shutil.copy(HERE / f, b / "experiments" / "circle-curve" / f)
    (b / ".git").mkdir(); (b / ".git" / "HEAD").write_text("ref: refs/heads/none\n")   # run_one's git rev-parse may fail harmlessly
    return b


def build():
    b = bundle_dir()
    tpl = (Template(file_context_path=b)
           .from_python_image("3.12")
           .apt_install(["curl", "git", "ca-certificates", "tar"])
           .pip_install(["numpy==2.5.3"])
           .run_cmd(f"curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain {TOOLCHAIN}")
           .set_envs({"PATH": "/root/.elan/bin:/usr/local/bin:/usr/bin:/bin", "OMP_NUM_THREADS": "1", "HOME": "/root"})
           .copy(".", "/root/lcn")
           .run_cmd("cd /root/lcn/lean && /root/.elan/bin/lake build LeanCheckedNetwork.Fast && /root/.elan/bin/lean --version")
           .run_cmd("chmod -R a+rwX /root"))
    info = Template.build(tpl, alias=ALIAS, cpu_count=CPU_COUNT, memory_mb=MEMORY_MB,
                          on_build_logs=lambda e: print(f"[build] {getattr(e, 'message', e)}", flush=True))
    print("built", ALIAS, "cpu", CPU_COUNT, "mem", MEMORY_MB, "->", info)


def tar_bytes(src: Path, arcname: str, exclude=(".lake",)) -> bytes:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as t:
        t.add(src, arcname=arcname, filter=lambda ti: None if any(f"/{e}/" in ti.name + "/" or ti.name.endswith(f"/{e}") for e in exclude) else ti)
    return buf.getvalue()


def run_job(job, out_dir: Path):
    name = job["name"]; log = open(out_dir / f"{name}.log", "w")
    def say(s): log.write(s); log.flush()
    t0 = time.time()
    sbx = Sandbox.create(template=ALIAS, timeout=SANDBOX_TIMEOUT, metadata={"job": name})
    try:
        say(f"sandbox {sbx.sandbox_id} for {name}\n")
        r = sbx.commands.run("nproc; free -m | head -2; /root/.elan/bin/lean --version", user="root", timeout=120)
        say(r.stdout + r.stderr)
        if job["kind"] == "seal":
            npz = Path(job["npz"]); remote = f"/root/work/{npz.name}"
            sbx.files.write(remote, npz.read_bytes(), user="root")
            cmd = (f"cd /root/lcn/experiments/circle-curve && python3 seal_cell.py {remote} /root/work/out --repo /root/lcn "
                   f"--jobs {REPLAY_JOBS} --build-jobs {BUILD_JOBS}" + (" --pure-clock" if job.get("pure_clock") else "") +
                   " ; python3 seal_verdict.py /root/work/ ; true")
        else:
            seal = Path(job["seal_dir"])
            sbx.files.write("/root/work/seal.tgz", tar_bytes(seal, "seal"), user="root")
            cmd = ("cd /root/work && tar xzf seal.tgz && cd /root/lcn/experiments/circle-curve && "
                   f"python3 seal_negative_control.py /root/work/seal /root/work/out --build-jobs {BUILD_JOBS}" + (f" --only {job['only']}" if job.get("only") else "") + " ; true")
        r = sbx.commands.run(cmd, user="root", timeout=SANDBOX_TIMEOUT - 600, on_stdout=say, on_stderr=say)
        say(f"\n[exit {r.exit_code}]\n")
        r = sbx.commands.run("cd /root/work && tar czf out.tgz --exclude=.lake out && ls -la out.tgz", user="root", timeout=600)
        say(r.stdout + r.stderr)
        data = sbx.files.read("/root/work/out.tgz", format="bytes", user="root")
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as t:
            dest = out_dir / name
            if dest.exists(): shutil.rmtree(dest)
            t.extractall(out_dir / f".{name}.tmp")
        shutil.move(str(out_dir / f".{name}.tmp" / "out"), str(out_dir / name)); shutil.rmtree(out_dir / f".{name}.tmp", ignore_errors=True)
        say(f"downloaded to {out_dir / name} after {time.time() - t0:.0f}s\n")
        return name, True
    except Exception as e:
        say(f"\nERROR {type(e).__name__}: {e}\n"); return name, False
    finally:
        try: sbx.kill()
        except Exception: pass
        log.close()


def run(jobs_file, out_dir):
    jobs = json.loads(Path(jobs_file).read_text()); out = Path(out_dir); out.mkdir(parents=True, exist_ok=True)
    print(f"{len(jobs)} jobs on template {ALIAS}", flush=True)
    with ThreadPoolExecutor(max_workers=len(jobs)) as ex:
        for name, ok in ex.map(lambda j: run_job(j, out), jobs):
            print(name, "ok" if ok else "FAILED", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "build": build()
    elif sys.argv[1] == "run": run(sys.argv[2], sys.argv[3])
    else: raise SystemExit(__doc__)
