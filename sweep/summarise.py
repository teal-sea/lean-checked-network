"""Collect every result.json under a directory into a markdown table and a CSV.

Usage: python3 summarise.py RESULTS_DIR [--md OUT.md] [--csv OUT.csv]

The CSV has one row per configuration with, for each network, the numpy wrong count and the
kernel verdict, so a phase diagram over training fraction x weight decay can be drawn from it
(columns trained_right / circle_right are 1 only when the kernel checked "right on every pair").
"""
import argparse
import csv
import json
from pathlib import Path

COLS = ["p", "H", "seed", "frac", "wd", "steps", "trained_wrong", "trained_gap", "trained_kernel", "trained_right",
        "circle_wrong", "circle_largest_weight", "circle_rescaled", "circle_rescale_factor", "circle_kernel", "circle_right",
        "axioms_standard", "replay_ok", "replay_of", "seconds_train", "seconds_build", "seconds_replay", "seconds_total",
        "lean_toolchain", "repo_commit", "failures", "path"]


def row_of(path):
    r = json.loads(Path(path).read_text())
    c = r.get("config", {})
    nets = r.get("networks", {})
    tr, ci = nets.get("trained", {}), nets.get("circle_only", {})
    kern = r.get("kernel", {})
    ax = r.get("stages", {}).get("axioms", {}).get("parsed", {})
    std = {"propext", "Classical.choice", "Quot.sound"}
    axioms_ok = bool(ax) and all(set(v) <= std for k, v in ax.items() if not k.startswith("_"))
    rep = r.get("stages", {}).get("replay", {})
    def verdict(key):
        k = kern.get(key, {})
        if k.get("status") == "pass":
            return "right_everywhere" if k.get("wrong_count") == 0 else f"wrong_on_{k.get('wrong_count')}"
        return "no_verdict"
    return {
        "p": c.get("p"), "H": c.get("H"), "seed": c.get("seed"), "frac": c.get("frac"), "wd": c.get("wd"), "steps": c.get("steps"),
        "trained_wrong": tr.get("wrong_count"), "trained_gap": tr.get("smallest_winning_gap"),
        "trained_kernel": verdict("trained"), "trained_right": int(verdict("trained") == "right_everywhere"),
        "circle_wrong": ci.get("wrong_count"), "circle_largest_weight": ci.get("largest_weight"),
        "circle_rescaled": int(bool(ci.get("rescaled"))), "circle_rescale_factor": ci.get("rescale_factor"),
        "circle_kernel": verdict("circle_only"), "circle_right": int(verdict("circle_only") == "right_everywhere"),
        "axioms_standard": int(axioms_ok), "replay_ok": rep.get("ok"), "replay_of": rep.get("of"),
        "seconds_train": r.get("seconds", {}).get("train"), "seconds_build": r.get("seconds", {}).get("build"),
        "seconds_replay": r.get("seconds", {}).get("replay"), "seconds_total": r.get("seconds", {}).get("total"),
        "lean_toolchain": r.get("lean_toolchain"), "repo_commit": (r.get("repo_commit") or "")[:12],
        "failures": "; ".join(f"[{f['stage']}] {f['why'][:80]}" for f in r.get("failures", [])),
        "path": str(path),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results_dir")
    ap.add_argument("--md", default=None)
    ap.add_argument("--csv", default=None)
    a = ap.parse_args()
    root = Path(a.results_dir)
    rows = sorted((row_of(p) for p in root.rglob("result.json")),
                  key=lambda r: (r["p"] or 0, r["H"] or 0, r["frac"] or 0, r["wd"] or 0, r["seed"] or 0))
    md = root / "summary.md" if a.md is None else Path(a.md)
    cs = root / "summary.csv" if a.csv is None else Path(a.csv)
    with open(cs, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLS)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    show = ["p", "H", "seed", "frac", "wd", "steps", "trained_wrong", "trained_kernel", "circle_wrong", "circle_rescaled",
            "circle_kernel", "axioms_standard", "replay_ok", "replay_of", "seconds_total"]
    lines = [f"# Sweep summary: {len(rows)} configurations", "",
             "trained_kernel / circle_kernel: what Lean's kernel checked (right_everywhere, wrong_on_k, or no_verdict when a stage failed).",
             "", "| " + " | ".join(show) + " |", "|" + "---|" * len(show)]
    for r in rows:
        lines.append("| " + " | ".join("" if r[k] is None else str(r[k]) for k in show) + " |")
    # the phase table: fraction x weight decay, counts of right-everywhere verdicts per cell
    cells = {}
    for r in rows:
        key = (r["frac"], r["wd"])
        c = cells.setdefault(key, {"n": 0, "trained": 0, "circle": 0, "verdicts": 0})
        c["n"] += 1
        c["trained"] += r["trained_right"]
        c["circle"] += r["circle_right"]
        c["verdicts"] += int(r["trained_kernel"] != "no_verdict")
    fracs = sorted({k[0] for k in cells if k[0] is not None})
    wds = sorted({k[1] for k in cells if k[1] is not None})
    if fracs and wds:
        lines += ["", "## Phase table: right-everywhere verdicts (trained / circle-only) over kernel verdicts, per fraction x weight decay", "",
                  "| frac \\ wd | " + " | ".join(str(w) for w in wds) + " |", "|" + "---|" * (len(wds) + 1)]
        for fr in fracs:
            cells_row = []
            for wd in wds:
                c = cells.get((fr, wd))
                cells_row.append("" if c is None else f"{c['trained']} / {c['circle']} of {c['verdicts']}")
            lines.append(f"| {fr} | " + " | ".join(cells_row) + " |")
    md.write_text("\n".join(lines) + "\n")
    print(f"{len(rows)} results -> {md} and {cs}")
    for l in lines[4:]:
        print(l)


if __name__ == "__main__":
    main()
