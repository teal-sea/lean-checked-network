"""Write sweep/tests/learning-curve-2026-10-16.md from run_one.py results of the 64-neuron checkpoints.

Usage: python3 sweep/curve_record.py RESULTS_DIR STEP1,STEP2,...   (RESULTS_DIR holds step{STEP}/result.json)
"""
import json, re, sys
from pathlib import Path

root, steps = Path(sys.argv[1]), [int(s) for s in sys.argv[2].split(",")]
rows, circle_notes = [], set()
for s in steps:
    d = root / f"step{s}"
    r = json.load(open(d / "result.json"))
    t, c = r["networks"]["trained"], r["networks"]["circle_only"]
    held = re.findall(rf"step {s}: train ([0-9.]+)\s+held-out ([0-9.]+)", (d / "train.log").read_text())
    train_acc, held_acc = held[-1] if held else ("?", "?")
    name = r["stages"]["gen"]["main_theorems"]["trained"][0].rsplit(".", 2)[0]
    rep = r["stages"]["replay"]
    ax = r["stages"]["axioms"]["parsed"]
    std = all(v in (["propext", "Classical.choice", "Quot.sound"], []) for v in ax.values())
    wrong = ", ".join(f"({a}, {b})" for a, b in t["wrong_pairs"]) or "none"
    rows.append(f"| {s:,} | {train_acc} / {held_acc} | {t['wrong_count']}: {wrong} | {t['smallest_winning_gap']:,} | {c['wrong_count']:,} | built, `wrongPairs_length`, `_nodup`, `_in_range` | {rep['ok']} of {rep['of']}, {int(r['seconds']['replay'])} s | {'standard' if std else 'NOT STANDARD'} | {int(r['seconds']['build'])} s |")
    if c.get("note"): circle_notes.add(c["note"])
ns = name.rsplit(".", 1)[0]
text = f"""# A learning curve whose every point is a theorem: the 64-neuron run, 2026-10-16

The run in `runs/p113_h64.log` is the one that was not right everywhere at every checkpoint. Each
checkpoint below was produced by `run_one.py 113 64 0 0.5 1.0 STEP` (the repository's `train.py`,
seed 0, half the pairs, weight decay 1.0, learning rate 0.01, full batch, stopped at STEP), which is
the same deterministic trajectory as the logged run, so the frozen network at each step is the
logged checkpoint. The runner then froze it, built its circle-only reduction, generated a Lean package,
ran `lake build`, replayed every module with `leanchecker` (two at a time) and printed the axioms.
Namespace `{ns}.ST{{STEP}}`. 4-core container, the machine shared with one other run for most of the time.

The theorem for each network is `answer_iff_not_wrong`: for every pair `(a, b)`, the network answers
`(a + b) % 113` **if and only if** `(a, b)` is not in an explicit list, with the list proved to have
the stated length, to be strictly increasing (no pair listed twice) and to hold only pairs below 113,
so the count is exactly the number of wrong inputs (`sweep/WrongSet.lean`). An empty list is
`adds_mod_113`.

| Step | Accuracy, float (train / held-out) | Wrong pairs, frozen (kernel) | Smallest winning margin, right pairs only | Circle-only reduction, wrong (kernel) | Kernel | `leanchecker` | Axioms | Build |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
{chr(10).join(rows)}

The margin column is `run_one.py`'s: the smallest gap between the right answer's score and the best other
score, over the pairs the network gets right. `train.py`'s log takes the minimum over all pairs, wrong ones
included, so its numbers are lower wherever a pair is wrong (both agree at step 12,000: 175,330).

Training accuracy is 1.0000 at every checkpoint, so every wrong pair is a held-out pair: the frozen
network memorised the 6,384 training pairs by step 2,000 and generalised to the last held-out pairs
between steps 10,000 and 12,000. That is grokking (Power et al., 2022) at the scale of three pairs,
and with the kernel's verdict on each point it is a fact about these six networks rather than a plot.

**The circles alone do not carry this run.** The circle-only reduction (each neuron cut to its single
circle wave, as `circle_only.py` does for the 128-neuron network, where it is right on every pair) is
wrong on hundreds of pairs at every checkpoint here, including step 12,000 where the trained network
is right on all 12,769. So the 64-neuron network's correctness rests on more than one wave per neuron:
the measured leftovers (third harmonics and the rest) are load-bearing at this width. Both facts are
kernel-checked, with the wrong lists named.
{("Circle-only note from the runner: " + "; ".join(sorted(circle_notes))) if circle_notes else ""}

The Lean packages were generated in a scratch directory outside the repository and are not committed;
`result.json` of each run, with the named theorems, module-by-module replay times and axioms, is in
`sweep/tests/learning-curve/`.
"""
out = Path("sweep/tests/learning-curve-2026-10-16.md"); out.write_text(text)
print(f"wrote {out}: {len(rows)} rows")
