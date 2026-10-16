# sweep: many configurations, each ending as a kernel-checked statement

The repository checks one network. This directory turns that into a runner for any
configuration (prime p, hidden size H, seed, training fraction, weight decay, steps) and a
Modal app that runs a grid of such points, so that every point ends as a statement Lean's
kernel accepted: either "right on every pair" or "wrong on exactly these k pairs".

Written 2026-10-16 against repo commit `ac031c42ac73df2ea132ac81759e6a9ab1abd38f`, toolchain
`leanprover/lean4:v4.35.0-rc2`, Lean core only, no Mathlib.

## Files

| File | What it does |
| --- | --- |
| `run_one.py` | `python3 sweep/run_one.py P H SEED FRAC WD STEPS OUTDIR`: trains (the repo's `train.py`), builds the circle-only network (the repo's `circle_only.py`), generates a fresh Lean package, runs `lake build`, replays every module with `lake env leanchecker`, prints the axioms, writes `OUTDIR/result.json`. Exit code non-zero on any failure |
| `WrongSet.lean` | Small lemmas, copied into every generated package: `rowsToPairs` with `mem_rowsToPairs`, `iff_not_mem_of_beq`, which turn the Boolean fact the kernel decides for a row into the statement about the network, and `strictLex` with `nodup_of_strictLex`, which make the length of the wrong list a count of distinct inputs |
| `circle_rescale.py` | The circle-only construction with all three tables scaled by one factor before rounding; used only when `circle_only.py`'s output cannot go through the fast evaluator (see below) |
| `negative_control.py` | Removes one pair from a generated wrong list and checks that the kernel rejects the package |
| `modal_sweep.py` | The Modal app: one container per grid point, calling `run_one.py`. Not run here (no token) |
| `make_grid.py`, `grid.json` | The first sweep (126 points) and its cost estimate |
| `summarise.py` | Collects every `result.json` under a directory into a markdown table and a CSV |

## What the generated Lean package states

For each of the two networks (`Trained`, `CircleOnly`) the package holds, in the namespace
`LeanCheckedNetwork.Sweep.<tag>.<network>` where `<tag>` encodes the configuration
(for example `P7_H8_S0_F0p7_WD1_ST200`):

- `E1`, `E2`, `W2`, `answer`: the frozen integer network, as in the repo's `Weights.lean`.
- `wrongRows : List (List Nat)`: row `a` lists every `b` with `answer a b ≠ (a + b) % p`.
- `wrongPairs : List (Nat × Nat)`: the same pairs as one explicit list.
- `table_ok`: `tableOk W2 H = true` (every read-out entry in [-128, 127]), by `decide +kernel`.
- `wrongPairs_eq : wrongPairs = rowsToPairs wrongRows 0` and `wrongPairs_length : wrongPairs.length = k`, by `decide +kernel`.
- `wrongPairs_strictLex : strictLex wrongPairs = true` (the list is strictly increasing in
  lexicographic order, one pass) and `wrongPairs_in_range` (both entries of every listed pair
  are below p), by `decide +kernel`; `wrongPairs_nodup : wrongPairs.Nodup` follows from the
  first through `nodup_of_strictLex` in `WrongSet.lean`. Added in review on 2026-10-16: without
  them the kernel accepted a list with an extra pair `(0, 999)` or with `(1, 0)` listed twice
  and `wrongPairs_length = 13` for a network wrong on 12 inputs, so "exactly k" was not forced.
- `fast_a`, one per row, by `decide +kernel`: for every `b < p`, the fast evaluator's checks
  pass and `(fastAnswer ... == (a + b) % p) == !(wrongRows.getD a []).contains b`. This is
  the same fast path as the repo's `gen_lean.py`, with the row's wrong list as the expected
  pattern instead of `true` everywhere.
- `row_a`: `answer a b = (a + b) % p ↔ b ∉ wrongRows.getD a []`, from `fast_a` through
  `answer_eq_fastAnswer` (the repo's proof that the fast path equals the network) and
  `iff_not_mem_of_beq`.
- `answer_iff_not_wrong : ∀ a < p, ∀ b < p, (answer a b = (a + b) % p ↔ (a, b) ∉ wrongPairs)`:
  the main theorem, for every network, right or wrong.
- `adds_mod_p : ∀ a < p, ∀ b < p, answer a b = (a + b) % p`: only when the list is empty, as a
  corollary. This is the repo's theorem.

A network that is wrong on k pairs therefore gets the kernel-checked statement "wrong on
exactly these k pairs" rather than a failed build. The conventions of `gen_lean.py` are kept:
`set_option maxRecDepth 100000` in the weights file, `set_option Elab.async false` in the row
files, `.ofNat` / `.negSucc` literals, `decide +kernel` per row, no `native_decide`.

`run_one.py` passes a configuration only if all of these hold: `lake build` completed with no
`sorry` warning; `lake env leanchecker` exited 0 on every generated module (Network, Fast,
WrongSet, and Weights, Table, every Rows file and AllInputs for both networks); `#print axioms`
of every main theorem listed a subset of `[propext, Classical.choice, Quot.sound]`; and a scan
of every `.lean` file in the package found none of `sorry`, `native_decide`, `axiom`, `opaque`,
`implemented_by`, `extern`, `skipKernelTC`. The verdict in `result.json` is derived from those
outputs only. The runner never writes a verdict it did not get from the kernel: if any stage
fails, `kernel.<network>.status` is `fail` with the reason, and the exit code is 1.

In every run here the axioms line was exactly `[propext, Classical.choice, Quot.sound]`. The
check accepts a subset of these three because a proof that uses fewer axioms is not weaker;
`result.json` records the exact line.

## The circle-only weight range

`circle_only.py` rounds each wave without rescaling, so its entries can exceed 127 (the repo's
own circle-only network reaches 130). The fast evaluator needs two things:
`tableOk` (every `W2` entry in [-128, 127], checked once) and `fastOk` per input
(`255 * sum(hidden) < 2^32`, which with entries up to 127 holds for H <= 261). The embedding
tables are not bounded by `tableOk`, only through `fastOk`. So `run_one.py` evaluates
`circle_only.py`'s output in numpy and:

- if `W2` is in range and the digit bound holds for every pair, the tables are used as written
  (in the p=7 test the circle-only network had an embedding entry of 140 and still went through,
  because only `W2` is bounded);
- otherwise it calls `circle_rescale.py`, which recomputes the same waves and multiplies all
  three tables by `127 / (largest unrounded entry over the three tables)` before rounding.
  `result.json` records `rescaled: true`, the factor, and the numpy numbers of both the
  as-written and the rescaled network. The kernel-checked circle-only network is then the
  rescaled one, which is a different network from the one `circle_only.py` wrote (the score of
  every pair is multiplied by about the cube of the factor before rounding, so the answers can
  differ in rare near-tie cases; the result records both wrong counts).

## result.json

`config` (p, H, seed, frac, wd, steps, lr, chunks, Lean namespace); `networks.trained` and
`networks.circle_only` (numpy: wrong count, wrong pairs (first 2,000), ties, smallest winning
gap, largest weight, whether `W2` is in range and the digit bound holds; for circle-only also
the as-written numbers, `rescaled` and the factor); `kernel.trained` and `kernel.circle_only`
(`pass`/`fail`, the statement the kernel accepted, or why not); `stages.axioms.lines`;
`stages.replay` (exit code and seconds per module); `stages.scan`; `seconds` per stage;
`lean_version`, `lean_toolchain`, `repo_commit`; `failures`; `ok`.

## Tests run here (2026-10-16, 4 cores, with three other numpy training jobs and, later, the main
session's own Lean build sharing the machine)

Outputs are in `tests/` (`right_p7.out`, `wrong_p7.out`, `negative_control_p7.out`,
`cal_p31_h64.out`, `cal_p61_h128.out`, `manywrong_p31.out`, `summary.md`, `summary.csv`); the
generated packages themselves are not kept in the repository.

1. Right everywhere: `run_one.py 7 8 0 1.0 1.0 3000` (trained on all 49 pairs; at p=7 no
   fraction below 1.0 generalised in the trials, so this is memorisation, which is fine for
   exercising the path). Both networks: `right on all 49 pairs (...adds_mod_7)`, replay 23 of 23
   modules, axioms `[propext, Classical.choice, Quot.sound]` for all four theorems, exit 0,
   28 s.
2. Wrong by design: `run_one.py 7 8 0 0.7 1.0 200`. Trained network wrong on 12 of 49, circle-only
   (rescaled by 0.9766, `W2` as written reached 130) wrong on 13 of 49. Both:
   `wrong on exactly k of 49 pairs (...answer_iff_not_wrong, wrongPairs_length)`, replay 23 of
   23, standard axioms, exit 0, 27 s.
3. Negative control: `negative_control.py tests/wrong_p7 Trained` removed `(1, 0)` from
   `wrongRows` and `wrongPairs` and lowered the stated length to 11. `lake build` exit 1, at
   `Trained/Rows01.lean:14:2` (the `decide +kernel` of `fast_1`): "Tactic `decide` proved that
   the proposition ... is false". In the toolchain source
   (`src/lean/Lean/Elab/Tactic/Decide.lean`, `doKernel`) a `+kernel` proof is produced only by
   `mkAuxLemma`, which the kernel checks; that message is printed in the `catch` branch after
   the kernel threw, with the elaborator re-reducing the proposition only to word the message.
   The script accepts that text or a raw `(kernel)` error, and verifies that the failing file
   holds `fast_1`.
4. Calibration, right everywhere at a real size: `run_one.py 31 64 0 0.5 1.0 2000`: both networks
   right on all 961 pairs, 41 of 41 modules replayed, build 49.6 s, replay 86.4 s (2 at a
   time), total 138 s. The circle-only network was rescaled (factor 0.9435; as written its
   largest entry was 135).
5. Calibration at p=61, H=128 (`run_one.py 61 128 0 0.5 1.0 2000`): both networks right on all
   3,721 pairs (`adds_mod_61`), 41 of 41 modules replayed, standard axioms, exit 0. Build 569 s
   wall and replay 578 s wall (2 at a time) while the main session's own p=113 build and three
   training jobs shared the 4 cores (load average 5 to 8). The per-file build times in
   `build.log` sum to 2,117 s against the cost model's 1,406 core-seconds for the two networks;
   with the machine about twice oversubscribed those agree to the precision available here.
   The circle-only network needed no rescaling (largest entry 127).
6. A badly wrong network with a long wrong list: `run_one.py 31 64 0 0.3 0.0 2000` (fraction
   0.3, no weight decay). Trained network wrong on 666 of 961 pairs, circle-only wrong on 59 of
   961; the kernel accepted `wrong on exactly 666` and `wrong on exactly 59`
   (`answer_iff_not_wrong`, `wrongPairs_length`), 41 of 41 modules replayed, standard axioms,
   exit 0, build 101 s, replay 100 s. One run, not a finding, but worth watching in the sweep:
   the circle-only reduction of a network that has not generalised was far less wrong than
   the network itself.

## The grid (grid.json, 130 points, five blocks)

Chosen on 2026-10-16 from the literature so that the sweep crosses the boundary where
generalisation stops, rather than sitting above it. The only published fraction x weight-decay
map for this exact architecture is Doshi, Das, He and Gromov, *To grok or not to grok* (ICLR
2024), at p = 97: generalisation begins between about 0.23 and 0.33 of the pairs depending on
weight decay, and at very large decay the weight norms collapse and accuracy with them. Gromov
(2023) finds that AdamW with long training pushes the boundary to about 0.15 to 0.18, and that
width above about 50 does not move it at p = 97. Nanda et al. (2023) report that a transformer
at p = 113 groks at 0.3 and not at 0.2, and that p = 53 needs weight decay 5 where 1 fails.
Varma et al. (2023) find grokking between 12 and 16 percent of the pairs only after about 1e7
epochs. Weight-decay values do not transfer between papers (mean-field against standard
parametrisation, squared error against cross-entropy, coupled against decoupled decay); only
their order does. `train.py` is cross-entropy with decoupled decay in standard parametrisation,
learning rate 0.01, 20,000 full-batch steps unless stated.

| Block | Points | What it asks |
| --- | --- | --- |
| A, main plane | 96 | p = 97, H = 128, fraction in {0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.50, 0.70} x weight decay in {0, 0.1, 1, 3} x 3 seeds (the seed sets both the initialisation and the training split). Where does "right on every pair" start, for the frozen network and for its circle-only reduction, and how does the boundary move with decay |
| B, width | 15 | p = 97, fraction 0.3, decay 1, H in {24, 48, 96, 192, 256} x 3 seeds. 48 is one neuron per frequency, 96 is p - 1; 256 is the largest width the fast evaluator's digit bound allows (H <= 261), so Morwani et al.'s 4(p - 1) = 384 is out of reach without a change to `Fast.lean` |
| C, other primes | 9 | fraction 0.3, H = 128: p = 113 at decay 1 (3 seeds); p = 53 at decay 1 and 5 (3 seeds each) |
| D, collapse probe | 4 | p = 97, fraction 0.5, H = 128, decay 10 and 20, 2 seeds: the regime where integer freezing is expected to fail first, because tiny weights lose resolution under a scale of 127 |
| E, long tail | 6 | p = 97, H = 128, decay 1, fraction in {0.10, 0.125, 0.15}, 200,000 steps, 2 seeds |

Every point records, besides the two kernel verdicts, the numpy wrong count, the smallest
winning margin, the largest weight per table and the circle-only rescale factor, so the
phase diagram can be drawn from `summarise.py`'s CSV. Nobody has published what integer
rounding does to a grokked network, so every point is new data as well as a theorem.

Estimated cost (`make_grid.py` writes the per-point estimate into `grid.json`, same cost model
as before: 1.01e-3 core-seconds per unit of p^2 (H + p) per network from the repository's own
26-minute figure, replay 0.8x the build, training 7.3e-8 s per step x training pair x neuron
on one thread): 94 container wall-hours, 377 billed core-hours (a container pays for the 4
cores it requests even while training on one thread), about $30 at Modal's prices read on
2026-10-16 ($0.0000131 per physical core per second, $0.00000222 per GiB of memory per second,
4 cores and 16 GiB requested; the Starter plan carries $30 of free credit per month). Block A
is $22 of that; the largest single point (H = 256) is estimated at 1.5 hours wall. These are
estimates from one calibration point; the local timings were taken on a shared machine and are
upper bounds rather than a second calibration.

## Running on Modal (not run here)

There is no Modal token in this container, so `modal_sweep.py` was never executed; it was
written against the documentation pages listed at its top (modal.com/docs/guide/images,
volumes, resources, scale, apps, retries, timeouts, and docs/reference/modal.Retries, read
2026-10-16) and only syntax-checked. Everything with logic is in `run_one.py`, which was run
here; the Modal file installs elan with the pinned toolchain at image build, copies the repo
into the image, calls `run_one.py` with the same arguments, and copies `OUTDIR` (without
`.lake`) to a Volume. From a machine with a token, in the repo root:

```bash
pip install modal && modal setup
modal run sweep/modal_sweep.py --grid sweep/grid.json          # add --limit 3 for a trial
modal volume get lean-checked-network-sweep / sweep-results
python3 sweep/summarise.py sweep-results
```

Function settings: `cpu=4.0`, `memory=(16384, 24576)` MiB, `timeout=4 * 3600`,
`retries=modal.Retries(max_retries=2, initial_delay=10.0, backoff_coefficient=2.0)`. Points
that already have a `result.json` on the Volume are skipped unless `--force` is given.

Things that could go wrong on the first real run and were not testable here: the
`add_local_dir` ignore patterns, memory at H=256 (two leanchecker processes at once; raise the
limit if a container is killed), and the numpy pin (2.5.3, the version used here; a different
numpy or BLAS can change the trained weights slightly, which changes which pairs are wrong,
but every point is checked by the kernel as it comes out, so the statement stays true of the
network that was actually produced).

## What is not done

- The planted-fault file of the repo (`expected_fail/FaultRow.lean`) is not regenerated per
  point; the negative control here plays that role for the wrong-set theorem.
- `nanoda` or another second checker is not run; only `leanchecker`.
- Prime Intellect: nothing here targets it; the same `run_one.py` would run on any Linux box
  with elan and numpy.
