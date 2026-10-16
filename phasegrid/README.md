# The phase-grid network adds mod p: derivation checked, theorem proved, instances kernel-checked

Written 2026-10-16. This directory turns a derivation written the same day in the author's private notes (Gromov's
analytic weights with the phases fixed on a grid, so that the unwanted waves cancel exactly) into
mathematics the Lean kernel accepts, in three stages. Nothing elsewhere in this repository changed.

| Stage | Directory | What it is | Status |
| --- | --- | --- | --- |
| 1 | `stage1/`, `logs/stage1_*.log` | the derivation checked adversarially in Python | measured; one miscount and one restriction in the proposal found, the bound confirmed and found loose |
| 2 | `mathlib/` (Lake project on Mathlib) | the general theorem, proved: for every modulus, every frequency set with a positive gap, every scale above the bound, the rounded phase-grid network adds mod p; plus a version for any tables within 1/2 of the analytic weights, and the p = 7 tables of stage 3 proved right by that theorem with certified cosines | proved, replayed by `leanchecker`, standard axioms |
| 3 | `instances/` (Lake project, core Lean only) | three explicit integer networks kernel-checked by the first repository's own route | all three kernel-checked and replayed by `leanchecker`, standard axioms; three planted faults rejected, two of them wrong only at the last pair of a row |

Versions: stage 2 uses `leanprover/lean4:v4.35.0` with Mathlib tag `v4.35.0` (commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`; `git ls-remote --tags` on 2026-10-16 lists `v4.35.0` and its release candidates as Mathlib's newest tags, so this is the latest stable Lean release Mathlib supports), oleans from `lake exe cache get` (9031 files from the Mathlib cache, nothing compiled from source); stage 3 uses
`leanprover/lean4:v4.35.0-rc2`, the first repository's toolchain. Python 3.13.16, numpy 2.5.3.

## Stage 1: the derivation, checked

**The score of one neuron has nine waves, not eight.** For a neuron at frequency k with phases
(phi1, phi2), `W2[c] (E1[a] + E2[b])^2` expands into nine cosines: the wanted wave
`(1/2) cos(ta + tb - tc)` and eight others carrying a phase `alpha phi1 + beta phi2` with
(alpha, beta) in {(1,1), (3,1), (1,-1), (1,3), (-1,1), (2,2), (2,0), (0,-2)}. The proposal lists
exactly these eight unwanted pairs but says "eight families ... the other seven". Over the grid
phi1 in {0, pi/2, pi, 3pi/2}, phi2 in {0, pi/2}, every family with alpha not a multiple of 4 sums to
zero (the four values of e^{i alpha phi1} cancel), and (0, -2) is killed by the two values of
e^{-2i phi2}. What survives is `4 cos(ta + tb - tc)` per frequency, as the proposal says
(`families.py`: Claim A max deviation 1.03e-14 over 20,000 random angle tuples; Claim B each family's
grid sum at most 6.2e-15; Claim C, the same identity as a polynomial in cos and sin of the three
angles, holds exactly at 2,000 random rational points). The exact statement is `octet` in stage 2.

**The rounding bound.** With `w' = round(M w)`, `x = round(M e1) + round(M e2)` and `X = M e1 + M e2`,

    w' x^2 - M w X^2 = (w' - M w) x^2 + M w (x - X)(x + X),

and `|w' - M w| <= 1/2`, `|x| <= 2M` (an integer within 1/2 of a number of size at most M), `|x - X| <= 1`,
`|x + X| <= 4M`, `|M w| <= M` give at most `(1/2)(2M)^2 + M (4M) = 6 M^2` per neuron. A score has 8|S|
neurons, so it is within `48 M^2 |S|` of `M^3` times the real score; the real score is `4|S|` at the
right answer and at most `4(|S| - g(S))` at any wrong one, so the integer gap is at least
`4 g M^3 - 96 |S| M^2 = 4 M^2 (M g - 24 |S|)`, positive when `M > 24 |S| / g(S)`. **The proposal's bound
is correct as a sufficient condition** (its "about 6M^2" per neuron is exactly 6M^2) and **proved in
stage 2**. It is loose in practice: the full frequency set adds mod p already at M = 1 for every odd
p tested and M = 2 at p = 12, where the bound asks for 24 or 25; Nanda's five frequencies at p = 113
work from M = 2 (bound 49.8); the smallest-gap set {1} at p = 113 works from M = 6 with ties and
wrong answers below that (bound 15,530). No counterexample to the bound was found in any case.

**What the theorem needs of p.** Nothing: `adds_mod_p` holds for every `p >= 1` (the gap hypothesis
does the work; p = 12 was tested and is covered by `adds_mod_p_full`). For the full frequency set the
proposal's "g = p/2" holds for odd p; for even p = 2m the set is {1, ..., m-1}, the wave sum at a
nonzero shift is `(-1 - cos(pi s))/2 <= 0`, so g = |S| = m - 1 and the bound is exactly 24, which is
why M >= 25 (not 24) is needed there. Frequencies with k = 0 mod p make the gap non-positive and are
excluded by the hypothesis, not by any primality.

**Measured (`rounding2.py`, this session; exact integer scores, first-index argmax as in
`Network.lean`).** M just above and just below the bound B = 24|S|/g, with the smallest winning margin:

| p | S | g(S) | B | M above B: wrong, ties, margin | M below B: wrong, ties, margin | scan: smallest M with no wrong answer and no tie |
| --- | --- | --- | --- | --- | --- | --- |
| 7 | all (1..3) | 3.5 | 20.6 | 21: 0, 0, 122,456 | 20: 0, 0, 105,000 | 1 |
| 7 | {1} | 0.377 | 63.7 | 64: 0, 0, 379,744 | 63: 0, 0, 361,368 | 3 (M = 1, 2 fail) |
| 11 | all (1..5) | 5.5 | 21.8 | 22: 0, 0, 232,256 | 21: 0, 0, 202,116 | 1 |
| 11 | {1} | 0.159 | 151.2 | 152: 0, 0, 2,148,672 | 151: 0, 0, 2,096,844 | 6 |
| 12 | all (1..5) | 5 | 24 | 25: 0, 0, 306,825 | 24: 0, 0, 276,480 | 2 |
| 12 | {1} | 0.134 | 179.1 | 180: 0, 0, 3,110,400 | 179: 0, 0, 2,958,890 | 6 |
| 97 | all (1..48) | 48.5 | 23.75 | 24: 0, 0, 2,662,896 | 23: 0, 0, 2,342,140 | 1 |
| 97 | {1,2,3} | 0.0293 | 2,457 | 2,458: 0, 0, 1,692,206,060 | 2,457: 0, 0, 1,707,530,952 | none in 1..30 |
| 97 | {1} | 0.0021 | 11,444 | 11,444: 0, 0, 12,000,045,408 | 11,443: 0, 0, 11,978,300,736 | none in 1..30 |
| 113 | all (1..56) | 56.5 | 23.79 | 24: 0, 0, 3,106,708 | 23: 0, 0, 2,731,756 | 1 |
| 113 | Nanda's {14,35,41,42,52} | 2.41 | 49.8 | 50: 0, 0, 1,164,292 | 49: 0, 0, 1,093,636 | 2 |
| 113 | {1,2,3} | 0.0216 | 3,333 | 3,333: 0, 0, 3,121,601,880 | 3,332: 0, 0, 3,131,283,620 | none in 1..30 |
| 113 | {1} | 0.00155 | 15,530 | 15,530: 0, 0, 22,137,073,568 | 15,529: 0, 0, 22,091,362,924 | none in 1..30 |
| 257 | all (1..128) | 128.5 | 23.9 | 24: 0, 0, 7,078,608 | 23: 0, 0, 6,238,752 | 1 |
| 257 | {1,2,3} | 0.00418 | 17,215 | 17,215: 0, 0, 82,996,874,604 | 17,214: 0, 0, 83,061,658,416 | none in 1..30 |
| 257 | {1} | 0.000299 | 80,310 | 80,310: 0, 0, 592,652,355,840 | 80,309: 0, 0, 592,668,925,712 | none in 1..30 |
| 1009 | all (1..504), 4032 neurons | 504.5 | 23.98 | 24: 0, 0, 27,808,980 | 23: 0, 0, 24,439,808 | not scanned (M = 25: 0 wrong, margin 31,410,432) |
| 1009 | {1,2,3} | 0.000271 | 265,258 | 265,258: 0, 0, 19,702,433,836,000 | 265,257: 0, 0, 19,599,058,044,408 | none in 1..30 |
| 1009 | {1} (12 of 1009 rows, exact integers) | 0.0000194 | 1,237,843 | 1,237,843: 0, 0, 140,254,949,975,992 | 1,237,842: 0, 0, 139,918,439,661,576 | none in 1..30 |

The random sets of 3 and 5 frequencies at each modulus are in the logs (all pass above and below the
bound; smallest passing M from 2 to 9). Below the bound nothing fails in any case tested, which is
what a loose sufficient bound looks like; the failures appear only at M an order of magnitude or more
below it. "Just below" is not a counterexample to anything: the bound is one-sided.

**Corrections to the proposal, in one place.** (1) Nine wave families per neuron, one wanted and eight
unwanted, not "eight ... the other seven". (2) "g = p/2 for all frequencies" holds for odd p only; for
even p the gap is |S| and that is where M >= 25 comes from (odd p needs only M >= 24, proved). (3) The
bound is right, with the per-neuron error exactly 6M^2 rather than "about"; it is loose by a factor
of roughly 10 to 25 on every set tested.

## Stage 2: the theorem, in Lean 4 with Mathlib

Lake project `mathlib/` (`lakefile.toml` requires `mathlib` at `v4.35.0`; `lake exe cache get`
fetched the oleans, nothing compiled from source). `PhaseGrid/Network.lean` is the first repository's
`Network.lean` byte for byte (`diff` in `verify2.sh`), so `answer` is the repository's definition.

Definitions (`Defs.lean`): `neurons S` lists `(k, j, l)` for `k` in `S` and the eight phase pairs;
`rE1 p a (k,j,l) = cos(2πka/p + jπ/2)`, `rE2`, `rW2` likewise; `E1 p S M` is the `List (List ℤ)` whose
row `a` is `round (M · rE1 p a n)` over the neurons (`round x = ⌊x + 1/2⌋`), `E2`, `W2` likewise;
`answer p S M a b := LeanCheckedNetwork.answer (E1 p S M) (E2 p S M) (W2 p S M) a b`;
`waveSum p S s = Σ_{k∈S} cos(2πks/p)`; `gap p S = |S| − max_{0<s<p} waveSum`.

Proved (kernel-accepted; every theorem below prints `[propext, Classical.choice, Quot.sound]` or a
subset; every module replayed by `leanchecker`; `verify2.sh` scans the sources for `sorry`,
`native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, `skipKernelTC` and finds none):

| Name | Statement (one line) | File |
| --- | --- | --- |
| `octet` | for all real `ta tb tc`, the eight phase-grid terms `cos(tc + jπ/2 + lπ/2)(cos(ta + jπ/2) + cos(tb + lπ/2))²` sum to `4 cos(ta + tb − tc)` | `Trig.lean` |
| `realScore_eq` (i) | `realScore p S a b c = 4 · waveSum p S (a + b − c)` | `Score.lean` |
| `waveSum_right` (ii) | `waveSum p S (a + b − (a+b)%p) = |S|` for `0 < p` | `Score.lean` |
| `waveSum_wrong` (ii) | if every `0 < s < p` has `waveSum p S s ≤ |S| − g`, then for `c < p`, `c ≠ (a+b)%p`: `waveSum p S (a + b − c) ≤ |S| − g` | `Score.lean` |
| `abs_round_le`, `neuron_bound` (iii) | `|round(Me)| ≤ M`; one neuron's integer term is within `6M²` of `M³` times its real term | `Score.lean` |
| `intScore_close` (iii) | `|intScore − M³ · realScore| ≤ 48 M² |S|` | `Score.lean` |
| `intScore_lt` (iv) | with `24|S| < M g`: every wrong answer's integer score is strictly below the right one's | `Score.lean` |
| `adds_mod_p` (iv) | `0 < p`, `g` a gap for `S`, `24|S| < M g` ⟹ `∀ a < p, ∀ b < p, answer p S M a b = (a + b) % p` | `Score.lean` |
| `adds_mod_p_of_gap` | the same with `g = gap p S` | `Score.lean` |
| `sum_cos_range_eq_zero`, `sum_cos_half` | the p roots of unity sum to zero; for odd `p = 2m+1`, `Σ_{k=1}^{m} cos(2πks/p) = −1/2` at `0 < s < p` | `FullSet.lean` |
| `adds_mod_p_full_odd` | every odd `p = 2m+1 ≥ 3`, `S = [1..m]`, every `M ≥ 24`: adds mod p | `FullSet.lean` |
| `adds_mod_7_full`, `adds_mod_113_full` | the two instances as corollaries, `M ≥ 24` | `FullSet.lean` |
| `sum_cos_even_le`, `adds_mod_p_full_even` | even `p = 2m ≥ 4`, `S = [1..m−1]`, `M ≥ 25` | `FullSetEven.lean` |
| `adds_mod_p_full` | **every `p ≥ 3`, `S = [1..⌊(p−1)/2⌋]`, every `M ≥ 25`: adds mod p** (the proposal's headline) | `FullSetEven.lean` |
| `argmax_of_strict`, `answer_ofFn` | the repository's `argmax` returns the index of a strict maximum; `answer` on `List.ofFn` tables is the `argmax` of the list of scores | `ListLemmas.lean` |
| `abs_int_le_of_close`, `neuron_bound_close`, `intScoreT_close`, `intScoreT_lt` | the rounding lemmas for arbitrary integers within `1/2` of `M` times the real weights | `Close.lean` (new this session) |
| `adds_mod_p_tables` | **any integer tables whose in-range entries are within `1/2` of `M cos(…)`** make `LeanCheckedNetwork.answer` return `(a+b)%p`, under the same gap and scale hypotheses | `Close.lean` |
| `adds_mod_p_of_close_round` | `adds_mod_p` re-derived from `adds_mod_p_tables` | `Close.lean` |
| `cos_pi28`, `sin_pi28`, `double_bounds`, `bounds_pi14`, `bounds_pi7`, `bounds_2pi7`, `bounds_4pi7`, `C1..C3`, `S1..S3` | certified rational boxes for `cos` and `sin` at `2πr/7`, `r = 1, 2, 3` (width about `1e-5`), from `Real.cos_bound`, `Real.sin_bound` at `π/28`, `Real.pi_gt_d6`, `Real.pi_lt_d6` and three doublings | `P7Link.lean` (new this session, generated by `p7link/gen_p7link.py`) |
| `cos_theta_quarter` | `cos(2πkx/p + jπ/2)` depends only on `kx mod p` and `j mod 4` | `P7Link.lean` |
| `E1_close`, `E2_close`, `W2_close` | every entry of the stage 3 tables `P7FullTables` is within `1/2` of `25 cos(…)` (504 entries, one short proof each) | `P7Link.lean` |
| `P7FullTables.adds_mod_7_by_theorem` | **the stage 3 tables at p = 7 answer `(a+b)%7` on every pair, by the general theorem** (no enumeration of the 49 pairs); the same statement as stage 3's brute-force `PhaseGridInstances.P7Full.adds_mod_7` | `P7Link.lean` |

`mathlib/verify2.sh` (log `logs/stage2_verify_final.log`): `Build completed successfully (9059 jobs)`; source scan
`none found`; `Network.lean` `identical` to the repository's; `replayed 11 of 11 modules` (`PhaseGrid.Network`,
`ListLemmas`, `Trig`, `Defs`, `Score`, `FullSet`, `FullSetEven`, `P7FullTables`, `Close`, `P7Link`, `Open`, each
`OK`); every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]` except
`LeanCheckedNetwork.answer_ofFn`, `[propext, Quot.sound]`. The root module `PhaseGrid`, which only imports
the others, is not replayed on its own: `leanchecker` on it re-checks all modules in one process, which
needed more than 6.4 GB here and was OOM-killed (dmesg: `Killed process 13679 (leanchecker) ...
anon-rss:6464300kB`); the first repository's script leaves its root out for the same reason.
The three `_close` theorems take about 2 minutes each to elaborate (504 entry proofs in all; the whole
`P7Link.lean` 395 s, under a machine load of 6 to 9 on 4 cores); `set_option maxHeartbeats 2000000 in`
on those three declarations raises the elaboration budget only.

Open (`Open.lean`; no `sorry` anywhere). *Corrected 2026-10-16 by the second adversarial review: this
paragraph used to list `tablesMatchP7` as open, although `P7Link.lean` proves it (`E1_eq`, `E2_eq`, `W2_eq`,
`tablesMatchP7`, in the table above), and `tablesClose113` as a `def … : Prop`, although the first review
removed that `def` because, as written, it compared the stage 2 `round` table with the cosines it was
rounded from and was trivially true.* What is open: (1) the p = 113 tables of stage 3 (all 56 frequencies
at M = 25, Nanda's five at M = 30) are not proved to be within 1/2 of `M cos(…)`, so they are not linked to
the general theorem; stated in words in `Open.lean`, since those tables are not in this package; needs
`cos(2πr/113)` to about 3e-5 for 56 values of r, the method of `P7Link.lean` with more precision; their
proof is the brute-force kernel check of stage 3. (2) `fullSetWorksAtTwo` (`def … : Prop`): the loose
bound, M = 2 suffices for the full set at every odd p, measured at five moduli, not proved.

## Stage 3: explicit networks, kernel-checked, core Lean only

Lake project `instances/`, toolchain `leanprover/lean4:v4.35.0-rc2`, no
dependencies. `Network.lean` and `Fast.lean` are the first repository's files, unchanged except the
import line of `Fast.lean`. Route: `gen_phase_grid.py` writes the integer tables
(`round(M cos(…))`, half up, after checking in numpy with exact integer scores that the network is
right on every pair and that no weight is within 1e-9 of a half-integer), one `decide +kernel` per
row of the addition table through the packed evaluator, `answer_eq_fastAnswer` turns each into a
statement about `answer`, `adds_mod_p` assembles the rows; `check_instance.sh` builds, replays every
module with `leanchecker`, prints axioms.

| Instance | p | S | neurons | M | smallest margin (numpy) | theorem | build (wall) | replay | axioms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `P7Full` | 7 | 1, 2, 3 | 24 | 25 | 122,456 at M = 21; at M = 25: 219,400 | `PhaseGridInstances.P7Full.adds_mod_7` | 8.3 s fresh (row files 1.0 s and 1.4 s, load 8.3) | 7 of 7 OK, 7 s | `[propext, Classical.choice, Quot.sound]` |
| `P113Nanda5` | 113 | 14, 35, 41, 42, 52 | 40 | 30 | 245,012 | `PhaseGridInstances.P113Nanda5.adds_mod_113` | 1048 s (earlier session, 3 jobs, loaded machine) | 21 of 21 OK, 1176 s serial | `[propext, Classical.choice, Quot.sound]` |
| `P113Full` | 113 | 1..56 | 448 | 25 | 3,514,188 | `PhaseGridInstances.P113Full.adds_mod_113` | 8017 s wall (05:11:25Z to 07:25:02Z, two row files at a time, machine shared): `Weights` 114 s, `Table` 5.9 s, the 16 row files 860 to 1292 s each (15,668 s in all, mean 979 s), `AllInputs` 0.7 s | 21 of 21 OK (row files 604 to 858 s each, two at a time, overlapping the build; `logs/stage3_P113Full_replay_driver.log`, `instances/replay.P113Full.out`) | `[propext, Classical.choice, Quot.sound]` |

Two changes were needed for the 448-neuron instance, both in how the same proof is written, not in
what is proved: the tables are written as 113 row definitions per table (one 50,624-entry list
literal exhausted the elaborator's memory: Lean killed with exit code 137 after 369 s), and each row's
check is split into five `decide +kernel` calls over consecutive ranges of `b` (one call per row needed
4.3 to 5.8 GB and was OOM-killed when two ran at once; the kernel frees its caches between
declarations, and the split brought a row file to about 2.2 GB (poll of `/proc`, `logs/stage3_P113Full_rss.log`)). `--rowdefs` and `--bchunks 5` in
`gen_phase_grid.py`; the p = 7 and Nanda instances use the plain form.

**Planted fault.** `P7Fault` is `P7Full` with the read-out rows of answers 0 and 1 swapped (14 of 49
pairs wrong, 2 in row 0). `check_fault.sh`: `lake env lean expected_fail/FaultRow.lean` fails with
"Tactic `decide` proved that the proposition … is false". In this toolchain `decide +kernel` hands the
proof term to the kernel first and, only after the kernel throws, evaluates the instance in the
elaborator to word the message (`Decide.lean`, `doKernel`), so that wording follows a kernel
rejection. To show the kernel's own verdict with nothing in between, `kernel_reject.lean` builds the
same proof term `of_decide_eq_true _ _ (Eq.refl true)` and calls `addDecl` directly, with
`Elab.async false`: output `kernel REJECTED fault_row0: (kernel) application type mismatch …` and
`kernel ACCEPTED real_row0` (2.5 s).

**Last-pair faults.** The fault above is wrong in row 0, so a check that stopped at the first bad
pair would already catch it. The second reviewer's two faults are wrong only in the last column:
`P7LastFault` is `P7Full` with E2 row 6 replaced by row 5, and `P113LastFault` is the 448-neuron
`P113Full` with `E2_112` replaced by `E2_111`. Both are regenerated from the committed tables by text
substitution (`instances/gen_last_fault.py`, byte-identical to the reviewer's files apart from the
header line) and are not committed (2 MB at p = 113). `check_last_fault.sh` builds their tables one
Lake call at a time, confirms that the kernel rejects `expected_fail/P7LastRow.lean` (the last row,
wrong only at (6, 6)) and `expected_fail/P113LastChunk.lean` (the last chunk of the last row, the
statement of `P113Full.fast_112_4`, wrong only at (112, 112)), then hands six proof terms to `addDecl`
in `kernel_reject_last.lean`: for each fault the range that stops before the bad pair is accepted, the
range that includes it is rejected, and the real network's same range is accepted. Run here on
2026-10-16, 10:28:32Z to 10:32:56Z (264 s: the two 448-neuron `Weights` modules 103 s and 100 s, the
six verdicts 43 s): all six as required (`instances/last_fault_kernel.out`, `last_fault_p7.out`,
`last_fault_p113.out`). The CI job runs it on every push.

**Cost per network** (kernel time, this machine, 4 cores shared with another Lean job throughout):

| Network | neurons | build (sum over files) | build (wall) | `leanchecker` replay (sum over modules) | peak RSS per process |
| --- | --- | --- | --- | --- | --- |
| `P7Full` | 24 | about 7 s | 8.3 s | 7 s | small |
| `P113Nanda5` | 40 | about 30 min (16 row files at about 110 s each, `Weights` 23 s; measured on one row file and in the first session's 1048 s wall at 3 jobs) | 1048 s (first session) | 1176 s | about 1 GB |
| `P113Full` | 448 | 15,788 s (16 row files 860 to 1292 s, `Weights` 114 s, `Table` 6 s) | 8017 s | 12,650 s (21 modules; 16 row files 604 to 858 s) | 2.26 GB per row file, 4.4 GB for `Weights` |

For comparison the first repository checked its two 128-neuron networks in 26 minutes wall on 4 cores
(about 52 core-minutes each). Per input pair the kernel spends about 0.13 s at 40 neurons and about
1.2 s at 448 neurons here (12,769 pairs: 15,668 s), close to linear in the width.

## What is proved, checked, measured, derived, open

- **Proved** (kernel, axioms printed, `leanchecker` replayed): everything in the stage 2 table, including
  `adds_mod_p`, `adds_mod_p_tables`, `adds_mod_p_full` and `P7FullTables.adds_mod_7_by_theorem`.
- **Checked** (kernel, specific instances): `PhaseGridInstances.P7Full.adds_mod_7` (p = 7, all frequencies, M = 25, 24 neurons),
  `PhaseGridInstances.P113Nanda5.adds_mod_113` (Nanda's five frequencies, M = 30, 40 neurons), both replayed by
  `leanchecker` with standard axioms; the planted fault rejected; `PhaseGridInstances.P113Full.adds_mod_113` (all 56 frequencies, M = 25, 448 neurons), replayed by `leanchecker` (21 of 21 modules) with standard axioms; and the 504 entries of the p = 7 tables decided as `t1 a n = v` lookups and the table equalities `ofFn_t1` and so on by `decide` inside `P7Link.lean`.
- **Measured** (Python): the stage 1 table; the looseness of the bound; the p = 1009 cases.
- **Derived** (pen and paper, then proved in Lean): the nine-wave expansion and its grid cancellation;
  the `6M²` per-neuron bound and `M > 24|S|/g`.
- **Open**: the three statements in `Open.lean`; the link between the p = 113 tables and the theorem.

## Run

    cd stage1 && python3 -I families.py && python3 -I rounding2.py 113 30
    cd mathlib && lake exe cache get && ./verify2.sh    # build, leanchecker on all 11 modules, axioms, source scan
    cd instances && ./check_instance.sh P7Full 7 1 && ./check_fault.sh && ./check_last_fault.sh   # about 5 min, mostly the two 448-neuron Weights modules
    cd instances && ./check_instance.sh P113Nanda5 113 1 && ./check_instance.sh P113Full 113 1   # 20 min and about 6 hours

Smaller networks of the same shape, a six-phase cycle in place of the eight-phase grid, the smallest
sets of frequencies that survive 8-bit rounding at 113 and 257, a composite modulus, and a planted fault:
`smallest-networks.md` (built by the other session of 2026-10-16, in `lean/LeanCheckedNetwork/` at the root).
