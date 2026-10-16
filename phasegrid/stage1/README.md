# Stage 1: checking the proposal's derivation numerically

Python 3.13.16, numpy 2.5.3. Run each script with `python3 -I`. Outputs of this session's runs
(2026-10-16, 04:37Z to 05:20Z) are in `../logs/` (the first session's and the second session's logs together).

| Script | What it checks | Log |
| --- | --- | --- |
| `families.py` | the nine cosine waves of one neuron (Claim A), the cancellation of the eight unwanted families over the phase grid (Claim B), and the exact polynomial form of the grid sum over random rationals (Claim C) | `families.log` |
| `rounding2.py p [scan_cap] [--big]` | the integer network at modulus p: all frequencies, the small-gap sets {1,2,3} and {1}, random sets of 3 and 5 frequencies (and Nanda's five at p = 113); tests M just above and just below the derived bound 24 abs(S)/g(S), then scans M = 1 .. scan_cap for failures. `--big` (p = 1009): single-threaded BLAS, no scan on the 4032-neuron set | `stage1_p7_11_12.log`, `stage1_p97_113_257.log`, `stage1_p1009.log` |
| `exact_subset.py` | p = 1009, S = {1}: the bound is M = 1,237,843, where scores exceed int64; exact Python integers on 12 rows | `stage1_p1009_S1_exact.log` |
| `p1009_random.py` | the random sets at p = 1009 | `stage1_p1009_random.log` |
| `summarize.py DIR` | one table from the rounding logs | |
| `rounding.py`, `threshold.py` | the earlier session's versions (same construction) | `../logs/` |

Rounding is half up (`floor(x + 1/2)`), as Lean's `round`; a weight within 1e-9 of a half-integer is
rounded by its exact value (this matters only at p = 12, where cos(pi/3) = 1/2 makes 25 cos a
half-integer). Scores are computed exactly: float64 matrix products while every score is below 2^52,
int64 otherwise, Python integers beyond 2^62.
