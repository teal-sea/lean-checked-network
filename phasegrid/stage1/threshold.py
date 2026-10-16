"""Stage 1c. Where is the real rounding threshold on the hardest (small-gap) frequency sets?

For each case, test M at fractions of the derived bound B = 24|S|/g(S) and report wrong answers and
ties, then search the smallest M such that M and the next 7 values of M all pass (a run of 8 passes).
"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rounding import check, gap

def report(p, S):
    g = gap(p, S); B = 24*len(S)/g
    print(f"\np={p} S={S} |S|={len(S)} g={g:.5g} bound B={B:.1f}")
    for frac in (1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 3/4, 1):
        M = max(1, int(np.ceil(frac*B)))
        wrong, ties, margin, _ = check(p, S, M)
        print(f"  M={M:6d} (B*{frac:.4g}): wrong={wrong} ties={ties} min margin={margin}")
    # smallest M starting a run of 8 consecutive passing M
    lo, run, M = None, 0, 1
    cap = int(B) + 10
    while M <= cap:
        wrong, ties, _, _ = check(p, S, M)
        if wrong == 0 and ties == 0:
            run += 1
            if run == 1: lo = M
            if run == 8: break
        else:
            run = 0
        M += max(1, M // 50)   # step grows slowly: exact for small M, coarse for large
    print(f"  smallest M beginning a run of 8 passes (stepped search): {lo if run == 8 else 'none found up to ' + str(cap)}; ratio B/M = {B/lo if lo else float('nan'):.1f}")

for p in (97, 113, 257):
    report(p, [1])
    report(p, [1, 2, 3])
report(113, [14, 35, 41, 42, 52])
