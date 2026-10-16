"""Freeze a trained recurrent adder to integers and check the finite-state certificate.

Freezing: each affine layer (recurrent: Wh, Wx, bh; sum bit: Wo, Wox, bo; carry: Wc, bc) is
scaled jointly so its largest entry in absolute value is 127, then rounded. A joint positive
scale does not change the sign of the pre-activation, so the only error is rounding.

Integer network (pure integer arithmetic, [.] is 1 if true else 0):
  step(h, (a, b))  = [ Wh h + Wx (a, b) + bh > 0 ]       entry by entry, h in {0,1}^H
  out(h, (a, b))   = [ Wo step(h,(a,b)) + Wox (a, b) + bo > 0 ]
  carry(h)         = [ Wc h + bc > 0 ]
Check: enumerate states reachable from h0 = 0 under all 4 input pairs; verify
  carry(h0) = 0,  carry(step(h,x)) = maj(a, b, carry(h)),  out(h,x) = a xor b xor carry(h)
for every reachable h and every x. Also verifies the same with phi given as a table built by
breadth-first search (consistency of the carry label along every path).

Usage: python3 freeze_check.py NET.npz [OUT_FROZEN.npz]
"""
import sys, itertools
import numpy as np

def freeze_layer(*mats):
    s = 127 / max(np.abs(m).max() for m in mats)
    return [np.round(m * s).astype(np.int64) for m in mats]

def load_frozen(path):
    n = np.load(path)
    Wh, Wx, bh = freeze_layer(n["Wh"], n["Wx"], n["bh"])
    Wo, Wox, bo = freeze_layer(n["Wo"], n["Wox"], n["bo"])
    Wc, bc = freeze_layer(n["Wc"], n["bc"])
    return dict(Wh=Wh, Wx=Wx, bh=bh, Wo=Wo[0], Wox=Wox[0], bo=int(bo[0]), Wc=Wc[0], bc=int(bc[0]))

def check(Q, verbose=True):
    H = Q["Wh"].shape[0]
    inputs = [(a, b) for a in (0, 1) for b in (0, 1)]
    def step(h, x):
        pre = Q["Wh"] @ h + Q["Wx"] @ np.array(x) + Q["bh"]
        return tuple(int(v) for v in (pre > 0)), int(np.abs(pre).min())
    def out(h, x):
        h2, _ = step(h, x)
        v = int(Q["Wo"] @ np.array(h2) + Q["Wox"] @ np.array(x) + Q["bo"])
        return int(v > 0), abs(v)
    def carry(h):
        v = int(Q["Wc"] @ np.array(h) + Q["bc"])
        return int(v > 0), abs(v)
    h0 = tuple([0] * H)
    reach = {h0: 0}           # state -> carry label assigned by breadth-first search (the table phi)
    queue = [h0]
    ok = True; problems = []
    min_margin = 10**9
    if carry(h0)[0] != 0:
        ok = False; problems.append("carry readout of h0 is 1")
    while queue:
        h = queue.pop(0); c = reach[h]
        for (a, b) in inputs:
            h2, mg = step(h, (a, b)); min_margin = min(min_margin, mg)
            c2 = (a + b + c) // 2
            y, mo = out(h, (a, b)); min_margin = min(min_margin, mo)
            if y != (a ^ b ^ c):
                ok = False; problems.append(f"sum bit wrong at h={h} x={(a,b)}")
            if h2 in reach:
                if reach[h2] != c2:
                    ok = False; problems.append(f"table phi inconsistent at h={h2}")
            else:
                reach[h2] = c2; queue.append(h2)
            cr, mc = carry(h2); min_margin = min(min_margin, mc)
            if cr != c2:
                ok = False; problems.append(f"carry readout wrong at h={h2}: readout {cr}, needed {c2}")
    if verbose:
        print(f"  H={H} reachable states: {len(reach)}  certificate {'HOLDS' if ok else 'FAILS'}"
              f"  smallest |pre-activation| over reachable transitions: {min_margin}")
        for h, c in reach.items():
            print(f"    state {''.join(map(str,h))} carry {c}")
        for p in problems[:5]:
            print("    " + p)
    return ok, len(reach), min_margin

if __name__ == "__main__":
    Q = load_frozen(sys.argv[1])
    print(sys.argv[1])
    ok, n, mg = check(Q)
    if len(sys.argv) > 2:
        np.savez(sys.argv[2], **Q)
        print("  frozen integer weights saved to", sys.argv[2])
    sys.exit(0 if ok else 1)
