"""Single-cell weight-fault census for the two-layer integer networks (measured baseline for
workstream 2 of the handoff). For every cell of E1, E2 and W2, every candidate new value is
tried and the network is re-evaluated on all p*p pairs; a fault "flips" if any answer changes.

Fault models:
  values  every value in [-128, 127] other than the current one (255 per cell)
  bits    every single bit flip of the 8-bit two's-complement cell (8 per cell)

Usage: python3 fault_census.py NETWORK.npz [values|bits] [--skip-E]
Semantics mirror lean/LeanCheckedNetwork/Network.lean: hidden = (E1[a]+E2[b])^2 entrywise,
score[c] = sum_h W2[c][h]*hidden[h], answer = first index of the largest score.
"""
import sys, time
import numpy as np

def candidates(cur, mode):
    if mode == "values":
        v = np.arange(-128, 128)
        return v[v != cur]
    u = int(cur) & 0xFF
    flipped = np.array([u ^ (1 << i) for i in range(8)])
    return np.where(flipped >= 128, flipped - 256, flipped).astype(np.int64)

def answers(S):
    return S.argmax(axis=-1)  # numpy argmax returns the first index on a tie, as Network.lean

def census(E1, E2, W2, mode, do_E=True):
    p, H = E1.shape
    A = np.arange(p)
    Hd = (E1[:, None, :] + E2[None, :, :]) ** 2
    S = np.einsum("abh,ch->abc", Hd, W2)
    right = (A[:, None] + A[None, :]) % p
    assert (answers(S) == right).all(), "baseline network is not right everywhere"
    out = {}
    # W2[c][h] -> v changes score[c] by (v - W2[c][h]) * hidden[h] on every pair
    t0 = time.time(); n = 0; cells = 0; tried = 0
    for c in range(p):
        for h in range(H):
            cur = W2[c, h]; vals = candidates(cur, mode); tried += vals.size
            newS = np.broadcast_to(S, (vals.size, p, p, p)).copy()
            newS[:, :, :, c] += (vals - cur)[:, None, None] * Hd[None, :, :, h]
            flip = (answers(newS) != right[None]).any(axis=(1, 2))
            k = int(flip.sum()); n += k; cells += bool(k)
    out["W2"] = (n, tried, cells, p * H, time.time() - t0)
    if do_E:
        for name, Ea, Eb, rowsel in (("E1", E1, E2, "row"), ("E2", E2, E1, "col")):
            t0 = time.time(); n = 0; cells = 0; tried = 0
            for x in range(p):
                for h in range(H):
                    cur = Ea[x, h]; vals = candidates(cur, mode); tried += vals.size
                    dh = (vals[:, None] + Eb[None, :, h]) ** 2 - (cur + Eb[:, h]) ** 2   # V, p
                    base = S[x] if rowsel == "row" else S[:, x]                           # p, p
                    newS = base[None] + dh[:, :, None] * W2[None, None, :, h]
                    tgt = right[x] if rowsel == "row" else right[:, x]
                    flip = (answers(newS) != tgt[None]).any(axis=1)
                    k = int(flip.sum()); n += k; cells += bool(k)
            out[name] = (n, tried, cells, p * H, time.time() - t0)
    return out

if __name__ == "__main__":
    path = sys.argv[1]; mode = sys.argv[2] if len(sys.argv) > 2 else "values"
    do_E = "--skip-E" not in sys.argv
    d = np.load(path)
    E1, E2, W2 = (d[k].astype(np.int64) for k in ("E1q", "E2q", "W2q"))
    res = census(E1, E2, W2, mode, do_E)
    tot_n = tot_t = 0
    for name, (n, tried, cells, ncells, secs) in res.items():
        tot_n += n; tot_t += tried
        print(f"{path} {mode} {name}: {n} of {tried} faults flip >= 1 answer; "
              f"{cells} of {ncells} cells have a flipping value; {secs:.0f} s")
    print(f"{path} {mode} TOTAL: {tot_n} of {tot_t}")
