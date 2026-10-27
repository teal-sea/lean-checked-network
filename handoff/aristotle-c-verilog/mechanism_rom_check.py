"""Checks that a fixed-phase network's three weight tables are one shared cosine ROM indexed by
angle sums (the basis of workstream 1's mechanism RTL), and sizes the trained network's
circle/residual split (tier B). Measured, not kernel evidence.

Usage: python3 mechanism_rom_check.py
"""
import numpy as np

def fixed_phase_rom(path):
    d = np.load(path)
    p, H, M = int(d["p"]), int(d["H"]), int(d["M"]); S = [int(k) for k in d["S"]]
    E1q, E2q, W2q = (d[k].astype(np.int64) for k in ("E1q", "E2q", "W2q"))
    if H != 6 * len(S):
        print(f"{path}: H={H} is not 6 per frequency (eight-phase grid from make_fixed_phase.py); "
              f"this check covers only the six-phase cycle networks")
        return None
    G = np.lcm(p, 6)                       # angle grid: 2*pi/G units; 678 for p = 113
    rom = np.round(M * np.cos(2 * np.pi * np.arange(G) / G)).astype(np.int64)
    x = np.arange(p)
    E1r = np.zeros_like(E1q); E2r = np.zeros_like(E2q); W2r = np.zeros_like(W2q)
    for i, k in enumerate(S):
        for j in range(6):
            h = 6 * i + j
            E1r[:, h] = rom[(6 * k * x + (G // 6) * j) % G]          # phi1 = 2 pi j / 6
            E2r[:, h] = rom[(6 * k * x + 4 * (G // 6) * j) % G]      # phi2 = 4 phi1
            W2r[:, h] = rom[(6 * k * x + 5 * (G // 6) * j) % G]      # phi1 + phi2
    diffs = {n: (int((R != Q).sum()), int(np.abs(R - Q).max())) for n, R, Q in
             (("E1", E1r, E1q), ("E2", E2r, E2q), ("W2", W2r, W2q))}
    total = sum(c for c, _ in diffs.values())
    print(f"{path}: p={p} H={H} M={M} S={S} grid={G} entries; ROM range [{rom.min()}, {rom.max()}]; "
          f"shared-ROM reconstruction differs in {total} of {3*p*H} cells "
          f"(E1 {diffs['E1'][0]}, E2 {diffs['E2'][0]}, W2 {diffs['W2'][0]}; max |diff| "
          f"{max(m for _, m in diffs.values())})")
    return total == 0

def trained_split(trained="network/trained.npz", circle="network/circle_only.npz"):
    t = np.load(trained); c = np.load(circle)
    T = [t[k].astype(np.int64) for k in ("E1q", "E2q", "W2q")]
    C = [c[k].astype(np.int64) for k in ("E1q", "E2q", "W2q")]
    R = [a - b for a, b in zip(T, C)]
    p, H = T[0].shape; A = np.arange(p); right = (A[:, None] + A[None, :]) % p
    def wrong(E1, E2, W2):
        Hd = (E1[:, None, :] + E2[None, :, :]) ** 2
        return int((np.einsum("abh,ch->abc", Hd, W2).argmax(-1) != right).sum())
    print(f"trained: max|w| = {max(abs(x).max() for x in T)}; wrong = {wrong(*T)} of {p*p}")
    print(f"circle-only: max|w| = {max(abs(x).max() for x in C)} (needs 9-bit cells); wrong = {wrong(*C)} of {p*p}")
    print(f"residual (trained - circle): max|w| = {max(abs(x).max() for x in R)}; "
          f"residual-only network wrong = {wrong(*R)} of {p*p}")

if __name__ == "__main__":
    for f in ("network/fixed12.npz", "network/fixed16.npz", "network/mod257_min.npz", "network/mod12_all.npz"):
        fixed_phase_rom(f)
    trained_split()
