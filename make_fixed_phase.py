"""Build fixed-phase circle networks that add mod p exactly, in the first repo's .npz format.

Per frequency k in S, 8 neurons: phi1 in {0, pi/2, pi, 3pi/2} x phi2 in {0, pi/2}.
E1[n,h] = cos(2 pi k n/p + phi1), E2[m,h] = cos(2 pi k m/p + phi2), W2[q,h] = cos(2 pi k q/p + phi1 + phi2),
rounded to integers at scale M. Usage: python3 make_fixed_phase.py P M OUT.npz k1,k2,...   (or 'all')
"""
import sys, numpy as np
p, M, out, spec = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
S = list(range(1, (p - 1) // 2 + 1)) if spec == "all" else [int(k) for k in spec.split(",")]
phis = [(a * np.pi / 2, b * np.pi / 2) for a in range(4) for b in range(2)]
x = np.arange(p)
E1, E2, W2 = [], [], []
for k in S:
    for f1, f2 in phis:
        E1.append(np.cos(2 * np.pi * k * x / p + f1))
        E2.append(np.cos(2 * np.pi * k * x / p + f2))
        W2.append(np.cos(2 * np.pi * k * x / p + f1 + f2))
E1, E2, W2 = (np.array(t).T for t in (E1, E2, W2))
H = E1.shape[1]
E1q, E2q, W2q = (np.round(M * t).astype(np.int64) for t in (E1, E2, W2))
a, b = np.divmod(np.arange(p * p), p)
z = E1q[a] + E2q[b]
Sc = (z * z) @ W2q.T
ans = Sc.argmax(1)
target = (a + b) % p
top2 = np.sort(Sc, 1)[:, -2:]
wrong = int((ans != target).sum()); ties = int((top2[:, 0] == top2[:, 1]).sum())
print(f"p={p} M={M} S={S if len(S) <= 8 else str(len(S))+' freqs'} H={H} wrong={wrong} ties={ties} "
      f"min gap={int((top2[:,1]-top2[:,0]).min())} max|w|={max(abs(E1q).max(), abs(E2q).max(), abs(W2q).max())}")
np.savez(out, p=p, H=H, M=M, S=np.array(S), E1=E1, E2=E2, W2=W2, E1q=E1q, E2q=E2q, W2q=W2q)
sys.exit(0 if wrong == 0 and ties == 0 else 1)
