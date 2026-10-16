"""Six neurons per frequency: phi1 = 2*pi*j/6, phi2 = 4*phi1 (j = 0..5). Same tables as make_fixed_phase.py.
Usage: python3 make_fixed_phase6.py P M OUT.npz k1,k2,...
"""
import sys, numpy as np
p, M, out, spec = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
S = list(range(1, (p - 1) // 2 + 1)) if spec == "all" else [int(k) for k in spec.split(",")]
phis = [(2*np.pi*j/6, 4*2*np.pi*j/6) for j in range(6)]
x = np.arange(p)
E1, E2, W2 = [], [], []
for k in S:
    for f1, f2 in phis:
        E1.append(np.cos(2*np.pi*k*x/p + f1)); E2.append(np.cos(2*np.pi*k*x/p + f2)); W2.append(np.cos(2*np.pi*k*x/p + f1 + f2))
E1, E2, W2 = (np.array(t).T for t in (E1, E2, W2))
H = E1.shape[1]
# exact-cancellation check on the real network: score == 3 * sum_k cos(2 pi k (a+b-c)/p)
a, b = np.divmod(np.arange(p*p), p); q = np.arange(p)
Sr = ((E1[a] + E2[b])**2) @ W2.T
pred = 3*sum(np.cos(2*np.pi*k*((a[:, None] + b[:, None] - q[None, :]) % p)/p) for k in S)
print(f"real: max|score - 3*wave| = {np.abs(Sr - pred).max():.2e}")
E1q, E2q, W2q = (np.round(M*t).astype(np.int64) for t in (E1, E2, W2))
z = E1q[a] + E2q[b]; Sc = (z*z) @ W2q.T
ans = Sc.argmax(1); target = (a + b) % p
top2 = np.sort(Sc, 1)[:, -2:]
wrong = int((ans != target).sum()); ties = int((top2[:,0] == top2[:,1]).sum())
print(f"p={p} M={M} S={S} H={H} wrong={wrong} ties={ties} min gap={int((top2[:,1]-top2[:,0]).min())} max|w|={max(abs(E1q).max(), abs(E2q).max(), abs(W2q).max())}")
np.savez(out, p=p, H=H, M=M, S=np.array(S), E1=E1, E2=E2, W2=W2, E1q=E1q, E2q=E2q, W2q=W2q)
sys.exit(0 if wrong == 0 and ties == 0 else 1)
