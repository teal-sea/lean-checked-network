"""Exact integer evaluation of the one-layer transformer, with a certified exp replacement.

Everything here is the reference the Lean lane mirrors. Three objects:

1. `quantise(W, q)`: every matrix to integers at scale S = 2^q (W_Q also absorbs 1/sqrt(32); the
   MLP biases are at S^4 and S^5 so that every quantity in the integer program has one scale).
   The "quantised model" M_q is the real-softmax transformer whose weights are these integers
   divided by their scales. Theorem C of DESIGN.md is about M_q.
2. `expfix(x, t, f, n, m, R)`: an integer-valued stand-in for 2^f * exp(x / 2^t) on integers
   x <= 0, built from a degree-(n-1) Taylor polynomial evaluated in exact rational arithmetic on
   y = x / 2^(t+m) in [-1, 0], raised to the 2^m-th power, and floored once. `delta_bound`
   gives the proved absolute error delta (Theorem B1).
3. `int_logits_raw` / `int_logits_tables`: the integer program. No division anywhere: the four
   softmax denominators D^h are carried along and their product D multiplies every additive
   term. The program's logits are L = D * S^6 * (logits of M_q) when expfix is exact; with the
   approximate expfix they move by at most E (`error_bound_E`, Theorem B2). The argmax of L is
   the model's answer, first index on a tie (as `argmax` in lean/LeanCheckedNetwork/Network.lean).

Usage:
  python3 transformer/int_transformer.py WEIGHTS.npz --q 8 --f 32 --n 16 --m 5      one configuration
  python3 transformer/int_transformer.py WEIGHTS.npz --scan "8,32,16,5;10,40,18,5"    a table
  python3 transformer/int_transformer.py --random 0 --q 8 ...                          random weights
  --subset K   check the raw program against the table program on K random pairs (default 64)
  --rows N     evaluate only the first N rows a (for a quick look); default all 113
"""
import argparse
import math
import sys
import time
from fractions import Fraction

import numpy as np

P = 113
VOCAB = P + 1
EQ = P
D_MODEL, N_HEADS, D_HEAD, D_MLP = 128, 4, 32, 512

# ----------------------------------------------------------------------------------------------
# expFix and its error bound (Theorem B1)


def taylor_tau(n):
    """Mathlib Real.exp_bound: for |y| <= 1, |exp y - sum_{i<n} y^i/i!| <= |y|^n (n+1)/(n! n)."""
    return Fraction(n + 1, math.factorial(n) * n)


def delta_bound(f, n, m, R):
    """A proved upper bound on |expfix(x) - 2^f exp(x/2^t)| for every integer x <= 0.

    In range (-R 2^t <= x <= 0): y = x/2^(t+m) is in [-1, 0] because R <= 2^m; the polynomial
    value T satisfies |T - exp y| <= tau and |T| <= 1 + tau, exp y <= 1; so
    |T^N - (exp y)^N| <= N tau (1 + tau)^(N-1) with N = 2^m, and the single floor adds < 1.
    Below the range the output is 0 and the true value is below 2^f e^-R, which the caller keeps
    at or below 1 (checked here with exp 1 > 2.7182818283, Mathlib's Real.exp_one_gt_d9).
    Returns an integer delta (ceiling of the exact rational bound).
    """
    assert R <= 2 ** m, "range reduction needs R <= 2^m"
    N = 2 ** m
    tau = taylor_tau(n)
    in_range = Fraction(2 ** f) * N * tau * (1 + tau) ** (N - 1) + 1
    clamp = Fraction(2 ** f) / Fraction(27182818283, 10 ** 10) ** R
    assert clamp <= 1, f"clamp error {float(clamp)} > 1: raise R"
    return math.ceil(max(in_range, clamp))


def expfix_params(t, f, n, m, R):
    """The integer constants of expfix: Horner coefficients c_i = (n-1)!/i! 2^((t+m)(n-1-i)) and F."""
    tm = t + m
    c = [math.factorial(n - 1) // math.factorial(i) * 2 ** (tm * (n - 1 - i)) for i in range(n)]
    F = math.factorial(n - 1) * 2 ** (tm * (n - 1))
    return c, F, F ** (2 ** m), R * 2 ** t


def expfix(x, t, f, n, m, R, params=None):
    """Integer stand-in for 2^f * exp(x / 2^t), x an integer <= 0. See delta_bound."""
    assert x <= 0
    c, F, F_pow, lo = params if params is not None else expfix_params(t, f, n, m, R)
    if x < -lo:
        return 0
    # N = sum_{i<n} c_i x^i by Horner; N / F = sum_{i<n} (x / 2^(t+m))^i / i! exactly.
    N = 0
    for i in range(n - 1, -1, -1):
        N = N * x + c[i]
    # One floor: floor(2^f * N^(2^m) / F^(2^m)). N^(2^m) >= 0 (even power for m >= 1; and N > 0).
    return (2 ** f * N ** (2 ** m)) // F_pow


# ----------------------------------------------------------------------------------------------
# weights


def random_weights(seed):
    rng = np.random.default_rng(seed)
    s = 1 / np.sqrt(D_MODEL)
    return {
        "tok": rng.normal(0, s, (VOCAB, D_MODEL)), "pos": rng.normal(0, s, (3, D_MODEL)),
        "WQ": rng.normal(0, s, (N_HEADS, D_MODEL, D_HEAD)), "WK": rng.normal(0, s, (N_HEADS, D_MODEL, D_HEAD)),
        "WV": rng.normal(0, s, (N_HEADS, D_MODEL, D_HEAD)), "WO": rng.normal(0, 1 / np.sqrt(D_HEAD), (N_HEADS, D_HEAD, D_MODEL)),
        "Win": rng.normal(0, s, (D_MODEL, D_MLP)), "bin": rng.normal(0, 0.1, D_MLP),
        "Wout": rng.normal(0, 1 / np.sqrt(D_MLP), (D_MLP, D_MODEL)), "bout": rng.normal(0, 0.1, D_MODEL),
        "U": rng.normal(0, s, (D_MODEL, P)),
    }


def load_weights(path):
    z = np.load(path)
    keys = ["tok", "pos", "WQ", "WK", "WV", "WO", "Win", "bin", "Wout", "bout", "U"]
    return {k: np.asarray(z[k], dtype=np.float64) for k in keys}


def rnd(x):
    """Round half away from zero to a Python-int object array (Lean: Int.round is half up; the
    two agree except at exact halves, which do not occur in float64 training weights times 2^q
    except by coincidence; the integer tables are what is checked, so the rule is immaterial)."""
    return np.vectorize(lambda v: int(math.floor(v + 0.5)), otypes=[object])(np.asarray(x, dtype=np.float64))


def quantise(W, q):
    """Integer weights at scale S = 2^q. W_Q absorbs 1/sqrt(32); biases at S^4 and S^5."""
    S = 2 ** q
    return {
        "q": q, "S": S, "t": 4 * q,
        "tok": rnd(S * W["tok"]), "pos": rnd(S * W["pos"]),
        "WQ": rnd(S * W["WQ"] / np.sqrt(D_HEAD)), "WK": rnd(S * W["WK"]), "WV": rnd(S * W["WV"]), "WO": rnd(S * W["WO"]),
        "Win": rnd(S * W["Win"]), "bin": rnd(S ** 4 * W["bin"]),
        "Wout": rnd(S * W["Wout"]), "bout": rnd(S ** 5 * W["bout"]),
        "U": rnd(S * W["U"]),
    }


def dequantise(Wq):
    """The real weights of the quantised model M_q (float64 views of the integers)."""
    S = float(Wq["S"])
    f = lambda a, s: np.asarray(a, dtype=object).astype(np.float64) / s
    return {
        "tok": f(Wq["tok"], S), "pos": f(Wq["pos"], S), "WQ": f(Wq["WQ"], S), "WK": f(Wq["WK"], S),
        "WV": f(Wq["WV"], S), "WO": f(Wq["WO"], S), "Win": f(Wq["Win"], S), "bin": f(Wq["bin"], S ** 4),
        "Wout": f(Wq["Wout"], S), "bout": f(Wq["bout"], S ** 5), "U": f(Wq["U"], S),
    }


# ----------------------------------------------------------------------------------------------
# float forward passes


def float_logits(W, pairs, scale_scores=True):
    """Real-softmax logits at the last position for an array of pairs; W real weights.
    scale_scores: divide q.k by sqrt(32) (the trained model); False for M_q, whose W_Q already
    carries the factor."""
    a, b = pairs[:, 0], pairs[:, 1]
    x0 = W["tok"][a] + W["pos"][0]; x1 = W["tok"][b] + W["pos"][1]
    x2 = np.broadcast_to(W["tok"][EQ] + W["pos"][2], x0.shape)
    X = np.stack([x0, x1, x2], 1)
    q = np.einsum("nd,hde->nhe", x2, W["WQ"])
    k = np.einsum("njd,hde->nhje", X, W["WK"])
    v = np.einsum("njd,hde->nhje", X, W["WV"])
    s = np.einsum("nhe,nhje->nhj", q, k)
    if scale_scores:
        s = s / np.sqrt(D_HEAD)
    s = s - s.max(-1, keepdims=True)
    e = np.exp(s)
    att = e / e.sum(-1, keepdims=True)
    z = np.einsum("nhj,nhje->nhe", att, v)
    r = x2 + np.einsum("nhe,hed->nd", z, W["WO"])
    mlp = np.maximum(r @ W["Win"] + W["bin"], 0) @ W["Wout"] + W["bout"]
    return (r + mlp) @ W["U"]


def margins_of(logits, labels):
    right = logits[np.arange(len(labels)), labels]
    wrong = logits.copy(); wrong[np.arange(len(labels)), labels] = -np.inf
    return right - wrong.max(1)


# ----------------------------------------------------------------------------------------------
# the integer program


def xhat(Wq, tok, j):
    return Wq["tok"][tok] + Wq["pos"][j]


def int_logits_raw(Wq, a, b, ef):
    """The integer program from the raw integer matrices (the definition). ef(x) = expfix(x)."""
    S = Wq["S"]
    toks = (a, b, EQ)
    x = [xhat(Wq, toks[j], j) for j in range(3)]
    ehat, Dh, w = [], [], []
    for h in range(N_HEADS):
        qh = x[2] @ Wq["WQ"][h]                              # (32,)
        s = [qh @ (x[j] @ Wq["WK"][h]) for j in range(3)]    # exact integer scores
        smax = max(s)
        e = [ef(sj - smax) for sj in s]
        ehat.append(e); Dh.append(sum(e))
        z = sum(e[j] * (x[j] @ Wq["WV"][h]) for j in range(3))   # (32,)
        w.append(z @ Wq["WO"][h])                                 # (128,)
    D = Dh[0] * Dh[1] * Dh[2] * Dh[3]
    c = [math.prod(Dh[k] for k in range(N_HEADS) if k != h) for h in range(N_HEADS)]
    A = sum(c[h] * w[h] for h in range(N_HEADS))
    r = D * S ** 2 * x[2] + A
    pre = r @ Wq["Win"] + D * Wq["bin"]
    mm = np.array([v if v > 0 else 0 for v in pre], dtype=object)
    o = mm @ Wq["Wout"] + D * Wq["bout"]
    fin = S ** 2 * r + o
    L = fin @ Wq["U"]
    return L, D


def build_tables(Wq):
    """Everything per token that the per-pair program looks up (Lean verifies these once).

    For head h and position j: scores sc[h][j][tok] = (W_Q^h x_2) . (W_K^h x_j(tok)),
    O = W_O^h W_V^h x_j(tok) (128), TI[h][j][tok] = O @ W_in (512), TU[h][j][tok] = O @ U (113).
    Position 2 only ever holds '=' ; the table there has one entry (index EQ) and the rest unused.
    Constants: CI = S^2 x_2 @ W_in + b_in, CU = S^4 x_2 @ U + b_out @ U, G = W_out @ U (512 x 113).
    """
    S = Wq["S"]
    x2 = xhat(Wq, EQ, 2)
    T = {"sc": [], "TI": [], "TU": [], "Omax": []}
    for h in range(N_HEADS):
        qh = x2 @ Wq["WQ"][h]
        sc, TI, TU, Omax = [], [], [], 0
        for j in range(3):
            toks = range(VOCAB) if j < 2 else [EQ]
            X = np.array([xhat(Wq, tok, j) for tok in toks], dtype=object)       # (n, 128)
            sc_j = (X @ Wq["WK"][h]) @ qh                                        # (n,)
            O = (X @ Wq["WV"][h]) @ Wq["WO"][h]                                  # (n, 128)
            Omax = max(Omax, max(abs(int(v)) for v in O.ravel()))
            if j == 2:
                full = np.zeros(VOCAB, dtype=object); full[EQ] = sc_j[0]; sc_j = full
                Ofull = np.zeros((VOCAB, D_MODEL), dtype=object); Ofull[EQ] = O[0]; O = Ofull
            sc.append(sc_j); TI.append(O @ Wq["Win"]); TU.append(O @ Wq["U"])
        T["sc"].append(sc); T["TI"].append(TI); T["TU"].append(TU); T["Omax"].append(Omax)
    T["CI"] = S ** 2 * (x2 @ Wq["Win"]) + Wq["bin"]
    T["CU"] = S ** 4 * (x2 @ Wq["U"]) + Wq["bout"] @ Wq["U"]
    T["G"] = Wq["Wout"] @ Wq["U"]
    T["X2max"] = max(abs(int(v)) for v in x2)
    return T


def int_logits_tables(Wq, T, a, b, ef):
    """The same integer program through the tables: what the kernel runs per pair."""
    S = Wq["S"]
    toks = (a, b, EQ)
    Dh, e = [], []
    for h in range(N_HEADS):
        s = [T["sc"][h][j][toks[j]] for j in range(3)]
        smax = max(s)
        eh = [ef(sj - smax) for sj in s]
        e.append(eh); Dh.append(sum(eh))
    D = Dh[0] * Dh[1] * Dh[2] * Dh[3]
    c = [math.prod(Dh[k] for k in range(N_HEADS) if k != h) for h in range(N_HEADS)]
    pre = D * T["CI"] + sum(c[h] * sum(e[h][j] * T["TI"][h][j][toks[j]] for j in range(3)) for h in range(N_HEADS))
    mm = np.array([v if v > 0 else 0 for v in pre], dtype=object)
    L = D * T["CU"] + S ** 2 * sum(c[h] * sum(e[h][j] * T["TU"][h][j][toks[j]] for j in range(3)) for h in range(N_HEADS)) + mm @ T["G"]
    return L, D


def argmax_first(L):
    best, bi = L[0], 0
    for i in range(1, len(L)):
        if L[i] > best:
            best, bi = L[i], i
    return bi


def margin_of(L, c):
    return L[c] - max(L[i] for i in range(len(L)) if i != c)


# ----------------------------------------------------------------------------------------------
# the perturbation bound (Theorem B2)


def norms(Wq, T):
    ab = lambda M: np.vectorize(abs, otypes=[object])(M)
    return {
        "X2": T["X2max"], "Omax": T["Omax"],
        "Win": max(int(v) for v in ab(Wq["Win"]).sum(0)),      # max over outputs i of sum_k |Win[k,i]|
        "bin": max(abs(int(v)) for v in Wq["bin"]),
        "Wout": max(int(v) for v in ab(Wq["Wout"]).sum(0)),
        "bout": max(abs(int(v)) for v in Wq["bout"]),
        "U": max(int(v) for v in ab(Wq["U"]).sum(0)),          # max over answers c of sum_k |U[k,c]|
    }


def error_bound_E(Wq, nm, f, delta):
    """|L~_c - L*_c| <= E for every c and every pair, where L~ uses expfix and L* the exact
    2^f exp. Derivation in DESIGN.md; every step is a triangle inequality on a product or a sum."""
    S = Wq["S"]
    Me = 2 ** f + delta                   # bound on e_j and e~_j
    MD = 3 * Me                           # bound on D^h and D~^h
    dDh = 3 * delta                       # |D~^h - D^h|
    dD = 4 * dDh * MD ** 3                # |D~ - D|, product of four
    dc = 3 * dDh * MD ** 2                # |c~^h - c^h|, product of three
    dA = sum(dc * 3 * Me * O + MD ** 3 * 3 * delta * O for O in nm["Omax"])
    dr = S ** 2 * nm["X2"] * dD + dA
    dpre = nm["Win"] * dr + nm["bin"] * dD
    do = nm["Wout"] * dpre + nm["bout"] * dD
    dfin = S ** 2 * dr + do
    return nm["U"] * dfin


# ----------------------------------------------------------------------------------------------


def evaluate(W, q, f, n, m, R, rows=P, subset=64, seed=0, say=print):
    t = 4 * q
    delta = delta_bound(f, n, m, R)
    params = expfix_params(t, f, n, m, R)
    ef = lambda x: expfix(x, t, f, n, m, R, params)
    Wq = quantise(W, q)
    S = Wq["S"]
    T = build_tables(Wq)
    nm = norms(Wq, T)
    E = error_bound_E(Wq, nm, f, delta)

    pairs = np.array([(a, b) for a in range(rows) for b in range(P)])
    labels = (pairs[:, 0] + pairs[:, 1]) % P
    # float reference of M_q (same integers, real softmax), and the trained float model
    Lq = float_logits(dequantise(Wq), pairs, scale_scores=False)
    Lf = float_logits(W, pairs, scale_scores=True)
    mq, mf = margins_of(Lq, labels), margins_of(Lf, labels)

    t0 = time.time()
    wrong, ties, below, minmargin, minmargin_pair, minreal = 0, 0, 0, None, None, None
    maxdev = 0.0
    rng = np.random.default_rng(seed)
    check = set(map(tuple, pairs[rng.choice(len(pairs), min(subset, len(pairs)), replace=False)]))
    for i, (a, b) in enumerate(pairs):
        L, D = int_logits_tables(Wq, T, int(a), int(b), ef)
        if (a, b) in check:
            L2, D2 = int_logits_raw(Wq, int(a), int(b), ef)
            assert D2 == D and all(int(u) == int(v) for u, v in zip(L, L2)), f"raw and table programs differ at {(a, b)}"
        ans = argmax_first(L)
        c = int(labels[i])
        mg = margin_of(L, c)
        if ans != c:
            wrong += 1
        if mg == 0:
            ties += 1
        if mg <= 2 * E:
            below += 1
        if minmargin is None or mg < minmargin:
            minmargin, minmargin_pair = mg, (int(a), int(b))
        if minreal is None or mg / (D * S ** 6) < minreal:
            minreal = mg / (D * S ** 6)
        # the integer program's logits over D S^6 against the float forward of M_q
        dev = max(abs(int(L[k]) / (D * S ** 6) - Lq[i, k]) for k in range(P))
        maxdev = max(maxdev, dev)
    secs = time.time() - t0
    rel = Fraction(minmargin, 2 * E) if E else None
    res = dict(q=q, t=t, f=f, n=n, m=m, R=R, delta=delta, E=E, pairs=len(pairs), wrong=wrong, ties=ties,
               below_2E=below, min_margin=minmargin, min_margin_pair=minmargin_pair, margin_over_2E=float(rel),
               min_margin_real_units=minreal, margin_floor_real_units=2 * E / (2 ** (4 * f) * S ** 6),
               float_Mq_min_margin=float(mq.min()), float_trained_min_margin=float(mf.min()),
               float_Mq_wrong=int((Lq.argmax(1) != labels).sum()), float_trained_wrong=int((Lf.argmax(1) != labels).sum()),
               max_dev_int_vs_floatMq=maxdev, raw_vs_table_pairs_checked=len(check), seconds=secs,
               norms=nm, E_bits=E.bit_length(), D_min_bits=(4 * f), logit_bits=max(abs(int(v)) for v in L).bit_length())
    return res


def kernel_cost(n, m):
    """Big-integer steps per pair in the table program, counted as in DESIGN.md."""
    expfix_steps = 12 * (n + m + 3)       # Horner n mult-adds, 2^m-th power as m squarings, shift, divide, compare
    denoms = 8 + 8 + 1                    # D^h sums, c^h products, D
    pre = 12 + 4 + 1                      # packed 512-digit numbers: e*TI, c*(...), D*CI
    unpack_relu = 2 * D_MLP + D_MLP
    out = D_MLP + 12 + 4 + 1 + 1          # packed 113-digit numbers: G columns times m, plus the attention and constant terms
    unpack_argmax = 2 * P + P
    return dict(expfix=expfix_steps, denominators=denoms, pre=pre, unpack_relu=unpack_relu, out=out,
                unpack_argmax=unpack_argmax, total=expfix_steps + denoms + pre + unpack_relu + out + unpack_argmax,
                big_multiply_adds=expfix_steps + denoms + pre + out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("weights", nargs="?")
    ap.add_argument("--random", type=int, default=None)
    ap.add_argument("--q", type=int, default=8)
    ap.add_argument("--f", type=int, default=32)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--m", type=int, default=5)
    ap.add_argument("--R", type=int, default=None, help="clamp; default ceil(f ln 2) + 1")
    ap.add_argument("--scan", default=None, help='semicolon list of "q,f,n,m"')
    ap.add_argument("--rows", type=int, default=P)
    ap.add_argument("--subset", type=int, default=64)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    W = random_weights(args.random) if args.random is not None else load_weights(args.weights)
    src = f"random seed {args.random}" if args.random is not None else args.weights
    out = open(args.out, "a") if args.out else None

    def say(s):
        print(s, flush=True)
        if out:
            print(s, file=out, flush=True)

    configs = [tuple(int(v) for v in c.split(",")) for c in args.scan.split(";")] if args.scan else [(args.q, args.f, args.n, args.m)]
    say(f"# int_transformer.py on {src}, rows {args.rows}, {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}")
    say("# q t f n m R delta E_bits min_margin_bits margin/(2E) wrong ties pairs_le_2E min_margin_real 2E_floor_real max_dev_vs_floatMq floatMq_wrong trained_wrong seconds")
    for (q, f, n, m) in configs:
        R = args.R if args.R is not None else math.ceil(f * math.log(2)) + 1
        r = evaluate(W, q, f, n, m, R, rows=args.rows, subset=args.subset, say=say)
        say(f"{q} {r['t']} {f} {n} {m} {R} {r['delta']} {r['E_bits']} {r['min_margin'].bit_length() if r['min_margin'] > 0 else -(-r['min_margin']).bit_length()} "
            f"{r['margin_over_2E']:.4g} {r['wrong']} {r['ties']} {r['below_2E']} {r['min_margin_real_units']:.6g} {r['margin_floor_real_units']:.3g} "
            f"{r['max_dev_int_vs_floatMq']:.3g} {r['float_Mq_wrong']} {r['float_trained_wrong']} {r['seconds']:.0f}")
        say(f"#   E = {r['E']}")
        say(f"#   min margin {r['min_margin']} at pair {r['min_margin_pair']}; norms {r['norms']}; logit bits {r['logit_bits']}; "
            f"float M_q min margin {r['float_Mq_min_margin']:.4f}, trained float min margin {r['float_trained_min_margin']:.4f}; "
            f"raw-vs-table checked on {r['raw_vs_table_pairs_checked']} pairs; kernel steps per pair {kernel_cost(n, m)}")


if __name__ == "__main__":
    main()
