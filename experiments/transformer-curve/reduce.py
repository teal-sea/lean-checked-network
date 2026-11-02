"""Float kill test for the transformer analog of the circle-curve result. The reductions and the
kill rule below were fixed on 2026-11-01 before any weight-decay-0 transformer checkpoint existed;
the only weights seen while writing them were the released grokked net transformer/runs/best.npz.

Question: does a MEMORIZING one-layer transformer (weight decay 0) contain an exact adder in a
reduction to a few Fourier waves, as the x^2 MLP does (experiments/circle-curve/FINDINGS.md)?

Per checkpoint, on the float weights, every count out of all 12,769 pairs:
  net     wrong pairs, train accuracy (against the labels trained on), held-out accuracy, min gap.
  k(n)    per MLP neuron n, the frequency in 1..56 with the most energy summed over its 8
          normalised input-table spectra ((E + pos_j) WV_h WO_h Win[:, n], h < 4, j < 2) and its
          normalised readout spectrum (W_L[n], W_L = Wout U). K_r: frequencies ranked by how many
          neurons pick them (ties: lower k first).
  A_m     (a weight set) the token rows 0..112 of W_E (token axis) and the columns of U (class
          axis) projected onto the constant plus cos/sin of the top m of K_r; all else unchanged.
          m in M_LIST. Control A_rand_m: m random frequencies, 3 draws seeded by m.
  B_m     (a weight set, one wave per neuron) A_m, then Wout' = T pinv(U'), T[n] = W_L[n]
          projected onto the wave of k(n) when k(n) is in the top m, else 0. B_m+bias adds
          beta = mean over pairs of the MLP activation times (Wout U' - T) to bout through
          pinv(U'). m in B_LIST ("all" = every frequency some neuron picks).
  C       (a table model, one wave per neuron) each neuron's 8 input tables projected onto the
          constant plus its own k(n); the 8 head-to-logit tables onto all picked frequencies on
          both axes; each W_L row onto its k(n) (no constant); attention scores unchanged.
          C+bias adds beta as above.
  N_m     (Nanda et al. 2023's restricted logits; not a weight set) the logit table over (a, b)
          projected onto the constant plus cos/sin of w_k (a + b), k the top m of K_r; m in N_LIST.
          Control N_rand_5.

Kill rule, fixed before results:
  - A checkpoint is MEMORIZING if train accuracy >= 0.99 and held-out accuracy < 0.5.
  - The result TRANSFERS if on at least one of the three weight-decay-0 seeds some memorizing
    checkpoint has a reduction the pipeline can evaluate exactly (A_m or B_m+bias with m <= 8,
    or C+bias) wrong on at most 1% of pairs (127), the random-frequency control at the same m is
    wrong on more than 50%, and the shuffled-label run's reductions stay above 90% wrong.
  - It is KILLED if on all three weight-decay-0 seeds every such reduction is wrong on more than
    1% of pairs at every memorizing checkpoint.
  - A memorizing checkpoint with such a reduction wrong on 0 pairs is the seal candidate.

Usage: python3 reduce.py CKPT.npz [...]          one JSON line per checkpoint on stdout
       python3 reduce.py --follow RUN_DIR         process RUN_DIR/ckpt_*.npz as they appear, append
                                                  to RUN_DIR/reduce.jsonl, stop once RUN_DIR/DONE
                                                  exists and every checkpoint is done
About a minute per checkpoint on one core; run it on a box, not the Mac."""
import glob
import json
import os
import sys
import time

import numpy as np

P, DH, H, NM = 113, 32, 4, 512
KEYS = ["tok", "pos", "WQ", "WK", "WV", "WO", "Win", "bin", "Wout", "bout", "U"]
M_LIST = [1, 2, 3, 4, 5, 6, 8, 12, 16]
B_LIST = [4, 8, 16, "all"]
N_LIST = [4, 5, 8]
PAIRS = np.array([(a, b) for a in range(P) for b in range(P)])
AA, BB = PAIRS[:, 0], PAIRS[:, 1]
Y = (AA + BB) % P
T = np.arange(P)
ROWS = np.arange(len(Y))


def basis(K, dc=True):
    cols = [np.ones(P) / np.sqrt(P)] if dc else []
    for k in K:
        c = np.cos(2 * np.pi * k * T / P); s = np.sin(2 * np.pi * k * T / P)
        cols += [c / np.linalg.norm(c), s / np.linalg.norm(s)]
    return np.stack(cols, 1)


def attention(W):
    """softmax weights (N, 4, 3) at the '=' position, and x2 = embedding of '=' at position 2."""
    E = W["tok"][:P]; x2 = W["tok"][P] + W["pos"][2]
    q = np.einsum("d,hde->he", x2, W["WQ"])
    sc = [np.einsum("td,hde,he->th", E + W["pos"][j], W["WK"], q) / np.sqrt(DH) for j in range(2)]
    sc2 = np.einsum("d,hde,he->h", x2, W["WK"], q) / np.sqrt(DH)
    s = np.stack([sc[0][AA], sc[1][BB], np.broadcast_to(sc2, (len(AA), H))], -1)
    s = s - s.max(-1, keepdims=True); e = np.exp(s)
    return e / e.sum(-1, keepdims=True), x2


def fwd(W, want_act=False):
    att, x2 = attention(W)
    E = W["tok"][:P]
    OV = np.einsum("hde,hef->hdf", W["WV"], W["WO"])
    V = [np.einsum("td,hdf->thf", E + W["pos"][j], OV) for j in range(2)]
    V2 = np.einsum("d,hdf->hf", x2, OV)
    r = (x2 + np.einsum("nh,nhf->nf", att[:, :, 0], V[0][AA]) + np.einsum("nh,nhf->nf", att[:, :, 1], V[1][BB])
         + att[:, :, 2] @ V2)
    act = np.maximum(r @ W["Win"] + W["bin"], 0)
    L = (r + act @ W["Wout"] + W["bout"]) @ W["U"]
    return (L, act) if want_act else L


def score(L):
    """[wrong pairs, smallest gap (right logit minus best other; negative when wrong somewhere)]."""
    right = L[ROWS, Y]; L2 = L.copy(); L2[ROWS, Y] = -np.inf
    return [int((L.argmax(1) != Y).sum()), round(float((right - L2.max(1)).min()), 5)]


def neuron_freqs(W):
    E = W["tok"][:P]
    Fn = np.zeros((NM, 56))
    def add(Tab):  # Tab: P x NM, token axis first
        en = (np.abs(np.fft.rfft(Tab, axis=0)) ** 2)[1:57].T
        return en / np.maximum(en.sum(1, keepdims=True), 1e-300)
    for h in range(H):
        M = W["WV"][h] @ W["WO"][h] @ W["Win"]
        for j in range(2):
            Fn += add((E + W["pos"][j]) @ M)
    Fn += add((W["Wout"] @ W["U"]).T)
    kn = Fn.argmax(1) + 1
    cnt = np.bincount(kn, minlength=57)
    Kr = sorted(range(1, 57), key=lambda k: (-cnt[k], k))
    share = float(np.mean(Fn[np.arange(NM), kn - 1] / Fn.sum(1)))
    return kn, Kr, cnt, share


def reduce_A(W, K):
    Bk = basis(K); W1 = dict(W)
    tok = W["tok"].copy(); tok[:P] = Bk @ (Bk.T @ W["tok"][:P]); W1["tok"] = tok
    W1["U"] = (W["U"] @ Bk) @ Bk.T
    kept_tok = float(np.linalg.norm(tok[:P]) ** 2 / np.linalg.norm(W["tok"][:P]) ** 2)
    kept_U = float(np.linalg.norm(W1["U"]) ** 2 / np.linalg.norm(W["U"]) ** 2)
    return W1, kept_tok, kept_U


def reduce_B(W, K, kn):
    W1, _, _ = reduce_A(W, K); Up = W1["U"]
    WL = W["Wout"] @ W["U"]
    Tg = np.zeros_like(WL)
    for n in range(NM):
        if kn[n] in K:
            b = basis([kn[n]], dc=False); Tg[n] = (WL[n] @ b) @ b.T
    pinvU = np.linalg.pinv(Up)
    W1["Wout"] = Tg @ pinvU
    L1, act = fwd(W1, want_act=True)
    beta = act.mean(0) @ (W["Wout"] @ Up - Tg)
    Wb = dict(W1); Wb["bout"] = W["bout"] + beta @ pinvU
    return score(L1), score(fwd(Wb)), int(np.isin(kn, K).sum())


def reduce_C(W, kn):
    att, x2 = attention(W)
    E = W["tok"][:P]
    G = W["Wout"] @ W["U"]
    TI = [[(E + W["pos"][j]) @ W["WV"][h] @ W["WO"][h] @ W["Win"] for j in range(2)] for h in range(H)]
    TU = [[(E + W["pos"][j]) @ W["WV"][h] @ W["WO"][h] @ W["U"] for j in range(2)] for h in range(H)]
    TI2 = [x2 @ W["WV"][h] @ W["WO"][h] @ W["Win"] for h in range(H)]
    TU2 = [x2 @ W["WV"][h] @ W["WO"][h] @ W["U"] for h in range(H)]
    CI = x2 @ W["Win"] + W["bin"]; CU = x2 @ W["U"] + W["bout"] @ W["U"]

    def run(TI, TU, G, CU):
        pre = CI + sum(att[:, h, 0, None] * TI[h][0][AA] + att[:, h, 1, None] * TI[h][1][BB]
                       + att[:, h, 2, None] * TI2[h] for h in range(H))
        act = np.maximum(pre, 0)
        L = CU + sum(att[:, h, 0, None] * TU[h][0][AA] + att[:, h, 1, None] * TU[h][1][BB]
                     + att[:, h, 2, None] * TU2[h] for h in range(H)) + act @ G
        return L, act

    used = sorted(set(kn.tolist())); BK = basis(used)
    TIp = [[np.zeros_like(TI[h][j]) for j in range(2)] for h in range(H)]
    for k in used:
        Bk = basis([k]); idx = kn == k
        for h in range(H):
            for j in range(2):
                TIp[h][j][:, idx] = Bk @ (Bk.T @ TI[h][j][:, idx])
    TUp = [[BK @ BK.T @ TU[h][j] @ BK @ BK.T for j in range(2)] for h in range(H)]
    Gp = np.zeros_like(G)
    for n in range(NM):
        b = basis([kn[n]], dc=False); Gp[n] = (G[n] @ b) @ b.T
    L0, _ = run(TI, TU, G, CU)
    L1, act = run(TIp, TUp, Gp, CU)
    beta = act.mean(0) @ (G - Gp)
    L2, _ = run(TIp, TUp, Gp, CU + beta)
    return score(L0)[0], score(L1), score(L2), len(used)


def nanda(L, K):
    Lr = L.reshape(P, P, P); s = (T[:, None] + T[None, :]) % P
    R = np.broadcast_to(Lr.mean((0, 1), keepdims=True), Lr.shape).copy()
    for k in K:
        for wave in (np.cos(2 * np.pi * k * s / P), np.sin(2 * np.pi * k * s / P)):
            R += np.einsum("ab,abc->c", wave, Lr)[None, None, :] * wave[:, :, None] / (wave ** 2).sum()
    R = R.reshape(-1, P)
    z = R - R.max(1, keepdims=True); ce = float(np.mean(np.log(np.exp(z).sum(1)) - z[ROWS, Y]))
    return [int((R.argmax(1) != Y).sum()), round(ce, 5)]


def rand_K(m, draw):
    return sorted(np.random.default_rng(1000 * m + draw).choice(np.arange(1, 57), m, replace=False).tolist())


def analyse(path):
    t0 = time.time()
    z = np.load(path)
    W = {k: np.asarray(z[k], dtype=np.float64) for k in KEYS}
    meta = {k: (z[k].item() if z[k].ndim == 0 else None) for k in ["epoch", "seed", "wd", "frac", "shuffled"] if k in z}
    tr = np.asarray(z["train_idx"]) if "train_idx" in z else np.arange(len(Y))
    labels = np.asarray(z["labels"]) if "labels" in z else Y
    te = np.setdiff1d(np.arange(len(Y)), tr)
    L = fwd(W)
    pred = L.argmax(1)
    res = {"file": os.path.basename(path), **meta,
           "net": score(L), "train_acc": round(float((pred[tr] == labels[tr]).mean()), 4),
           "heldout_acc": round(float((pred[te] == Y[te]).mean()), 4) if len(te) else None}
    kn, Kr, cnt, share = neuron_freqs(W)
    res["K_r"] = Kr[:16]; res["K_count"] = [int(cnt[k]) for k in Kr[:16]]
    res["n_freqs_picked"] = int((cnt[1:] > 0).sum()); res["dominant_share"] = round(share, 4)
    res["A"] = {}
    res["A_rand"] = {}
    for m in M_LIST:
        W1, kt, ku = reduce_A(W, Kr[:m])
        res["A"][m] = score(fwd(W1)) + [round(kt, 4), round(ku, 4)]
        res["A_rand"][m] = [score(fwd(reduce_A(W, rand_K(m, d))[0]))[0] for d in range(3)]
    res["B"] = {}
    for m in B_LIST:
        K = sorted(set(kn.tolist())) if m == "all" else Kr[:m]
        clock, biased, kept = reduce_B(W, K, kn)
        res["B"][m] = {"clock": clock, "bias": biased, "neurons": kept, "m": len(K)}
    c0, c1, c2, nused = reduce_C(W, kn)
    res["C"] = {"table_check": c0, "clock": c1, "bias": c2, "freqs": nused}
    res["N"] = {m: nanda(L, Kr[:m]) for m in N_LIST}
    res["N_rand_5"] = [nanda(L, rand_K(5, d))[0] for d in range(3)]
    res["secs"] = round(time.time() - t0, 1)
    return res


def main():
    if sys.argv[1] == "--follow":
        d = sys.argv[2]; out = os.path.join(d, "reduce.jsonl")
        done = set()
        if os.path.exists(out):
            done = {json.loads(l)["file"] for l in open(out) if l.strip()}
        while True:
            finished = os.path.exists(os.path.join(d, "DONE"))
            todo = [p for p in sorted(glob.glob(os.path.join(d, "ckpt_*.npz"))) if os.path.basename(p) not in done]
            for p in todo:
                with open(out, "a") as fh:
                    fh.write(json.dumps(analyse(p)) + "\n")
                done.add(os.path.basename(p))
            if finished and not todo:
                break
            if not todo:
                time.sleep(30)
        open(os.path.join(d, "REDUCED"), "w").write("ok\n")
    else:
        for p in sys.argv[1:]:
            print(json.dumps(analyse(p)), flush=True)


if __name__ == "__main__":
    main()
