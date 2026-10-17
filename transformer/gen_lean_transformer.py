"""Write the quantised transformer into the core-Lean package transformer/lean/, and simulate the
exact program the Lean kernel runs.

Usage: python3 transformer/gen_lean_transformer.py WEIGHTS.npz [--rows-per-file N] [--simulate]
                                                   [--fault H TOK I DELTA] [--out DIR] [--name NAME]

The Lean model (Transformer/Model.lean) is the table program of DESIGN.md section 6 on lists of
Int, with expFix as in int_transformer.py. This script writes the tables (Transformer/Weights.lean),
the bounds layer (Transformer/Net/B/*.lean, Table.lean, Cols.lean; `--bounds-only` rewrites just that from the committed
data files), the row files (Transformer/RowsNN.lean), Transformer/AllInputs.lean, and, with --fault, a copy of the
tables with one raw weight changed (the tables are rebuilt from the changed raw weights) plus the
expected_fail file.

--simulate runs, in Python integers, the packed program that `fastCheck` in Transformer/Fast.lean
runs (base B digits, shift K, truncated subtraction as ReLU), compares its answer and margin with
int_transformer.int_logits_tables on every pair, and reports whether the per-pair checks pass.
"""
import argparse
import math
import sys
import time
from pathlib import Path

import numpy as np

sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))
import int_transformer as it  # noqa: E402

P, EQ, HEADS, DMLP = it.P, it.EQ, it.N_HEADS, it.D_MLP
Q, F, N, M, R = 8, 32, 16, 5, 24
T_UNIT = 4 * Q
LOG2B = 208
B = 2 ** LOG2B


def lit(x):
    """An Int literal written as a constructor, so the kernel does no typeclass unfolding."""
    x = int(x)
    return f"(.ofNat {x})" if x >= 0 else f"(.negSucc {-x - 1})"


def vec(v):
    return "[" + ", ".join(lit(x) for x in v) + "]"


def ivec(v):
    return [int(x) for x in np.asarray(v, dtype=object).ravel()]


def tables_of(Wq):
    """The tables in the shape the Lean file holds them (position 2 is the single token '=')."""
    T = it.build_tables(Wq)
    tb = {
        "sc0": [[int(T["sc"][h][0][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "sc1": [[int(T["sc"][h][1][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "sc2": [int(T["sc"][h][2][EQ]) for h in range(HEADS)],
        "TI0": [[ivec(T["TI"][h][0][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "TI1": [[ivec(T["TI"][h][1][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "TI2": [ivec(T["TI"][h][2][EQ]) for h in range(HEADS)],
        "TU0": [[ivec(T["TU"][h][0][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "TU1": [[ivec(T["TU"][h][1][k]) for k in range(it.VOCAB)] for h in range(HEADS)],
        "TU2": [ivec(T["TU"][h][2][EQ]) for h in range(HEADS)],
        "CI": ivec(T["CI"]), "CU": ivec(T["CU"]),
        "G": [ivec(T["G"][i]) for i in range(DMLP)],
    }
    amax = lambda vs: max(abs(x) for x in vs)
    tb["kTI"] = max(max(amax(v) for tbl in (tb["TI0"], tb["TI1"]) for h in tbl for v in h), max(amax(v) for v in tb["TI2"]))
    tb["kTU"] = max(max(amax(v) for tbl in (tb["TU0"], tb["TU1"]) for h in tbl for v in h), max(amax(v) for v in tb["TU2"]))
    tb["kCI"] = amax(tb["CI"]); tb["kCU"] = amax(tb["CU"]); tb["kG"] = max(amax(r) for r in tb["G"])
    return T, tb


def constants(Wq, T):
    nm = it.norms(Wq, T)
    delta = it.delta_bound(F, N, M, R)
    E = it.error_bound_E(Wq, nm, F, delta)
    c, Fc, Fpow, lo = it.expfix_params(T_UNIT, F, N, M, R)
    return dict(S=Wq["S"], S2=Wq["S"] ** 2, f2=2 ** F, lo=lo, cs=c, Fc=Fc, Fpow=Fpow, pw=2 ** M, delta=delta, E=E, E2=2 * E, norms=nm)


# ----------------------------------------------------------------------------------------------
# the exact program of Transformer/Fast.lean, in Python integers


def pkI(v):
    """pkI (d :: ds) = d + B * pkI ds, on signed digits."""
    acc = 0
    for d in reversed(v):
        acc = d + B * acc
    return acc


def unpk(n, N):
    out = []
    for _ in range(n):
        out.append(N % B); N //= B
    return out


def expfix_lean(x, K):
    """expFix as Model.lean writes it: horner on Int, natAbs, Nat power, one Nat division."""
    if x < -K["lo"]:
        return 0
    acc = 0
    for c in reversed(K["cs"]):
        acc = c + x * acc
    return (K["f2"] * abs(acc) ** K["pw"]) // K["Fpow"]


def packed_tables(tb):
    """pkI of every table vector, computed once (the kernel caches them per row file)."""
    pc = {}
    for key in ("TI0", "TI1", "TU0", "TU1"):
        pc[key] = [[pkI(v) for v in tb[key][h]] for h in range(HEADS)]
    for key in ("TI2", "TU2"):
        pc[key] = [pkI(v) for v in tb[key]]
    pc["CI"], pc["CU"] = pkI(tb["CI"]), pkI(tb["CU"])
    pc["G"] = [pkI(r) for r in tb["G"]]
    return pc


def fast_check(tb, K, a, b, want_detail=False, pc=None):
    """Mirror of fastCheck in Fast.lean. Returns (ok_bits, answer, margin)."""
    if pc is None:
        pc = packed_tables(tb)
    e = []
    for h in range(HEADS):
        s0, s1, s2 = tb["sc0"][h][a], tb["sc1"][h][b], tb["sc2"][h]
        smax = max(s0, max(s1, s2))
        e.append((expfix_lean(s0 - smax, K), expfix_lean(s1 - smax, K), expfix_lean(s2 - smax, K)))
    Dh = [sum(eh) for eh in e]
    D = Dh[0] * Dh[1] * Dh[2] * Dh[3]
    c = [Dh[1] * Dh[2] * Dh[3], Dh[0] * Dh[2] * Dh[3], Dh[0] * Dh[1] * Dh[3], Dh[0] * Dh[1] * Dh[2]]
    kTI, kCI, kTU, kCU, kG = tb["kTI"], tb["kCI"], tb["kTU"], tb["kCU"], tb["kG"]
    preP = D * pc["CI"]
    Kpre = D * kCI
    for h in range(HEADS):
        preP += c[h] * (e[h][0] * pc["TI0"][h][a] + (e[h][1] * pc["TI1"][h][b] + e[h][2] * pc["TI2"][h]))
        Kpre += c[h] * (e[h][0] * kTI + (e[h][1] * kTI + e[h][2] * kTI))
    ones512 = pkI([1] * DMLP); ones113 = pkI([1] * P)
    shifted = preP + Kpre * ones512
    assert shifted >= 0
    digits = unpk(DMLP, shifted)
    mlist = [max(d - Kpre, 0) for d in digits]          # d ∸ K
    LP = D * pc["CU"]
    KL = D * kCU
    att = 0; attK = 0
    for h in range(HEADS):
        att += c[h] * (e[h][0] * pc["TU0"][h][a] + (e[h][1] * pc["TU1"][h][b] + e[h][2] * pc["TU2"][h]))
        attK += c[h] * (e[h][0] * kTU + (e[h][1] * kTU + e[h][2] * kTU))
    LP += K["S2"] * att + sum(mi * g for mi, g in zip(mlist, pc["G"]))
    KL += K["S2"] * attK + DMLP * Kpre * kG
    shiftedL = LP + KL * ones113
    assert shiftedL >= 0
    ld = unpk(P, shiftedL)
    right = (a + b) % P
    ans = it.argmax_first(ld)
    other = max(ld[i] for i in range(P) if i != right)
    ok = (2 * Kpre < B, 2 * KL < B, ans == right, other + K["E2"] < ld[right])
    margin = ld[right] - other
    if want_detail:
        return ok, ans, margin, dict(D=D, Kpre=Kpre, KL=KL, maxdigit_pre=max(digits), maxdigit_L=max(ld))
    return ok, ans, margin


def simulate(tb, K, Wq, T, rows, log):
    t0 = time.time()
    ef = lambda x: it.expfix(x, T_UNIT, F, N, M, R)
    bad = 0; minmargin = None; maxK = 0; maxKL = 0; maxdig = 0
    pc = packed_tables(tb)
    for a in range(rows):
        for b in range(P):
            ok, ans, mg, det = fast_check(tb, K, a, b, True, pc)
            Lref, Dref = it.int_logits_tables(Wq, T, a, b, ef)
            cref = (a + b) % P
            mref = it.margin_of(Lref, cref)
            if not all(ok) or ans != it.argmax_first(Lref) or mg != mref or det["D"] != Dref:
                bad += 1
                log(f"MISMATCH at ({a},{b}): ok {ok} ans {ans} ref {it.argmax_first(Lref)} margin {mg} ref {mref}")
            minmargin = mg if minmargin is None else min(minmargin, mg)
            maxK = max(maxK, det["Kpre"]); maxKL = max(maxKL, det["KL"]); maxdig = max(maxdig, det["maxdigit_L"])
    log(f"simulate: {rows} rows, {rows * P} pairs, {bad} mismatches or failed checks, {time.time() - t0:.0f} s")
    log(f"  smallest margin {minmargin} ({minmargin.bit_length()} bits), 2E = {K['E2']} ({K['E2'].bit_length()} bits), margin/(2E) = {minmargin / K['E2']:.1f}")
    log(f"  largest K {maxK.bit_length()} bits, largest KL {maxKL.bit_length()} bits, largest L digit {maxdig.bit_length()} bits, B = 2^{LOG2B}; 2*KL < B needs KL < 2^{LOG2B - 1}")
    return bad == 0


# ----------------------------------------------------------------------------------------------
# Lean sources


def write_weights(root, name, tb, K, src_label, fault_note=""):
    """The tables, split over files of at most about 60,000 literals each (elaboration memory scales
    with the file), and Weights.lean assembling them."""
    def named(prefix, vectors, doc):
        """One def per vector (a 58,000-literal def exceeds the elaborator's recursion depth), then
        the list of their names."""
        defs = "\n".join(f"def {prefix}_{i} : List Int := {vec(v)}" for i, v in enumerate(vectors))
        names = ", ".join(f"{prefix}_{i}" for i in range(len(vectors)))
        return f"{defs}\n\n/-- {doc} -/\ndef {prefix} : List (List Int) := [{names}]"

    def nat_list(v):
        return "[" + ", ".join(str(x) for x in v) + "]"

    w = root / "W"
    w.mkdir(exist_ok=True)
    head = f"""import Transformer.Model

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Transformer.{name}

"""
    mods = []
    for key in ("TI0", "TI1"):
        for h in range(HEADS):
            (w / f"{key}_{h}.lean").write_text(head + named(f"{key}_{h}", tb[key][h], f"`{key}` of head {h}: one 512-vector per token") + f"\n\nend Transformer.{name}\n")
            mods.append(f"W.{key}_{h}")
    for key in ("TU0", "TU1"):
        body = "\n\n".join(named(f"{key}_{h}", tb[key][h], f"`{key}` of head {h}: one 113-vector per token") for h in range(HEADS))
        (w / f"{key}.lean").write_text(head + body + f"\n\nend Transformer.{name}\n")
        mods.append(f"W.{key}")
    misc = f"""{named("sc0", tb['sc0'], "scores at position 0, one list over the token per head")}

{named("sc1", tb['sc1'], "scores at position 1, one list over the token per head")}

def sc2 : List Int := {vec(tb['sc2'])}

{named("TI2", tb['TI2'], "`TI` at position 2 (the token `=`), one 512-vector per head")}

{named("TU2", tb['TU2'], "`TU` at position 2, one 113-vector per head")}

def CI : List Int := {vec(tb['CI'])}

def CU : List Int := {vec(tb['CU'])}

{named("G", tb['G'], "`G = W_out^T U`: 512 rows of 113")}
"""
    (w / "Misc.lean").write_text(head + misc + f"\nend Transformer.{name}\n")
    mods.append("W.Misc")
    # Bnd and Tab's fields come from Transformer.Fast, not Model: without this import `Bnd` is an auto-bound
    # implicit and `{ kTI := .. }` fails with "expected type is not of the form (C ...)".
    imports = "\n".join(["import Transformer.Fast"] + [f"import Transformer.{name}.{m}" for m in mods])
    body = f"""{imports}

/-!
# Tables of the quantised transformer{fault_note}

q = {Q} (S = {K['S']}), t = {T_UNIT}, f = {F}, n = {N}, m = {M}, R = {R}. `sc0 h` is the list over the first
token of the attention score of head `h` at position 0, `sc1 h` the same at position 1, `sc2 h` the
score of the `=` token at position 2; `TI0 h tok`, `TI1 h tok`, `TI2 h` are the 512-vectors
`W_in^T (W_O^h W_V^h x_j(tok))`, `TU0 h tok`, `TU1 h tok`, `TU2 h` the 113-vectors with `U` in
place of `W_in`; `CI = S^2 W_in^T x_2 + b_in`, `CU = S^4 U^T x_2 + U^T b_out`, `G = W_out^T U`
(512 rows of 113). `.ofNat n` is the integer n and `.negSucc n` the integer -(n + 1).
Generated by `gen_lean_transformer.py` from `{src_label}`; the tables themselves are in `W/`.
-/

namespace Transformer.{name}

def TI0 : List (List (List Int)) := [TI0_0, TI0_1, TI0_2, TI0_3]
def TI1 : List (List (List Int)) := [TI1_0, TI1_1, TI1_2, TI1_3]
def TU0 : List (List (List Int)) := [TU0_0, TU0_1, TU0_2, TU0_3]
def TU1 : List (List (List Int)) := [TU1_0, TU1_1, TU1_2, TU1_3]

/-- The exp constants: `cs` are the Horner coefficients `(n-1)!/i! 2^((t+m)(n-1-i))`,
`Fpow = ((n-1)! 2^((t+m)(n-1)))^(2^m)`, `lo = R 2^t`, `f2 = 2^f`, `pw = 2^m`, `S2 = S^2`. -/
def cfg : Cfg := {{
  S2 := {K['S2']}, f2 := {K['f2']}, lo := {K['lo']}, pw := {K['pw']},
  cs := {nat_list(K['cs'])},
  Fpow := {K['Fpow']} }}

/-- The largest absolute entry of each table (checked by `tables_ok`). -/
def bnd : Bnd := {{ kTI := {tb['kTI']}, kCI := {tb['kCI']}, kTU := {tb['kTU']}, kCU := {tb['kCU']}, kG := {tb['kG']} }}

def tab : Tab := {{
  sc0 := sc0, sc1 := sc1, sc2 := sc2, TI0 := TI0, TI1 := TI1, TI2 := TI2,
  TU0 := TU0, TU1 := TU1, TU2 := TU2, CI := CI, CU := CU, G := G }}

/-- Twice the logit error bound E of DESIGN.md section 5 (Theorem B2), as an integer:
E = {K['E']}. -/
def E2 : Nat := {K['E2']}

/-- The model's answer for the pair `(a, b)`: the index of the largest logit. -/
def answer (a b : Nat) : Nat := Transformer.answer cfg tab a b

/-- The logit margin of the right answer over the best wrong one. -/
def margin (a b : Nat) : Int := Transformer.margin cfg tab a b

end Transformer.{name}
"""
    (root / "Weights.lean").write_text(body)


# ----------------------------------------------------------------------------------------------
# the bounds layer: tables_ok as many small kernel checks plus an ordinary assembly proof
#
# `decide +kernel` on the whole of `tablesOk tab bnd` is one kernel declaration over about 630,000 literals and
# its kernel caches grew to 15 GB (CI run 38995569877). Instead each table vector gets its own theorem
# `ok_<vector> : vecOk n k <vector> = true := by decide +kernel` (modules Net/B/*.lean, one per data file), and
# Net/Table.lean assembles `tables_ok` with `tablesOk_of` (Transformer/BoundsLib.lean) from the conjuncts of
# `tablesOk`; the numbers 114, 512, 113 below are the ones `tablesOk` itself states in Fast.lean.

NTOK, DI, DU = 114, 512, 113
G_COL_BOUND = 8774 * 2025  # chosenBounds.G in mathlib/Transformer/Logits.lean: sum_i |G i k| <= ||Wout|| ||U||


def refine_chain(pred, items):
    """A flat tactic proof of `List.all [items] pred = true` from `ok_<item>` for every item (no deep nesting)."""
    lines = [f"  refine all_cons_of ({pred}) {n} _ ok_{n} ?_" for n in items]
    return "\n".join(lines + ["  exact all_nil_true _"])


def b_header(name, imports):
    imps = "\n".join(["import Transformer.BoundsLib"] + [f"import Transformer.{name}.{m}" for m in imports])
    return f"""{imps}

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Transformer.{name}

"""


def counts_of(tb):
    """How many of each thing the tables hold (from the real tables, or from the committed sources)."""
    return {"heads": len(tb["TI0"]), "ntok": len(tb["TI0"][0]), "nG": len(tb["G"]), "ncol": len(tb["G"][0])}


def write_bounds(root, name, tb, shape=None):
    """Net/B/*.lean (one module per data file, one theorem per vector) and Net/Cols.lean (G column sums).
    `tb` needs kTI, kCI, kTU, kCU, kG and the table shapes; returns the list of B module names."""
    sh = shape or counts_of(tb)
    heads, ntok, nG, ncol = sh["heads"], sh["ntok"], sh["nG"], sh["ncol"]
    kTI, kCI, kTU, kCU, kG = (int(tb[k]) for k in ("kTI", "kCI", "kTU", "kCU", "kG"))
    b = root / "B"
    b.mkdir(exist_ok=True)
    mods = []

    def vec_thms(prefix, count, n, k):
        return "\n".join(f"theorem ok_{prefix}_{t} : vecOk {n} {k} {prefix}_{t} = true := by decide +kernel" for t in range(count))

    def head_block(key, h, n, k):
        pre = f"{key}_{h}"
        names = [f"{pre}_{t}" for t in range(ntok)]
        pred = f"vecOk {n} {k}"
        return f"""{vec_thms(pre, ntok, n, k)}

theorem ok_{pre} : ({pre}.length == {NTOK} && {pre}.all ({pred})) = true := by
  refine and_intro' (by decide +kernel) ?_
{refine_chain(pred, names)}
"""

    for key in ("TI0", "TI1"):
        for h in range(heads):
            m = f"{key}_{h}"
            (b / f"{m}.lean").write_text(b_header(name, [f"W.{m}"]) + head_block(key, h, DI, kTI) + f"\nend Transformer.{name}\n")
            mods.append(f"B.{m}")
    for key in ("TU0", "TU1"):
        body = "\n".join(head_block(key, h, DU, kTU) for h in range(heads))
        (b / f"{key}.lean").write_text(b_header(name, [f"W.{key}"]) + body + f"\nend Transformer.{name}\n")
        mods.append(f"B.{key}")
    # TI2, TU2 (one vector per head), CI, CU
    ti2 = [f"TI2_{h}" for h in range(heads)]
    tu2 = [f"TU2_{h}" for h in range(heads)]
    misc = f"""{vec_thms("TI2", heads, DI, kTI)}

theorem ok_TI2 : TI2.all (vecOk {DI} {kTI}) = true := by
{refine_chain(f"vecOk {DI} {kTI}", ti2)}

{vec_thms("TU2", heads, DU, kTU)}

theorem ok_TU2 : TU2.all (vecOk {DU} {kTU}) = true := by
{refine_chain(f"vecOk {DU} {kTU}", tu2)}

theorem ok_CI : vecOk {DI} {kCI} CI = true := by decide +kernel

theorem ok_CU : vecOk {DU} {kCU} CU = true := by decide +kernel
"""
    (b / "Misc.lean").write_text(b_header(name, ["W.Misc"]) + misc + f"\nend Transformer.{name}\n")
    mods.append("B.Misc")
    grows = [f"G_{i}" for i in range(nG)]
    gb = f"""{vec_thms("G", nG, DU, kG)}

theorem ok_G : G.all (vecOk {DU} {kG}) = true := by
{refine_chain(f"vecOk {DU} {kG}", grows)}
"""
    (b / "G.lean").write_text(b_header(name, ["W.Misc"]) + gb + f"\nend Transformer.{name}\n")
    mods.append("B.G")

    # column sums of G, one kernel check per column, each about 512 * (column + 1) steps
    cols = "\n\n".join(f"theorem ok_col_{k} : colAbsSum G {k} ≤ {G_COL_BOUND} := by decide +kernel" for k in range(ncol))
    cases = "\n".join(f"  | {k}, _ => exact ok_col_{k}" for k in range(ncol))
    (root / "Cols.lean").write_text(f"""import Transformer.BoundsLib
import Transformer.{name}.Weights

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Column sums of `G`

The Mathlib-side `Tables.Bounded chosenBounds` needs, for every column `k`, `sum_i |G i k| <= 8774 * 2025 = {G_COL_BOUND}`
(`chosenBounds.G` in `mathlib/Transformer/Logits.lean`); `tablesOk` gives only the per-entry bound, which times {nG} is too
weak. `colAbsSum G k` adds the absolute values of entry `k` of every row. One kernel check per column.
This is a statement about the core list table `tab.G`; its link to the Mathlib tables is not proved here.
-/

namespace Transformer.{name}

{cols}

theorem G_length : tab.G.length = {nG} := by decide +kernel

theorem colSums_ok : ∀ k, k < {ncol} → colAbsSum tab.G k ≤ {G_COL_BOUND} := by
  intro k hk
  match k, hk with
{cases}
  | n + {ncol}, h => exact absurd h (by omega)

end Transformer.{name}
""")
    return mods


def write_table(root, name, tb=None, shape=None):
    """Net/Table.lean: `tables_ok` from the pieces. The statement is unchanged: `tablesOk tab bnd = true`."""
    sh = shape or counts_of(tb)
    heads = sh["heads"]
    imports = ["Transformer.BoundsLib", f"Transformer.{name}.Weights"] + [f"Transformer.{name}.{m}" for m in B_MODULES(heads)]
    imp = "\n".join(f"import {i}" for i in imports)
    parts = []

    def per_head(tab_field, key, n, kfield):
        pred = f"fun h => h.length == {NTOK} && h.all (vecOk {n} bnd.{kfield})"
        items = [f"{key}_{h}" for h in range(heads)]
        typed = pred.replace("fun h =>", "fun (h : List (List Int)) =>", 1)  # the binder type is explicit so nothing waits on unification
        pre = "".join(f"  refine all_cons_of ({typed}) {m} _ ok_{m} ?_\n" for m in items)
        return f"""theorem tab_{key}_len : (tab.{key}.length == {heads}) = true := by decide +kernel

theorem tab_{key}_all : tab.{key}.all ({pred}) = true := by
{pre}  exact all_nil_true _
"""

    for key, n, kf in (("TI0", DI, "kTI"), ("TI1", DI, "kTI")):
        parts.append(per_head(key, key, n, kf))
    parts.append(f"""theorem tab_TI2_len : (tab.TI2.length == {heads}) = true := by decide +kernel

theorem tab_TI2_all : tab.TI2.all (vecOk {DI} bnd.kTI) = true := ok_TI2
""")
    for key, n, kf in (("TU0", DU, "kTU"), ("TU1", DU, "kTU")):
        parts.append(per_head(key, key, n, kf))
    parts.append(f"""theorem tab_TU2_len : (tab.TU2.length == {heads}) = true := by decide +kernel

theorem tab_TU2_all : tab.TU2.all (vecOk {DU} bnd.kTU) = true := ok_TU2
""")
    (root / "Table.lean").write_text(f"""{imp}

set_option maxRecDepth 100000

namespace Transformer.{name}

/-! `tables_ok` is `tablesOk tab bnd = true` exactly as before, but proved from one small kernel check per
table vector (`B/*.lean`), glued by `tablesOk_of` (`Transformer/BoundsLib.lean`). The per-vector theorems state the
bound as a numeral, `bnd` is a structure of the same numerals, and the unifier identifies them by unfolding `bnd`;
nothing here evaluates a table. -/

{chr(10).join(parts)}
/-- Every table has the right shape and its entries are within `bnd`: the one-time check the fast
evaluator's proof needs. -/
theorem tables_ok : tablesOk tab bnd = true :=
  tablesOk_of tab bnd tab_TI0_len tab_TI0_all tab_TI1_len tab_TI1_all tab_TI2_len tab_TI2_all
    tab_TU0_len tab_TU0_all tab_TU1_len tab_TU1_all tab_TU2_len tab_TU2_all
    ok_CI ok_CU ok_G

end Transformer.{name}
""")


def B_MODULES(heads):
    return ([f"B.TI0_{h}" for h in range(heads)] + [f"B.TI1_{h}" for h in range(heads)]
            + ["B.TU0", "B.TU1", "B.Misc", "B.G"])


def write_rows(root, name, rows_per_file):
    files = []
    starts = list(range(0, P, rows_per_file))
    for i, s in enumerate(starts):
        rs = list(range(s, min(s + rows_per_file, P)))
        body = []
        for a in rs:
            body.append(f"""/-- Row {a}: the packed program answers ({a} + b) % 113 with margin above 2E for every b, and its
digit checks pass; `fastCheck_correct` turns this into the statement about the model. -/
theorem fast_{a} : ∀ b, b < 113 → fastCheck cfg tab bnd E2 {a} b = true := by
  decide +kernel
""")
        (root / f"Rows{i:02d}.lean").write_text(f"""import Transformer.{name}.Table

/-! Rows {rs[0]} to {rs[-1]} of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

namespace Transformer.{name}

open Transformer

{chr(10).join(body)}
end Transformer.{name}
""")
        files.append(i)
    cases = "\n".join(f"  | {a}, _ => exact row_{a}" for a in range(P))
    rowthms = "\n".join(f"""theorem row_{a} : ∀ b, b < 113 → answer {a} b = ({a} + b) % 113 ∧ margin {a} b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 {a} b (by omega) hb tables_ok (fast_{a} b hb)""" for a in range(P))
    imports = "\n".join(f"import Transformer.{name}.Rows{i:02d}" for i in files)
    (root / "AllInputs.lean").write_text(f"""{imports}
import Transformer.Equiv

/-!
# The quantised transformer: right on every input, with margin

`adds_mod_113`: the model answers `(a + b) % 113` for all 12,769 pairs `(a, b)`.
`margin_ok`: on every pair the right logit exceeds the best wrong one by more than `2E`
(`E2 = 2E`, the constant of Theorem B2 in DESIGN.md).
-/

namespace Transformer.{name}

open Transformer

{rowthms}

theorem both : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 ∧ margin a b > E2 := by
  intro a ha
  match a, ha with
{cases}
  | n + 113, h => exact absurd h (by omega)

theorem adds_mod_113 : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 :=
  fun a ha b hb => (both a ha b hb).1

theorem margin_ok : ∀ a, a < 113 → ∀ b, b < 113 → margin a b > E2 :=
  fun a ha b hb => (both a ha b hb).2

end Transformer.{name}
""")
    return len(files)


def sources_shape(root, name):
    """The table constants and shapes read back from the committed Net/Weights.lean and Net/W/*.lean (no numerics)."""
    import re
    wl = (root / "Weights.lean").read_text()
    m = re.search(r"def bnd : Bnd := \{ kTI := (\d+), kCI := (\d+), kTU := (\d+), kCU := (\d+), kG := (\d+) \}", wl)
    if not m:
        raise SystemExit("Weights.lean: no `def bnd` line in the expected shape")
    ks = dict(zip(("kTI", "kCI", "kTU", "kCU", "kG"), map(int, m.groups())))
    w = root / "W"
    count = lambda f, pre: len(re.findall(rf"^def {pre}_\d+ :", (w / f).read_text(), re.M))
    ncol = len(re.findall(r"\(\.(?:ofNat|negSucc) \d+\)", re.search(r"^def G_0 : List Int := (.*)$", (w / "Misc.lean").read_text(), re.M).group(1)))
    shape = {"heads": len(list(w.glob("TI0_*.lean"))), "ntok": count("TI0_0.lean", "TI0_0"),
             "nG": count("Misc.lean", "G"), "ncol": ncol}
    return ks, shape


def write_manifest(root):
    """sha256 of every generated data file, so a bounds-only regeneration can show the numeric data did not change."""
    import hashlib
    lines = [f"{hashlib.sha256(p.read_bytes()).hexdigest()}  W/{p.name}" for p in sorted((root / "W").glob("*.lean"))]
    (root / "W.sha256").write_text("\n".join(lines) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("weights", nargs="?")
    ap.add_argument("--rows-per-file", type=int, default=1)
    ap.add_argument("--simulate", action="store_true")
    ap.add_argument("--sim-rows", type=int, default=P)
    ap.add_argument("--fault", nargs=4, metavar=("MATRIX", "I", "J", "DELTA"), default=None,
                    help="change raw integer weight MATRIX[I][J] (flattened indices after quantisation) by DELTA")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent / "lean"))
    ap.add_argument("--name", default="Net")
    ap.add_argument("--log", default=None)
    ap.add_argument("--bounds-only", action="store_true",
                    help="rewrite only Net/B/*, Net/Table.lean, Net/Cols.lean from the committed Net/Weights.lean and Net/W/*.lean "
                         "(no weights file, no numerics; the data files are not touched)")
    args = ap.parse_args()
    out = open(args.log, "a") if args.log else None

    def log(s):
        print(s, flush=True)
        if out:
            print(s, file=out, flush=True)

    root = Path(args.out) / "Transformer" / args.name
    if args.bounds_only:
        ks, shape = sources_shape(root, args.name)
        tb = dict(ks)
        mods = write_bounds(root, args.name, tb, shape)
        write_table(root, args.name, shape=shape)
        write_manifest(root)
        log(f"bounds-only: {ks}, shape {shape}; wrote {len(mods)} B modules, Table.lean, Cols.lean under {root}")
        return
    if not args.weights:
        ap.error("weights file required unless --bounds-only")
    W = it.load_weights(args.weights)
    Wq = it.quantise(W, Q)
    fault_note = ""
    if args.fault:
        mat, i, j, d = args.fault[0], int(args.fault[1]), int(args.fault[2]), int(args.fault[3])
        flat = Wq[mat].reshape(-1, Wq[mat].shape[-1])
        old = int(flat[i][j]); flat[i][j] = old + d
        fault_note = f" with one planted fault: raw weight {mat}[{i}][{j}] changed from {old} to {old + d}"
        log(f"fault: {mat}[{i}][{j}] {old} -> {old + d}")
    T, tb = tables_of(Wq)
    K = constants(Wq, T)
    log(f"tables: kTI {tb['kTI']} kCI {tb['kCI']} kTU {tb['kTU']} kCU {tb['kCU']} kG {tb['kG']}; delta {K['delta']}, E {K['E']} ({K['E'].bit_length()} bits)")
    if args.simulate:
        ok = simulate(tb, K, Wq, T, args.sim_rows, log)
        if not ok:
            log("simulation found mismatches" + (" (expected for a fault)" if args.fault else ""))
    root.mkdir(parents=True, exist_ok=True)
    write_weights(root, args.name, tb, K, Path(args.weights).name, fault_note)
    write_manifest(root)
    mods = write_bounds(root, args.name, tb)
    write_table(root, args.name, tb)
    nfiles = write_rows(root, args.name, args.rows_per_file)
    log(f"wrote {root}: Weights, {len(mods)} B modules, Table, Cols, {nfiles} row files, AllInputs, W.sha256")


if __name__ == "__main__":
    main()
