import Transformer.Fast

/-!
# Assembling `tablesOk` from small kernel-checked pieces

`tablesOk tab bnd = true` as one `decide +kernel` evaluates about 630,000 literals in a single kernel
declaration, and the kernel keeps every intermediate term of a declaration alive (CI run 38995569877:
resident memory reached 15 GB and the job was terminated). Here the check is split: one small
`decide +kernel` per table vector (`Transformer/Net/B/*.lean`, generated), and ordinary proofs that put
the pieces together. The statements are the ones `tablesOk` unfolds to; nothing is weakened.

* `and_intro'`, `all_cons_of`, `all_nil_true`: the Boolean glue;
* `tablesOk_of`: `tablesOk T bd = true` from its fifteen conjuncts, for arbitrary variables `T` and `bd`
  (so no table is ever evaluated while assembling);
* `colAbsSum`: the sum over the rows of `G` of the absolute value of the entry in a column.
-/

namespace Transformer

theorem and_intro' {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha
  subst hb
  rfl

theorem all_nil_true {α : Type} (p : α → Bool) : ([] : List α).all p = true := rfl

theorem all_cons_of {α : Type} (p : α → Bool) (a : α) (l : List α) (ha : p a = true)
    (hl : l.all p = true) : (a :: l).all p = true := by
  first
    | exact and_intro' ha hl
    | (rw [List.all_cons]; exact and_intro' ha hl)

/-- The fifteen conjuncts of `tablesOk`, in order. -/
theorem tablesOk_of (T : Tab) (bd : Bnd)
    (h1 : (T.TI0.length == 4) = true)
    (h2 : T.TI0.all (fun h => h.length == 114 && h.all (vecOk 512 bd.kTI)) = true)
    (h3 : (T.TI1.length == 4) = true)
    (h4 : T.TI1.all (fun h => h.length == 114 && h.all (vecOk 512 bd.kTI)) = true)
    (h5 : (T.TI2.length == 4) = true)
    (h6 : T.TI2.all (vecOk 512 bd.kTI) = true)
    (h7 : (T.TU0.length == 4) = true)
    (h8 : T.TU0.all (fun h => h.length == 114 && h.all (vecOk 113 bd.kTU)) = true)
    (h9 : (T.TU1.length == 4) = true)
    (h10 : T.TU1.all (fun h => h.length == 114 && h.all (vecOk 113 bd.kTU)) = true)
    (h11 : (T.TU2.length == 4) = true)
    (h12 : T.TU2.all (vecOk 113 bd.kTU) = true)
    (h13 : vecOk 512 bd.kCI T.CI = true)
    (h14 : vecOk 113 bd.kCU T.CU = true)
    (h15 : T.G.all (vecOk 113 bd.kG) = true) :
    tablesOk T bd = true := by
  unfold tablesOk
  exact and_intro' (and_intro' (and_intro' (and_intro' (and_intro' (and_intro' (and_intro'
    (and_intro' (and_intro' (and_intro' (and_intro' (and_intro' (and_intro' (and_intro' h1 h2) h3) h4) h5) h6) h7)
    h8) h9) h10) h11) h12) h13) h14) h15

/-- `sum_i |G i k|` for the rows `G`: the quantity the Mathlib-side bound `Tables.Bounded` asks to be small. -/
def colAbsSum : List (List Int) → Nat → Nat
  | [], _ => 0
  | r :: rs, k => (nth (0 : Int) r k).natAbs + colAbsSum rs k

end Transformer
