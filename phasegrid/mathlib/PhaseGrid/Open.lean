import PhaseGrid.FullSetEven
import PhaseGrid.P7FullTables
import PhaseGrid.P7Link

/-!
# Open statements: what this package states but does not prove

Nothing here is a theorem with a placeholder proof: each open item is a `def` of type `Prop`, a
statement with no proof attached. No declaration in the package has a placeholder proof.
-/

namespace PhaseGrid

/-! The first session listed here `tablesMatchP7`, that the stage 3 tables at `p = 7` equal the rounded
exact cosines `E1 7 [1, 2, 3] 25` and so on. It is now the theorem `PhaseGrid.tablesMatchP7` in
`P7Link.lean`, with `P7FullTables.adds_mod_7_by_theorem` and `P7FullTables.adds_mod_7_by_full`. -/

/-! OPEN, stated in words because the objects are not in this package: the stage 3 tables
`PhaseGridInstances.P113Full.E1`, `E2`, `W2` (all 56 frequencies, `M = 25`) and
`PhaseGridInstances.P113Nanda5.E1`, `E2`, `W2` (Nanda's five, `M = 30`) are within `1/2` of `M cos(…)`
entry by entry, which is the hypothesis `adds_mod_p_tables` needs to prove them right without
enumeration. Certifying it needs `cos(2πr/113)` for `r = 1, …, 56` to about `3e-5` (the smallest distance
of a weight from a half-integer is `7.5e-4` at scale `25`), by the method of `P7Link.lean` with more
precision; not done. At `p = 113` the brute-force route of stage 3 is the proof.

Correction recorded 2026-10-16 by the adversarial review: this file used to state the item as
`def tablesClose113 : Prop := ∀ a, a < 113 → ∀ n ∈ neurons (List.range' 1 56),
|((E1 113 (List.range' 1 56) 25).getD a []).getD (idx n) 0 - 25 * rE1 113 a n| ≤ 1/2`.
That compares the stage 2 table `E1 113 … 25`, which is `round (25 cos …)` by definition, with
`25 cos …`, and never mentions the stage 3 tables (they are not in this package); it is true by
`abs_sub_round` plus a `decide` on the index bookkeeping, and was proved that way in the review
(`review-general/tablesClose113_trivial.lean`, axioms `[propext, Classical.choice, Quot.sound]`).
The `def` is removed so that nothing here is listed as open while being trivially provable. -/

/-- OPEN. The derived bound `24 |S| < M g(S)` is sufficient but loose: measured in stage 1, the full
frequency set adds mod `p` already at `M = 1` for every odd `p` tested (7, 11, 97, 113, 257) and at
`M = 2` for `p = 12`, where the bound asks for `M ≥ 24` or `25`. Stated here for all odd `p ≥ 5`; not proved, and not
tested beyond the moduli listed. -/
def fullSetWorksAtTwo : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ a, a < 2 * m + 1 → ∀ b, b < 2 * m + 1 →
    answer (2 * m + 1) (List.range' 1 m) 2 a b = (a + b) % (2 * m + 1)

end PhaseGrid
