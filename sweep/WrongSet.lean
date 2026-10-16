import LeanCheckedNetwork.Fast

/-!
# Stating exactly where a network is wrong

A network that is wrong on some pairs still gets a kernel-checked statement: for every pair
`(a, b)`, its answer is `(a + b) % p` if and only if `(a, b)` is not in an explicit list. The
list is given row by row (`rowsToPairs` turns the per-row lists into the list of pairs), so
each row's check costs only that row's share.
-/

namespace LeanCheckedNetwork

/-- `rowsToPairs [bs0, bs1, ...] a0` is the list of `(a0 + i, b)` for every `b` in `bs_i`. -/
def rowsToPairs : List (List Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | bs :: rest, a => bs.map (fun b => (a, b)) ++ rowsToPairs rest (a + 1)

theorem mem_rowsToPairs (rows : List (List Nat)) (a0 x y : Nat) :
    (x, y) ∈ rowsToPairs rows a0 ↔ a0 ≤ x ∧ y ∈ rows.getD (x - a0) [] := by
  induction rows generalizing a0 with
  | nil => simp [rowsToPairs]
  | cons bs rest ih =>
    simp only [rowsToPairs, List.mem_append, List.mem_map, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨b, hb, rfl, rfl⟩ | ⟨h1, h2⟩)
      · simp [hb]
      · refine ⟨by omega, ?_⟩
        have : x - a0 = (x - (a0 + 1)) + 1 := by omega
        rw [this]; simpa using h2
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · left; exact ⟨y, by simpa using h2, rfl, rfl⟩
      · right
        refine ⟨hlt, ?_⟩
        have : x - a0 = (x - (a0 + 1)) + 1 := by omega
        rw [this] at h2; simpa using h2

/-- From the Boolean fact the kernel decides to the statement about the row. -/
theorem iff_not_mem_of_beq {x y : Nat} {L : List Nat} {b : Nat}
    (h : (x == y) = !L.contains b) : x = y ↔ b ∉ L := by
  constructor
  · intro hxy hb
    have : (x == y) = true := beq_iff_eq.mpr hxy
    rw [h] at this
    simp [hb] at this
  · intro hb
    apply beq_iff_eq.mp
    rw [h]
    simp [hb]

/-! ## The list of wrong pairs holds every pair once (added in review, 2026-10-16) -/

/-- Lexicographic order on pairs of naturals. -/
def lexLt (x y : Nat × Nat) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

/-- `true` when the list is strictly increasing in lexicographic order. One pass, so the kernel
decides it in time linear in the length of the list. -/
def strictLex : List (Nat × Nat) → Bool
  | (a, b) :: (c, d) :: rest => (a < c || (a == c && b < d)) && strictLex ((c, d) :: rest)
  | _ => true

theorem lexLt_trans {x y z : Nat × Nat} (h1 : lexLt x y) (h2 : lexLt y z) : lexLt x z := by
  unfold lexLt at *; omega

theorem lexLt_ne {x y : Nat × Nat} (h : lexLt x y) : x ≠ y := by
  intro e; subst e; unfold lexLt at h; omega

theorem strictLex_cons_cons {x y : Nat × Nat} {l : List (Nat × Nat)}
    (h : strictLex (x :: y :: l) = true) : lexLt x y ∧ strictLex (y :: l) = true := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [strictLex, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨by unfold lexLt; omega, h.2⟩

theorem pairwise_of_strictLex : ∀ (l : List (Nat × Nat)), strictLex l = true → l.Pairwise lexLt
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | x :: y :: l, h => by
    have ⟨hxy, hrest⟩ := strictLex_cons_cons h
    have ih := pairwise_of_strictLex (y :: l) hrest
    refine List.Pairwise.cons ?_ ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hxy
    · exact lexLt_trans hxy (List.rel_of_pairwise_cons ih hz')

/-- A strictly increasing list has no repeated entry. -/
theorem nodup_of_strictLex (l : List (Nat × Nat)) (h : strictLex l = true) : l.Nodup :=
  (pairwise_of_strictLex l h).imp lexLt_ne

end LeanCheckedNetwork
