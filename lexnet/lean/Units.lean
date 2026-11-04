/- Generic lemmas about clipped threshold units.  No weights appear here. -/
namespace Units
def clip1 (x : Int) : Int := min 1 (max 0 x)
def ge (p a : Int) : Int := min 1 (max (0 : Int) (p + 1 * a))
def le (q a : Int) : Int := min 1 (max (0 : Int) (q + (-1) * a))
def ind (a c : Int) : Int := if a = c then 1 else 0
def lin (b : Int) : List (Int × Int) → Int
  | [] => b
  | (w, v) :: t => lin (b + w * v) t
def pairsOf (cs : List Int) (a : Int) : List (Int × Int) :=
  cs.flatMap fun c => [(1, ge (1 - c) a), (1, le (c + 1) a)]
def rowA (cs : List Int) (a b : Int) : Int :=
  clip1 (lin (-(cs.length : Int)) (pairsOf cs a ++ [(-1, b)]))
def rowAB (ca cb a b : Int) : Int :=
  clip1 (lin (-3) [(1, ge (1 - ca) a), (1, le (ca + 1) a), (1, ge (1 - cb) b), (1, le (cb + 1) b)])
def rowBA (cb ca b a : Int) : Int :=
  clip1 (lin (-3) [(1, ge (1 - cb) b), (1, le (cb + 1) b), (1, ge (1 - ca) a), (1, le (ca + 1) a)])

theorem ind01 (a c : Int) : 0 ≤ ind a c ∧ ind a c ≤ 1 := by unfold ind; split <;> omega
theorem ind_eq1 (a c : Int) : ind a c = 1 ↔ a = c := by unfold ind; split <;> omega

theorem pair_unit (c a : Int) : ge (1 - c) a + le (c + 1) a = 1 + ind a c := by
  unfold ge le ind; split <;> omega

theorem lin_eq (L : List (Int × Int)) : ∀ b, lin b L = b + (L.map fun p => p.1 * p.2).sum := by
  induction L with
  | nil => intro b; simp [lin]
  | cons p t ih => intro b; simp only [lin, ih, List.map_cons, List.sum_cons]; omega

theorem sum_pairs (cs : List Int) (a : Int) :
    ((pairsOf cs a).map fun p => p.1 * p.2).sum = cs.length + (cs.map (ind a)).sum := by
  induction cs with
  | nil => simp [pairsOf]
  | cons c t ih =>
    have := pair_unit c a
    simp only [pairsOf, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.length_cons] at ih ⊢
    omega

theorem count_le_one (cs : List Int) (hn : cs.Nodup) (a : Int) :
    (cs.map (ind a)).sum = if a ∈ cs then 1 else 0 := by
  induction cs with
  | nil => simp
  | cons c t ih =>
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.sum_cons, ih hn.2]
    by_cases h : a = c
    · subst h; simp [ind, hn.1]
    · have : ind a c = 0 := by simp [ind, h]
      rw [this]; by_cases h2 : a ∈ t <;> simp [h, h2]

theorem rowA_iff (cs : List Int) (hn : cs.Nodup) (a b : Int) (hb : 0 ≤ b) :
    rowA cs a b = 1 ↔ (a ∈ cs ∧ b = 0) := by
  unfold rowA
  rw [lin_eq, List.map_append, List.sum_append, sum_pairs, count_le_one cs hn]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, clip1]
  by_cases h : a ∈ cs <;> simp [h] <;> omega

theorem rowA_01 (cs : List Int) (a b : Int) : rowA cs a b = 0 ∨ rowA cs a b = 1 := by
  unfold rowA clip1; omega

theorem rowAB_iff (ca cb a b : Int) : rowAB ca cb a b = 1 ↔ (a = ca ∧ b = cb) := by
  have h1 := pair_unit ca a; have h2 := pair_unit cb b
  have h3 := ind_eq1 a ca; have h4 := ind_eq1 b cb
  have h5 := ind01 a ca; have h6 := ind01 b cb
  unfold rowAB; simp only [lin, clip1]; omega

theorem rowBA_iff (cb ca b a : Int) : rowBA cb ca b a = 1 ↔ (a = ca ∧ b = cb) := by
  have h1 := pair_unit ca a; have h2 := pair_unit cb b
  have h3 := ind_eq1 a ca; have h4 := ind_eq1 b cb
  have h5 := ind01 a ca; have h6 := ind01 b cb
  unfold rowBA; simp only [lin, clip1]; omega
theorem rowAB_01 (ca cb a b : Int) : rowAB ca cb a b = 0 ∨ rowAB ca cb a b = 1 := by
  unfold rowAB clip1; simp only [lin]; omega
theorem rowBA_01 (cb ca b a : Int) : rowBA cb ca b a = 0 ∨ rowBA cb ca b a = 1 := by
  unfold rowBA clip1; simp only [lin]; omega

theorem grp_iff (rs : List Int) (h01 : ∀ r ∈ rs, r = 0 ∨ r = 1) :
    clip1 (lin 0 (rs.map fun r => (1, r))) = 1 ↔ ∃ r ∈ rs, r = 1 := by
  rw [lin_eq]
  have e : (List.map (fun p : Int × Int => p.1 * p.2) (List.map (fun r => ((1 : Int), r)) rs)).sum = rs.sum := by
    simp [List.map_map, Function.comp_def]
  rw [e]
  have key : ∀ rs : List Int, (∀ r ∈ rs, r = 0 ∨ r = 1) →
      (0 ≤ rs.sum ∧ ((1 ≤ rs.sum) ↔ ∃ r ∈ rs, r = 1)) := by
    intro rs
    induction rs with
    | nil => intro _; simp
    | cons r t ih =>
      intro h
      have h1 := h r (List.mem_cons_self ..)
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.sum_cons, List.mem_cons, exists_eq_or_imp]
      obtain ⟨h2a, h2b⟩ := h2
      rcases h1 with h1 | h1 <;> subst h1
      · simp; refine ⟨h2a, ?_⟩; simpa using h2b
      · simp; omega
  obtain ⟨k1, k2⟩ := key rs h01
  unfold clip1; rw [← k2]; omega
end Units
