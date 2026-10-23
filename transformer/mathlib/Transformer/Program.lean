import Transformer.ExpFix

/-!
# The integer program of the one-layer transformer, as a function of twelve numbers

`transformer/DESIGN.md` section 6: everything linear that follows a token is a table, and the
per-pair program reads the tables, computes the twelve attention weights `e^h_j` (four heads,
three positions), the four softmax denominators `D^h = Σ_j e^h_j`, their product `D` and the
cofactors `c^h = Π_{h' ≠ h} D^{h'}`, and then

    pre_i = D CI_i + Σ_h c^h Σ_j e^h_j TI[h][j][tok_j]_i          (512 hidden units)
    m_i   = max 0 pre_i
    L_k   = D CU_k + S² Σ_h c^h Σ_j e^h_j TU[h][j][tok_j]_k + Σ_i m_i G_{i k}    (113 logits)

`logits` below is this program over any linearly ordered commutative ring, as a function of the
twelve numbers `e`. The integer run (`intLogits`) uses `e = expFix (s_j - max s)`; the real-exp
run (`realExpLogits`) uses `e = 2^f exp((s_j - max s) / 2^t)`. The scores `s_j = sc[h][j][tok_j]`
are the same integers in both.
-/

namespace Transformer

/-- The integer tables of DESIGN.md section 6 (`build_tables` in `int_transformer.py`). Position
`2` only ever holds the token `=` (113); the tables are indexed by all 114 tokens for uniformity. -/
structure Tables where
  sc : Fin 4 → Fin 3 → Fin 114 → ℤ
  TI : Fin 4 → Fin 3 → Fin 114 → Fin 512 → ℤ
  TU : Fin 4 → Fin 3 → Fin 114 → Fin 113 → ℤ
  CI : Fin 512 → ℤ
  CU : Fin 113 → ℤ
  G : Fin 512 → Fin 113 → ℤ

/-- The tokens at the three positions for the pair `(a, b)`: `a`, `b`, `=`. -/
def toks (a b : Fin 113) : Fin 3 → Fin 114 := ![a.castSucc, b.castSucc, 113]

section generic
variable {α : Type*} [CommRing α]

/-- `D^h = Σ_j e^h_j`. -/
def Dh (e : Fin 4 → Fin 3 → α) (h : Fin 4) : α := ∑ j, e h j

/-- `D = D^0 D^1 D^2 D^3`. -/
def Dprod (e : Fin 4 → Fin 3 → α) : α := Dh e 0 * Dh e 1 * Dh e 2 * Dh e 3

/-- `c^h = Π_{h' ≠ h} D^{h'}`, so that `c^h D^h = D`. -/
def cof (e : Fin 4 → Fin 3 → α) : Fin 4 → α
  | 0 => Dh e 1 * Dh e 2 * Dh e 3
  | 1 => Dh e 0 * Dh e 2 * Dh e 3
  | 2 => Dh e 0 * Dh e 1 * Dh e 3
  | 3 => Dh e 0 * Dh e 1 * Dh e 2

/-- `Σ_h c^h Σ_j e^h_j t_{h j}`: the attention term against a table slice `t`. -/
def att (e : Fin 4 → Fin 3 → α) (t : Fin 4 → Fin 3 → α) : α :=
  ∑ h, cof e h * ∑ j, e h j * t h j

/-- The pre-activation of hidden unit `i`. -/
def pre (T : Tables) (tok : Fin 3 → Fin 114) (e : Fin 4 → Fin 3 → α) (i : Fin 512) : α :=
  Dprod e * (T.CI i : α) + att e (fun h j => (T.TI h j (tok j) i : α))

/-- The hidden unit after the ReLU. -/
def hid [LinearOrder α] (T : Tables) (tok : Fin 3 → Fin 114) (e : Fin 4 → Fin 3 → α) (i : Fin 512) : α :=
  max 0 (pre T tok e i)

/-- The logit of answer `k`. -/
def logits [LinearOrder α] (T : Tables) (S : ℕ) (tok : Fin 3 → Fin 114) (e : Fin 4 → Fin 3 → α) (k : Fin 113) :
    α :=
  Dprod e * (T.CU k : α) + (S : α) ^ 2 * att e (fun h j => (T.TU h j (tok j) k : α))
    + ∑ i, hid T tok e i * (T.G i k : α)

theorem cof_mul_Dh (e : Fin 4 → Fin 3 → α) : ∀ h : Fin 4, cof e h * Dh e h = Dprod e
  | 0 => by simp only [cof, Dprod]; ring
  | 1 => by simp only [cof, Dprod]; ring
  | 2 => by simp only [cof, Dprod]; ring
  | 3 => by simp only [cof, Dprod]

end generic

/-- The integer program cast to the reals is the real program on the cast weights. -/
theorem logits_cast (T : Tables) (S : ℕ) (tok : Fin 3 → Fin 114) (e : Fin 4 → Fin 3 → ℤ)
    (k : Fin 113) :
    ((logits T S tok e k : ℤ) : ℝ) = logits T S tok (fun h j => (e h j : ℝ)) k := by
  have hDh : ∀ h, ((Dh e h : ℤ) : ℝ) = Dh (fun h j => (e h j : ℝ)) h := by
    intro h; unfold Dh; rw [Int.cast_sum]
  have hcof : ∀ h, ((cof e h : ℤ) : ℝ) = cof (fun h j => (e h j : ℝ)) h
    | 0 => by simp only [cof]; rw [Int.cast_mul, Int.cast_mul, hDh, hDh, hDh]
    | 1 => by simp only [cof]; rw [Int.cast_mul, Int.cast_mul, hDh, hDh, hDh]
    | 2 => by simp only [cof]; rw [Int.cast_mul, Int.cast_mul, hDh, hDh, hDh]
    | 3 => by simp only [cof]; rw [Int.cast_mul, Int.cast_mul, hDh, hDh, hDh]
  have hD : ((Dprod e : ℤ) : ℝ) = Dprod (fun h j => (e h j : ℝ)) := by
    unfold Dprod; rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, hDh, hDh, hDh, hDh]
  have hatt : ∀ (t : Fin 4 → Fin 3 → ℤ),
      ((att e t : ℤ) : ℝ) = att (fun h j => (e h j : ℝ)) (fun h j => (t h j : ℝ)) := by
    intro t; unfold att; rw [Int.cast_sum]
    apply Finset.sum_congr rfl; intro h _
    rw [Int.cast_mul, hcof, Int.cast_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    rw [Int.cast_mul]
  have hpre : ∀ i, ((pre T tok e i : ℤ) : ℝ) = pre T tok (fun h j => (e h j : ℝ)) i := by
    intro i; unfold pre; rw [Int.cast_add, Int.cast_mul, hD, hatt]; simp only [Int.cast_id]
  have hhid : ∀ i, ((hid T tok e i : ℤ) : ℝ) = hid T tok (fun h j => (e h j : ℝ)) i := by
    intro i; unfold hid; rw [Int.cast_max, hpre, Int.cast_zero]
  unfold logits
  simp only [Int.cast_id]
  rw [Int.cast_add, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_sum, hD, hatt,
    Int.cast_pow, Int.cast_natCast]
  have hsum : ∑ i, ((hid T tok e i * T.G i k : ℤ) : ℝ)
      = ∑ i, hid T tok (fun h j => (e h j : ℝ)) i * (T.G i k : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Int.cast_mul, hhid]
  rw [hsum]

/-- The largest of the three scores of head `h`. -/
def smax (T : Tables) (tok : Fin 3 → Fin 114) (h : Fin 4) : ℤ :=
  max (max (T.sc h 0 (tok 0)) (T.sc h 1 (tok 1))) (T.sc h 2 (tok 2))

/-- `s_j - max_j s_j ≤ 0`: the input of `expFix`. -/
def shifted (T : Tables) (tok : Fin 3 → Fin 114) (h : Fin 4) (j : Fin 3) : ℤ :=
  T.sc h j (tok j) - smax T tok h

theorem sc_le_smax (T : Tables) (tok : Fin 3 → Fin 114) (h : Fin 4) :
    ∀ j : Fin 3, T.sc h j (tok j) ≤ smax T tok h
  | 0 => (le_max_left _ _).trans (le_max_left _ _)
  | 1 => (le_max_right _ _).trans (le_max_left _ _)
  | 2 => le_max_right _ _

theorem shifted_nonpos (T : Tables) (tok : Fin 3 → Fin 114) (h : Fin 4) (j : Fin 3) :
    shifted T tok h j ≤ 0 :=
  sub_nonpos.2 (sc_le_smax T tok h j)

/-- The twelve integer attention weights: `expFix (s_j - max s)`. -/
def eInt (p : ExpParams) (T : Tables) (tok : Fin 3 → Fin 114) : Fin 4 → Fin 3 → ℤ :=
  fun h j => (expFix p (shifted T tok h j) : ℤ)

/-- The twelve real attention weights: `2^f exp ((s_j - max s) / 2^t)`. -/
noncomputable def eReal (p : ExpParams) (T : Tables) (tok : Fin 3 → Fin 114) :
    Fin 4 → Fin 3 → ℝ :=
  fun h j => 2 ^ p.f * Real.exp ((shifted T tok h j : ℝ) / 2 ^ p.t)

/-- The integer program's logits on the pair `(a, b)`: what the kernel evaluates. -/
def intLogits (p : ExpParams) (T : Tables) (S : ℕ) (a b : Fin 113) : Fin 113 → ℤ :=
  logits T S (toks a b) (eInt p T (toks a b))

/-- The same program with the exact real exponential in place of `expFix`. -/
noncomputable def realExpLogits (p : ExpParams) (T : Tables) (S : ℕ) (a b : Fin 113) :
    Fin 113 → ℝ :=
  logits T S (toks a b) (eReal p T (toks a b))

/-- The right answer: `(a + b) % 113`, which is addition in `Fin 113`. -/
def ans (a b : Fin 113) : Fin 113 := a + b

theorem ans_val (a b : Fin 113) : (ans a b : ℕ) = (a + b) % 113 := Fin.val_add a b

section argmax
variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- Scan the indices in `l`, keeping the first index of the largest value seen so far
(the rule of `argmaxFrom` in `lean/LeanCheckedNetwork/Network.lean`: move only on a strict increase). -/
def argmaxFrom (L : Fin n → α) : List (Fin n) → Fin n → Fin n
  | [], best => best
  | i :: is, best => argmaxFrom L is (if L best < L i then i else best)

/-- The index of the largest entry, the first one on a tie. -/
def argmaxFirst (L : Fin (n + 1) → α) : Fin (n + 1) := argmaxFrom L (List.finRange (n + 1)) 0

theorem argmaxFrom_stay (L : Fin n → α) (r : Fin n) (hr : ∀ k, L k ≤ L r) :
    ∀ l : List (Fin n), argmaxFrom L l r = r := by
  intro l
  induction l with
  | nil => rfl
  | cons i is ih =>
    simp only [argmaxFrom]
    have hni : ¬ (L r < L i) := not_lt.2 (hr i)
    simp only [hni, ite_false]
    exact ih

theorem argmaxFrom_eq_of_mem (L : Fin n → α) (r : Fin n) (hr : ∀ k, k ≠ r → L k < L r) :
    ∀ (l : List (Fin n)) (best : Fin n), r ∈ l → argmaxFrom L l best = r := by
  have hle : ∀ k, L k ≤ L r := by
    intro k
    by_cases hk : k = r
    · rw [hk]
    · exact (hr k hk).le
  intro l
  induction l with
  | nil => intro best h; simp at h
  | cons i is ih =>
    intro best hmem
    simp only [argmaxFrom]
    by_cases hri : r ∈ is
    · exact ih _ hri
    · have hi : i = r := by
        rcases List.mem_cons.1 hmem with h | h
        · exact h.symm
        · exact absurd h hri
      subst hi
      have : (if L best < L i then i else best) = i := by
        by_cases hb : best = i
        · rw [hb]; simp
        · have hlt : L best < L i := hr best hb
          simp only [hlt, ite_true]
      rw [this]
      exact argmaxFrom_stay L i hle is

/-- If `r` is the strict maximum of `L`, `argmaxFirst L = r`. -/
theorem argmaxFirst_eq (L : Fin (n + 1) → α) (r : Fin (n + 1)) (hr : ∀ k, k ≠ r → L k < L r) :
    argmaxFirst L = r :=
  argmaxFrom_eq_of_mem L r hr _ 0 (List.mem_finRange r)

end argmax

end Transformer
