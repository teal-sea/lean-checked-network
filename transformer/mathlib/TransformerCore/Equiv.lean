import TransformerCore.Fast

/-!
# The packed evaluator agrees with the plain program

`fastCheck_correct`: when `tablesOk` holds and `fastCheck K T bd E2 a b` passes, the plain
program's answer is `(a + b) % 113` and its margin exceeds `E2`. The proof is linear algebra on
lists: `pkI` is additive and commutes with scalars (so the packed `pre` and logits are `pkI` of the
plain ones), every entry of `pre` and of the logits is bounded by the shift `K` the evaluator adds
(so the shifted digits are natural numbers below `B` and are read back exactly), ReLU is the
truncated subtraction of the shift, and the argmax and the margin do not see a shift of every logit
by the same amount. Nothing here is trusted beyond Lean's kernel.
-/

namespace TransformerCore

/-! ## Packing and unpacking -/

theorem unpk_pk (ds : List Nat) (h : ∀ d ∈ ds, d < B) : unpk ds.length (pk ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d < B := h d (by simp)
    simp only [List.length_cons, unpk, pk]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ B_pos,
      Nat.div_eq_of_lt hd, Nat.zero_add, ih (fun x hx => h x (by simp [hx]))]

theorem unpkSub_eq (n N K : Nat) : unpkSub n N K = (unpk n N).map (· - K) := by
  induction n generalizing N with
  | zero => rfl
  | succ n ih => simp [unpkSub, unpk, ih]

theorem length_unpk (n N : Nat) : (unpk n N).length = n := by
  induction n generalizing N with
  | zero => rfl
  | succ n ih => simp [unpk, ih]

theorem pkI_map_ofNat (ds : List Nat) : pkI (ds.map Int.ofNat) = Int.ofNat (pk ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, pkI, pk, ih, Int.add_def, Int.mul_def, Int.ofNat_eq_coe, Int.natCast_add, Int.natCast_mul]

theorem pkI_vadd (u v : List Int) : pkI (vadd u v) = Int.add (pkI u) (pkI v) := by
  induction u generalizing v with
  | nil => cases v <;> simp [vadd, pkI]
  | cons x xs ih =>
    cases v with
    | nil => simp [vadd, pkI]
    | cons y ys =>
      simp only [vadd, pkI, ih]
      simp only [Int.add_def, Int.mul_def, Int.mul_add]
      omega

theorem pkI_smulN (c : Nat) (v : List Int) : pkI (smulN c v) = nmul c (pkI v) := by
  induction v with
  | nil => simp [smulN, pkI, nmul]
  | cons x xs ih =>
    simp only [smulN, List.map_cons, pkI, nmul] at ih ⊢
    rw [ih]
    simp only [Int.add_def, Int.mul_def, Int.mul_add, Int.mul_left_comm (Int.ofNat c) (Int.ofNat B)]

theorem pkI_headVec (e : Nat × Nat × Nat) (v0 v1 v2 : List Int) :
    pkI (headVec e v0 v1 v2) = headPk e v0 v1 v2 := by
  simp only [headVec, headPk, pkI_vadd, pkI_smulN]

theorem pkI_lincombN (cs : List Nat) (rs : List (List Int)) :
    pkI (lincombN cs rs) = dotNI cs (rs.map pkI) := by
  induction cs generalizing rs with
  | nil => cases rs <;> simp [lincombN, dotNI, pkI]
  | cons c cs ih =>
    cases rs with
    | nil => simp [lincombN, dotNI, pkI]
    | cons r rs => simp only [lincombN, List.map_cons, dotNI, pkI_vadd, pkI_smulN, ih, nmul]

theorem pkI_map_add (v : List Int) (k : Int) :
    pkI (v.map (· + k)) = pkI v + k * pkI (List.replicate v.length 1) := by
  induction v with
  | nil => simp [pkI]
  | cons x xs ih =>
    simp only [List.map_cons, List.length_cons, List.replicate, pkI, ih]
    simp only [Int.add_def, Int.mul_def, Int.mul_add, Int.mul_one, Int.mul_left_comm k (Int.ofNat B)]
    omega

theorem ones_eq (n : Nat) : Int.ofNat (ones n) = pkI (List.replicate n (1 : Int)) := by
  rw [ones, ← pkI_map_ofNat, List.map_replicate]; rfl

/-! ## Bounds on entries -/

/-- Every entry of `v` is in `[-k, k]`. -/
def AbsBnd (k : Nat) (v : List Int) : Prop := ∀ x ∈ v, -(k : Int) ≤ x ∧ x ≤ k

theorem absBnd_mono {k k' : Nat} {v : List Int} (h : AbsBnd k v) (hk : k ≤ k') : AbsBnd k' v := by
  intro x hx
  have := h x hx
  omega

theorem absBnd_nil (k : Nat) : AbsBnd k [] := by intro x hx; simp at hx

theorem absBnd_smulN (c k : Nat) (v : List Int) (h : AbsBnd k v) : AbsBnd (c * k) (smulN c v) := by
  intro x hx
  simp only [smulN, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := h y hy
  have hc : (0 : Int) ≤ Int.ofNat c := Int.natCast_nonneg c
  constructor
  · have := Int.mul_le_mul_of_nonneg_left hy'.1 hc
    simp only [Int.mul_def, Int.mul_neg] at this ⊢
    simpa using this
  · have := Int.mul_le_mul_of_nonneg_left hy'.2 hc
    simpa using this

theorem absBnd_vadd (k1 k2 : Nat) (u v : List Int) (hu : AbsBnd k1 u) (hv : AbsBnd k2 v) :
    AbsBnd (k1 + k2) (vadd u v) := by
  induction u generalizing v with
  | nil => cases v <;> simp only [vadd] <;> exact absBnd_mono hv (by omega)
  | cons x xs ih =>
    cases v with
    | nil => simp only [vadd]; exact absBnd_mono hu (by omega)
    | cons y ys =>
      simp only [vadd]
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · have h1 := hu x (by simp); have h2 := hv y (by simp)
        simp only [Int.add_def]; omega
      · exact ih ys (fun w hw => hu w (by simp [hw])) (fun w hw => hv w (by simp [hw])) z hz

theorem absBnd_headVec (e : Nat × Nat × Nat) (k : Nat) (v0 v1 v2 : List Int)
    (h0 : AbsBnd k v0) (h1 : AbsBnd k v1) (h2 : AbsBnd k v2) :
    AbsBnd (headK e k) (headVec e v0 v1 v2) := by
  unfold headVec headK
  exact absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ h0)
    (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ h1) (absBnd_smulN _ _ _ h2))

theorem absBnd_lincombN (cs : List Nat) (rs : List (List Int)) (Kc k : Nat)
    (hc : ∀ c ∈ cs, c ≤ Kc) (hr : ∀ r ∈ rs, AbsBnd k r) :
    AbsBnd (cs.length * Kc * k) (lincombN cs rs) := by
  induction cs generalizing rs with
  | nil => cases rs <;> exact absBnd_nil _
  | cons c cs ih =>
    cases rs with
    | nil => exact absBnd_nil _
    | cons r rs =>
      simp only [lincombN, List.length_cons]
      have hb := absBnd_vadd _ _ _ _ (absBnd_smulN c k r (hr r (by simp)))
        (ih rs (fun x hx => hc x (by simp [hx])) (fun x hx => hr x (by simp [hx])))
      refine absBnd_mono hb ?_
      have : c ≤ Kc := hc c (by simp)
      have h1 : c * k ≤ Kc * k := Nat.mul_le_mul_right k this
      calc c * k + cs.length * Kc * k ≤ Kc * k + cs.length * Kc * k := by omega
        _ = (cs.length + 1) * Kc * k := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega

theorem vecOk_iff (n k : Nat) (v : List Int) : vecOk n k v = true ↔ v.length = n ∧ AbsBnd k v := by
  simp only [vecOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, AbsBnd]
  constructor
  · rintro ⟨hl, hb⟩
    refine ⟨hl, fun x hx => ?_⟩
    have := hb x hx
    simp only [Int.ofNat_eq_coe] at this
    omega
  · rintro ⟨hl, hb⟩
    refine ⟨hl, fun x hx => ?_⟩
    have := hb x hx
    simp only [Int.ofNat_eq_coe]
    omega

/-! ## Lengths and membership -/

theorem length_smulN (c : Nat) (v : List Int) : (smulN c v).length = v.length := by
  simp [smulN]

theorem length_vadd (u v : List Int) : (vadd u v).length = max u.length v.length := by
  induction u generalizing v with
  | nil => cases v <;> simp [vadd]
  | cons x xs ih =>
    cases v with
    | nil => simp [vadd]
    | cons y ys => simp only [vadd, List.length_cons, ih]; omega

theorem length_lincombN_le (cs : List Nat) (rs : List (List Int)) (n : Nat)
    (hr : ∀ r ∈ rs, r.length ≤ n) : (lincombN cs rs).length ≤ n := by
  induction cs generalizing rs with
  | nil => cases rs <;> simp [lincombN]
  | cons c cs ih =>
    cases rs with
    | nil => simp [lincombN]
    | cons r rs =>
      simp only [lincombN, length_vadd, length_smulN]
      have := hr r (by simp)
      have := ih rs (fun x hx => hr x (by simp [hx]))
      omega

theorem nth_mem {α : Type} (d : α) (l : List α) (i : Nat) (hi : i < l.length) : nth d l i ∈ l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [nth]
    | succ i => simp only [nth, List.mem_cons]; exact Or.inr (ih i (by simpa using hi))

theorem all_nth {α : Type} (p : α → Bool) (d : α) (l : List α) (i : Nat) (hi : i < l.length)
    (h : l.all p = true) : p (nth d l i) = true := by
  simp only [List.all_eq_true] at h
  exact h _ (nth_mem d l i hi)

theorem nth_map {α β : Type} (f : α → β) (d : α) (l : List α) (i : Nat) :
    nth (f d) (l.map f) i = f (nth d l i) := by
  induction l generalizing i with
  | nil => simp [nth]
  | cons x xs ih => cases i <;> simp [nth, ih]

/-! ## Digits -/

theorem digits_eq (v : List Int) (K : Nat) (hb : AbsBnd K v) (hB : 2 * K < B) :
    unpk v.length (Int.toNat (pkI v + K * pkI (List.replicate v.length 1))) =
      v.map (fun x : Int => (x + (K : Int)).toNat) := by
  have h1 : pkI v + K * pkI (List.replicate v.length 1) = pkI (v.map (· + (K : Int))) :=
    (pkI_map_add v K).symm
  have h2 : v.map (· + (K : Int)) = (v.map (fun x : Int => (x + (K : Int)).toNat)).map Int.ofNat := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have := hb x hx
    simp only [Function.comp, Int.ofNat_eq_coe]
    omega
  rw [h1, h2, pkI_map_ofNat]
  show unpk _ (pk _) = _
  have hlen : v.length = (v.map (fun x : Int => (x + (K : Int)).toNat)).length := by simp
  rw [hlen]
  apply unpk_pk
  intro d hd
  simp only [List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  have := hb x hx
  omega

theorem relu_digits (v : List Int) (K : Nat) (hb : AbsBnd K v) (hB : 2 * K < B) :
    unpkSub v.length (Int.toNat (pkI v + K * pkI (List.replicate v.length 1))) K = v.map Int.toNat := by
  rw [unpkSub_eq, digits_eq v K hb hB, List.map_map]
  apply List.map_congr_left
  intro x hx
  have := hb x hx
  simp only [Function.comp, Int.ofNat_eq_coe]
  omega

theorem shifted_digits (v : List Int) (K : Nat) (hb : AbsBnd K v) (hB : 2 * K < B) :
    (unpk v.length (Int.toNat (pkI v + K * pkI (List.replicate v.length 1)))).map Int.ofNat =
      v.map (· + (K : Int)) := by
  rw [digits_eq v K hb hB, List.map_map]
  apply List.map_congr_left
  intro x hx
  have := hb x hx
  simp only [Function.comp, Int.ofNat_eq_coe]
  omega

/-! ## Argmax and margin: natural versus integer digits, and shifts -/

theorem argmaxFrom_shift (xs : List Int) (K : Int) (i bi : Nat) (bv : Int) :
    argmaxFrom (xs.map (· + K)) i bi (bv + K) = argmaxFrom xs i bi bv := by
  induction xs generalizing i bi bv with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, argmaxFrom]
    have e : (bv + K < x + K) ↔ bv < x := by omega
    by_cases hlt : bv < x <;> simp [e, hlt, ih]

theorem argmax_shift (xs : List Int) (K : Int) : argmax (xs.map (· + K)) = argmax xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [List.map_cons, argmax, argmaxFrom_shift]

theorem argmaxFromN_eq (xs : List Nat) (i bi bv : Nat) :
    argmaxFromN xs i bi bv = argmaxFrom (xs.map Int.ofNat) i bi (Int.ofNat bv) := by
  induction xs generalizing i bi bv with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, argmaxFromN, argmaxFrom]
    have e : (Int.ofNat bv < Int.ofNat x) ↔ bv < x := by simp only [Int.ofNat_eq_coe]; omega
    by_cases hlt : bv < x <;> simp [e, hlt, ih]

theorem argmaxN_eq (xs : List Nat) : argmaxN xs = argmax (xs.map Int.ofNat) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [List.map_cons, argmaxN, argmax, argmaxFromN_eq]

theorem maxI_shift (a b K : Int) : maxI (a + K) (b + K) = maxI a b + K := by
  simp only [maxI]
  have e : (a + K < b + K) ↔ a < b := by omega
  by_cases h : a < b <;> simp [e, h]

theorem maxExceptFrom_shift (xs : List Int) (K : Int) (i c : Nat) (acc : Int) :
    maxExceptFrom (xs.map (· + K)) i c (acc + K) = maxExceptFrom xs i c acc + K := by
  induction xs generalizing i acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxExceptFrom]
    by_cases h : i = c
    · simp [h, ih]
    · simp only [h, ↓reduceIte]
      rw [maxI_shift]
      exact ih _ _

theorem nth_map_add (L : List Int) (K : Int) (j : Nat) (hj : j < L.length) :
    nth 0 (L.map (· + K)) j = nth 0 L j + K := by
  induction L generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp [nth]
    | succ j => simp only [List.map_cons, nth]; exact ih j (by simpa using hj)

theorem maxExcept_shift (L : List Int) (K : Int) (c : Nat) (hc : (if c = 0 then 1 else 0) < L.length) :
    maxExcept (L.map (· + K)) c = maxExcept L c + K := by
  simp only [maxExcept]
  rw [nth_map_add L K _ hc, maxExceptFrom_shift]

theorem maxN_eq (a b : Nat) : Int.ofNat (maxN a b) = maxI (Int.ofNat a) (Int.ofNat b) := by
  simp only [maxN, maxI]
  have e : (Int.ofNat a < Int.ofNat b) ↔ a < b := by simp only [Int.ofNat_eq_coe]; omega
  by_cases h : a < b <;> simp [e, h]

theorem maxExceptFromN_eq (xs : List Nat) (i c acc : Nat) :
    Int.ofNat (maxExceptFromN xs i c acc) = maxExceptFrom (xs.map Int.ofNat) i c (Int.ofNat acc) := by
  induction xs generalizing i acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxExceptFromN, maxExceptFrom]
    simp only [Int.ofNat_eq_coe] at ih ⊢
    by_cases h : i = c
    · simp only [h, ↓reduceIte]; exact ih _ _
    · simp only [h, ↓reduceIte]
      have := maxN_eq acc x
      simp only [Int.ofNat_eq_coe] at this
      rw [← this]; exact ih _ _

theorem nthN_eq (ds : List Nat) (j : Nat) : Int.ofNat (nth 0 ds j) = nth 0 (ds.map Int.ofNat) j := by
  have := nth_map Int.ofNat 0 ds j
  simpa using this.symm

theorem maxExceptN_eq (ds : List Nat) (c : Nat) :
    Int.ofNat (maxExceptN ds c) = maxExcept (ds.map Int.ofNat) c := by
  simp only [maxExceptN, maxExcept, maxExceptFromN_eq, nthN_eq]

/-! ## The tables -/

theorem tablesOk_facts (T : Tab) (bd : Bnd) (ht : tablesOk T bd = true) (h tok : Nat) (hh : h < 4) (htok : tok < 114) :
    vecOk 512 bd.kTI (nth [] (nth [] T.TI0 h) tok) = true ∧
    vecOk 512 bd.kTI (nth [] (nth [] T.TI1 h) tok) = true ∧
    vecOk 512 bd.kTI (nth [] T.TI2 h) = true ∧
    vecOk 113 bd.kTU (nth [] (nth [] T.TU0 h) tok) = true ∧
    vecOk 113 bd.kTU (nth [] (nth [] T.TU1 h) tok) = true ∧
    vecOk 113 bd.kTU (nth [] T.TU2 h) = true := by
  simp only [tablesOk, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨l0, a0⟩, l1⟩, a1⟩, l2⟩, a2⟩, l3⟩, a3⟩, l4⟩, a4⟩, l5⟩, a5⟩, _⟩, _⟩, _⟩ := ht
  have f0 := all_nth _ [] T.TI0 h (by omega) a0
  have f1 := all_nth _ [] T.TI1 h (by omega) a1
  have f3 := all_nth _ [] T.TU0 h (by omega) a3
  have f4 := all_nth _ [] T.TU1 h (by omega) a4
  simp only [Bool.and_eq_true, beq_iff_eq] at f0 f1 f3 f4
  refine ⟨all_nth _ [] _ tok (by omega) f0.2, all_nth _ [] _ tok (by omega) f1.2,
    all_nth _ [] T.TI2 h (by omega) a2, all_nth _ [] _ tok (by omega) f3.2,
    all_nth _ [] _ tok (by omega) f4.2, all_nth _ [] T.TU2 h (by omega) a5⟩

theorem tablesOk_const (T : Tab) (bd : Bnd) (ht : tablesOk T bd = true) :
    vecOk 512 bd.kCI T.CI = true ∧ vecOk 113 bd.kCU T.CU = true ∧ ∀ r ∈ T.G, vecOk 113 bd.kG r = true := by
  simp only [tablesOk, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨_, hCI⟩, hCU⟩, hG⟩ := ht
  exact ⟨hCI, hCU, by simpa [List.all_eq_true] using hG⟩

/-- From the digits of the shifted logits to the plain answer. -/
theorem answer_from_digits (d : List Nat) (L : List Int) (KL : Nat) (hd : d.map Int.ofNat = L.map (· + (KL : Int)))
    (right : Nat) (hans : argmaxN d = right) : argmax L = right := by
  rw [argmaxN_eq, hd, argmax_shift] at hans
  exact hans

/-- From the digits of the shifted logits to the plain margin. -/
theorem margin_from_digits (d : List Nat) (L : List Int) (KL c E2 : Nat) (hd : d.map Int.ofNat = L.map (· + (KL : Int)))
    (hc : c < L.length) (h2 : (if c = 0 then 1 else 0) < L.length)
    (hmar : maxExceptN d c + E2 < nth 0 d c) : (E2 : Int) < Int.sub (nth 0 L c) (maxExcept L c) := by
  have h1 : Int.ofNat (maxExceptN d c) = maxExcept L c + KL := by
    rw [maxExceptN_eq, hd, maxExcept_shift L KL c h2]
  have h3 : Int.ofNat (nth 0 d c) = nth 0 L c + KL := by
    rw [nthN_eq, hd, nth_map_add L KL c hc]
  simp only [Int.ofNat_eq_coe] at h1 h3
  show (E2 : Int) < nth 0 L c - maxExcept L c
  omega

/-! ## The main theorem -/

/-- The bounds on one head's three vectors, as `AbsBnd`, with their lengths. -/
theorem head_bnd (n k : Nat) (v0 v1 v2 : List Int) (h0 : vecOk n k v0 = true) (h1 : vecOk n k v1 = true)
    (h2 : vecOk n k v2 = true) (e : Nat × Nat × Nat) :
    AbsBnd (headK e k) (headVec e v0 v1 v2) ∧ (headVec e v0 v1 v2).length = n := by
  rw [vecOk_iff] at h0 h1 h2
  refine ⟨absBnd_headVec e k v0 v1 v2 h0.2 h1.2 h2.2, ?_⟩
  simp [headVec, length_vadd, length_smulN, h0.1, h1.1, h2.1]

theorem fastCheck_correct (K : Cfg) (T : Tab) (bd : Bnd) (E2 a b : Nat) (ha : a < 113) (hb : b < 113)
    (ht : tablesOk T bd = true) (h : fastCheck K T bd E2 a b = true) :
    answer K T a b = (a + b) % 113 ∧ margin K T a b > E2 := by
  -- the table vectors this pair uses
  obtain ⟨i00, i01, i02, u00, u01, u02⟩ := tablesOk_facts T bd ht 0 a (by omega) (by omega)
  obtain ⟨i10, _, i12, u10, _, u12⟩ := tablesOk_facts T bd ht 1 a (by omega) (by omega)
  obtain ⟨i20, _, i22, u20, _, u22⟩ := tablesOk_facts T bd ht 2 a (by omega) (by omega)
  obtain ⟨i30, _, i32, u30, _, u32⟩ := tablesOk_facts T bd ht 3 a (by omega) (by omega)
  obtain ⟨_, i01, _, _, u01, _⟩ := tablesOk_facts T bd ht 0 b (by omega) (by omega)
  obtain ⟨_, i11, _, _, u11, _⟩ := tablesOk_facts T bd ht 1 b (by omega) (by omega)
  obtain ⟨_, i21, _, _, u21, _⟩ := tablesOk_facts T bd ht 2 b (by omega) (by omega)
  obtain ⟨_, i31, _, _, u31, _⟩ := tablesOk_facts T bd ht 3 b (by omega) (by omega)
  obtain ⟨hCI, hCU, hG⟩ := tablesOk_const T bd ht
  -- name the shared quantities
  unfold answer margin logits preAct headI headU
  dsimp only
  unfold fastCheck at h
  simp only [] at h
  generalize headE K T a b 0 = E0 at h ⊢
  generalize headE K T a b 1 = E1 at h ⊢
  generalize headE K T a b 2 = E2' at h ⊢
  generalize headE K T a b 3 = E3 at h ⊢
  generalize dens E0 E1 E2' E3 = dc at h ⊢
  generalize nth [] (nth [] T.TI0 0) a = v00 at h i00 ⊢
  generalize nth [] (nth [] T.TI0 1) a = v10 at h i10 ⊢
  generalize nth [] (nth [] T.TI0 2) a = v20 at h i20 ⊢
  generalize nth [] (nth [] T.TI0 3) a = v30 at h i30 ⊢
  generalize nth [] (nth [] T.TI1 0) b = v01 at h i01 ⊢
  generalize nth [] (nth [] T.TI1 1) b = v11 at h i11 ⊢
  generalize nth [] (nth [] T.TI1 2) b = v21 at h i21 ⊢
  generalize nth [] (nth [] T.TI1 3) b = v31 at h i31 ⊢
  generalize nth [] T.TI2 0 = v02 at h i02 ⊢
  generalize nth [] T.TI2 1 = v12 at h i12 ⊢
  generalize nth [] T.TI2 2 = v22 at h i22 ⊢
  generalize nth [] T.TI2 3 = v32 at h i32 ⊢
  generalize nth [] (nth [] T.TU0 0) a = w00 at h u00 ⊢
  generalize nth [] (nth [] T.TU0 1) a = w10 at h u10 ⊢
  generalize nth [] (nth [] T.TU0 2) a = w20 at h u20 ⊢
  generalize nth [] (nth [] T.TU0 3) a = w30 at h u30 ⊢
  generalize nth [] (nth [] T.TU1 0) b = w01 at h u01 ⊢
  generalize nth [] (nth [] T.TU1 1) b = w11 at h u11 ⊢
  generalize nth [] (nth [] T.TU1 2) b = w21 at h u21 ⊢
  generalize nth [] (nth [] T.TU1 3) b = w31 at h u31 ⊢
  generalize nth [] T.TU2 0 = w02 at h u02 ⊢
  generalize nth [] T.TU2 1 = w12 at h u12 ⊢
  generalize nth [] T.TU2 2 = w22 at h u22 ⊢
  generalize nth [] T.TU2 3 = w32 at h u32 ⊢
  -- pre: bound, length, packed form
  obtain ⟨b0, l0⟩ := head_bnd 512 bd.kTI v00 v01 v02 i00 i01 i02 E0
  obtain ⟨b1, l1⟩ := head_bnd 512 bd.kTI v10 v11 v12 i10 i11 i12 E1
  obtain ⟨b2, l2⟩ := head_bnd 512 bd.kTI v20 v21 v22 i20 i21 i22 E2'
  obtain ⟨b3, l3⟩ := head_bnd 512 bd.kTI v30 v31 v32 i30 i31 i32 E3
  rw [vecOk_iff] at hCI hCU
  generalize hpre : vadd (smulN dc.1 T.CI) (vadd (smulN dc.2.1 (headVec E0 v00 v01 v02))
    (vadd (smulN dc.2.2.1 (headVec E1 v10 v11 v12))
      (vadd (smulN dc.2.2.2.1 (headVec E2' v20 v21 v22)) (smulN dc.2.2.2.2 (headVec E3 v30 v31 v32))))) = pre
  generalize hKp : dc.1 * bd.kCI + (dc.2.1 * headK E0 bd.kTI + (dc.2.2.1 * headK E1 bd.kTI +
    (dc.2.2.2.1 * headK E2' bd.kTI + dc.2.2.2.2 * headK E3 bd.kTI))) = Kp at h
  have preB : AbsBnd Kp pre := by
    rw [← hpre, ← hKp]
    exact absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ hCI.2)
      (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ b0)
        (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ b1)
          (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ b2) (absBnd_smulN _ _ _ b3))))
  have preL : pre.length = 512 := by
    rw [← hpre]; simp [length_vadd, length_smulN, hCI.1, l0, l1, l2, l3]
  have preP : pkI pre = Int.add (nmul dc.1 (pkI T.CI))
      (Int.add (nmul dc.2.1 (headPk E0 v00 v01 v02))
        (Int.add (nmul dc.2.2.1 (headPk E1 v10 v11 v12))
          (Int.add (nmul dc.2.2.2.1 (headPk E2' v20 v21 v22)) (nmul dc.2.2.2.2 (headPk E3 v30 v31 v32))))) := by
    rw [← hpre]; simp only [pkI_vadd, pkI_smulN, pkI_headVec]
  -- the checks
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hKB, hLB⟩, hans⟩, hmar⟩ := h
  -- the hidden layer
  have hm : unpkSub 512 (Int.toNat (Int.add (pkI pre) (nmul Kp (Int.ofNat (ones 512))))) Kp = pre.map Int.toNat := by
    have := relu_digits pre Kp preB hKB
    rw [preL] at this
    rw [← this, ones_eq, ← preL]
    rfl
  rw [preP] at hm
  rw [hm] at hans hmar
  -- the logits: bound, length, packed form
  obtain ⟨c0, m0⟩ := head_bnd 113 bd.kTU w00 w01 w02 u00 u01 u02 E0
  obtain ⟨c1, m1⟩ := head_bnd 113 bd.kTU w10 w11 w12 u10 u11 u12 E1
  obtain ⟨c2, m2⟩ := head_bnd 113 bd.kTU w20 w21 w22 u20 u21 u22 E2'
  obtain ⟨c3, m3⟩ := head_bnd 113 bd.kTU w30 w31 w32 u30 u31 u32 E3
  generalize hL : vadd (smulN dc.1 T.CU)
    (vadd (smulN K.S2 (vadd (smulN dc.2.1 (headVec E0 w00 w01 w02))
        (vadd (smulN dc.2.2.1 (headVec E1 w10 w11 w12))
          (vadd (smulN dc.2.2.2.1 (headVec E2' w20 w21 w22)) (smulN dc.2.2.2.2 (headVec E3 w30 w31 w32))))))
      (lincombN (pre.map Int.toNat) T.G)) = L
  generalize hKL : dc.1 * bd.kCU + (K.S2 * (dc.2.1 * headK E0 bd.kTU + (dc.2.2.1 * headK E1 bd.kTU +
    (dc.2.2.2.1 * headK E2' bd.kTU + dc.2.2.2.2 * headK E3 bd.kTU))) + 512 * Kp * bd.kG) = KL at hLB hmar hans
  have hGb : ∀ r ∈ T.G, AbsBnd bd.kG r := fun r hr => ((vecOk_iff _ _ _).1 (hG r hr)).2
  have hGl : ∀ r ∈ T.G, r.length ≤ 113 := fun r hr => Nat.le_of_eq ((vecOk_iff _ _ _).1 (hG r hr)).1
  have hmc : ∀ c ∈ pre.map Int.toNat, c ≤ Kp := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    have := preB x hx
    omega
  have LB : AbsBnd KL L := by
    have hl := absBnd_lincombN (pre.map Int.toNat) T.G Kp bd.kG hmc hGb
    rw [List.length_map, preL] at hl
    rw [← hL, ← hKL]
    exact absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ hCU.2)
      (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _
        (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ c0)
          (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ c1)
            (absBnd_vadd _ _ _ _ (absBnd_smulN _ _ _ c2) (absBnd_smulN _ _ _ c3))))) hl)
  have LL : L.length = 113 := by
    have := length_lincombN_le (pre.map Int.toNat) T.G 113 hGl
    rw [← hL]; simp only [length_vadd, length_smulN, hCU.1, m0, m1, m2, m3]
    omega
  have LP : pkI L = Int.add (nmul dc.1 (pkI T.CU))
      (Int.add (nmul K.S2
          (Int.add (nmul dc.2.1 (headPk E0 w00 w01 w02))
            (Int.add (nmul dc.2.2.1 (headPk E1 w10 w11 w12))
              (Int.add (nmul dc.2.2.2.1 (headPk E2' w20 w21 w22)) (nmul dc.2.2.2.2 (headPk E3 w30 w31 w32))))))
        (dotNI (pre.map Int.toNat) (T.G.map pkI))) := by
    rw [← hL]; simp only [pkI_vadd, pkI_smulN, pkI_headVec, pkI_lincombN]
  have hd : (unpk 113 (Int.toNat (Int.add (pkI L) (nmul KL (Int.ofNat (ones 113)))))).map Int.ofNat =
      L.map (· + (KL : Int)) := by
    have := shifted_digits L KL LB hLB
    rw [LL] at this
    rw [← this, ones_eq, ← LL]
    rfl
  rw [LP] at hd
  -- conclude
  refine ⟨answer_from_digits _ L KL hd _ hans, margin_from_digits _ L KL ((a + b) % 113) E2 hd ?_ ?_ hmar⟩
  · rw [LL]; omega
  · rw [LL]; split <;> omega

end TransformerCore
