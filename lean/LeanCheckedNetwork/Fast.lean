import LeanCheckedNetwork.Network

/-!
# A faster evaluator for the kernel, proved to give the same answer

Lean's kernel spends about the same time on each small arithmetic step, so the plain network
(`answer`, about 14,500 multiply-adds per input) is slow to check on all 12,769 inputs. This
file computes the same answer with a few hundred big-number steps per input instead.

The idea: write all 113 scores as the digits of one large number in base `B = 2^32`. Adding
neuron `h`'s contribution to every score at once is then a single multiplication and addition
of large numbers. Reading the digits back gives every score, shifted up by the same constant
(the weights are shifted to be non-negative), and a shift by a constant does not change which
score is largest.

`answer_eq_fastAnswer` proves that `fastAnswer` equals `answer` whenever the cheap checks in
`fastOk` pass. Nothing here is trusted beyond Lean's kernel.
-/

namespace LeanCheckedNetwork

/-- The base of the packed representation. -/
def B : Nat := 4294967296

theorem B_pos : 0 < B := by decide

/-- Digits `[d0, d1, ...]` packed as `d0 + B * (d1 + B * (...))`. -/
def pk : List Nat → Nat
  | [] => 0
  | d :: ds => d + B * pk ds

/-- The first `n` base-`B` digits of `N`. -/
def unpk : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, N => N % B :: unpk n (N / B)

theorem unpk_pk (ds : List Nat) (h : ∀ d ∈ ds, d < B) : unpk ds.length (pk ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d < B := h d (by simp)
    simp only [List.length_cons, unpk, pk]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ B_pos,
      Nat.div_eq_of_lt hd, Nat.zero_add, ih (fun x hx => h x (by simp [hx]))]

/-- Dot product on natural numbers. -/
def dotN : List Nat → List Nat → Nat
  | x :: xs, y :: ys => x * y + dotN xs ys
  | _, _ => 0

/-- Pack the columns of a table: entry `h` is `pk` of column `h`, built row by row. -/
def colsPk : List (List Nat) → List Nat → List Nat
  | [], z => z
  | r :: rs, z => List.zipWith (fun x c => x + B * c) r (colsPk rs z)

theorem dotN_zeros (y : List Nat) (n : Nat) : dotN y (List.replicate n 0) = 0 := by
  induction y generalizing n with
  | nil => cases n <;> rfl
  | cons a ys ih => cases n with
    | zero => rfl
    | succ n => simp [List.replicate, dotN, ih]

theorem dotN_zipWith (y r C : List Nat) (hl : r.length = C.length) :
    dotN y (List.zipWith (fun x c => x + B * c) r C) = dotN y r + B * dotN y C := by
  induction y generalizing r C with
  | nil => cases r <;> cases C <;> simp [dotN]
  | cons a ys ih =>
    cases r with
    | nil => cases C with
      | nil => simp [dotN]
      | cons _ _ => simp at hl
    | cons x rs =>
      cases C with
      | nil => simp at hl
      | cons c cs =>
        simp only [List.zipWith_cons_cons, dotN]
        rw [ih rs cs (by simpa using hl)]
        simp only [Nat.mul_add]
        rw [Nat.mul_left_comm a B c]
        omega

theorem colsPk_length (rs : List (List Nat)) (z : List Nat) (H : Nat)
    (hr : ∀ r ∈ rs, r.length = H) (hz : z.length = H) : (colsPk rs z).length = H := by
  induction rs with
  | nil => simpa [colsPk] using hz
  | cons r rs ih =>
    simp only [colsPk, List.length_zipWith]
    rw [hr r (by simp), ih (fun x hx => hr x (by simp [hx]))]
    simp

/-- The packed accumulation equals the packed list of all dot products. -/
theorem dotN_colsPk (y : List Nat) (rs : List (List Nat)) (H : Nat)
    (hr : ∀ r ∈ rs, r.length = H) :
    dotN y (colsPk rs (List.replicate H 0)) = pk (rs.map (dotN y)) := by
  induction rs with
  | nil => simp [colsPk, pk, dotN_zeros]
  | cons r rs ih =>
    have hrs : ∀ x ∈ rs, x.length = H := fun x hx => hr x (by simp [hx])
    simp only [colsPk, List.map_cons, pk]
    rw [dotN_zipWith _ _ _ (by rw [hr r (by simp), colsPk_length rs _ H hrs (by simp)]), ih hrs]

theorem dotN_le (y w : List Nat) (m : Nat) (hw : ∀ x ∈ w, x ≤ m) : dotN y w ≤ m * y.sum := by
  induction y generalizing w with
  | nil => cases w <;> simp [dotN]
  | cons a ys ih =>
    cases w with
    | nil => simp [dotN]
    | cons x ws =>
      simp only [dotN, List.sum_cons, Nat.mul_add]
      have h1 : a * x ≤ m * a := by
        rw [Nat.mul_comm m a]; exact Nat.mul_le_mul_left a (hw x (by simp))
      have h2 := ih ws (fun z hz => hw z (by simp [hz]))
      omega

/-! ## From integers to the packed natural numbers -/

/-- Shift an integer weight in `[-128, 127]` to a natural number in `[0, 255]`. -/
def shiftW (w : Int) : Nat := (w + 128).toNat

theorem dot_shift (h w : List Int) (hl : w.length = h.length)
    (hh : ∀ x ∈ h, 0 ≤ x) (hw : ∀ x ∈ w, -128 ≤ x) :
    ((dotN (h.map Int.toNat) (w.map shiftW) : Nat) : Int) = dot w h + 128 * h.sum := by
  induction h generalizing w with
  | nil => cases w <;> simp_all [dotN, dot]
  | cons a hs ih =>
    cases w with
    | nil => simp at hl
    | cons x ws =>
      have ha : 0 ≤ a := hh a (by simp)
      have hx : -128 ≤ x := hw x (by simp)
      simp only [List.map_cons, dotN, dot, List.sum_cons]
      rw [Int.natCast_add, Int.natCast_mul, ih ws (by simpa using hl)
        (fun z hz => hh z (by simp [hz])) (fun z hz => hw z (by simp [hz]))]
      simp only [shiftW, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (by omega : 0 ≤ x + 128)]
      show a * (x + 128) + (dot ws hs + 128 * hs.sum) = x * a + dot ws hs + 128 * (a + hs.sum)
      rw [Int.mul_add, Int.mul_add, Int.mul_comm a x, Int.mul_comm a 128]
      omega

theorem scores_eq_map (h : List Int) (W : List (List Int)) :
    scores h W = W.map (fun w => dot w h) := by
  induction W with
  | nil => rfl
  | cons w ws ih => simp [scores, ih]

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

/-! ## The fast evaluator -/

/-- The network's answer, computed with packed big numbers. -/
def fastAnswer (E1 E2 W2 : List (List Int)) (H : Nat) (a b : Nat) : Nat :=
  let y := (hidden (nth E1 a) (nth E2 b)).map Int.toNat
  let C := colsPk (W2.map (·.map shiftW)) (List.replicate H 0)
  argmax ((unpk W2.length (dotN y C)).map Int.ofNat)

/-- Cheap checks under which `fastAnswer` is exact. -/
def fastOk (E1 E2 : List (List Int)) (H : Nat) (a b : Nat) : Bool :=
  let h := hidden (nth E1 a) (nth E2 b)
  h.length == H && h.all (0 ≤ ·) && decide (255 * (h.map Int.toNat).sum < B)

/-- Checks on the read-out table, done once: every row has length `H`, every entry in `[-128, 127]`. -/
def tableOk (W2 : List (List Int)) (H : Nat) : Bool :=
  W2.all (fun r => r.length == H && r.all (fun x => decide (-128 ≤ x) && decide (x ≤ 127)))

theorem answer_eq_fastAnswer (E1 E2 W2 : List (List Int)) (H a b : Nat)
    (ht : tableOk W2 H = true) (hf : fastOk E1 E2 H a b = true) :
    answer E1 E2 W2 a b = fastAnswer E1 E2 W2 H a b := by
  simp only [tableOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  unfold fastAnswer answer
  simp only [fastOk] at hf
  generalize hidden (nth E1 a) (nth E2 b) = h at hf ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨hlen, hnn⟩, hbound⟩ := hf
  have hrows : ∀ r ∈ W2.map (·.map shiftW), r.length = H := by
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    simp [(ht w hw).1]
  have hdig : ∀ d ∈ (W2.map (·.map shiftW)).map (dotN (h.map Int.toNat)), d < B := by
    intro d hd
    simp only [List.map_map, List.mem_map, Function.comp] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    have hle : dotN (h.map Int.toNat) (w.map shiftW) ≤ 255 * (h.map Int.toNat).sum := by
      apply dotN_le
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      have := (ht w hw).2 v hv
      simp only [shiftW]; omega
    omega
  dsimp only
  rw [dotN_colsPk _ _ H hrows]
  have hlen2 : ((W2.map (·.map shiftW)).map (dotN (h.map Int.toNat))).length = W2.length := by simp
  rw [← hlen2, unpk_pk _ hdig, scores_eq_map, ← argmax_shift _ (128 * h.sum)]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp]
  exact (dot_shift h w (by rw [(ht w hw).1, hlen]) hnn (fun x hx => ((ht w hw).2 x hx).1)).symm

end LeanCheckedNetwork
