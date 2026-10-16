The fast route from the repository, packed big numbers, one row at a time.

```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000
set_option Elab.async false


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

namespace LeanCheckedNetwork.Net

open LeanCheckedNetwork

theorem table_ok : tableOk W2 32 = true := by decide +kernel

theorem fast_0 : ∀ b, b < 23 →
    (fastOk E1 E2 32 0 b && fastAnswer E1 E2 W2 32 0 b == (0 + b) % 23) = true := by
  decide +kernel

theorem row_0 : ∀ b, b < 23 → answer 0 b = (0 + b) % 23 := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 0 b table_ok h.1, h.2]

theorem fast_1 : ∀ b, b < 23 →
    (fastOk E1 E2 32 1 b && fastAnswer E1 E2 W2 32 1 b == (1 + b) % 23) = true := by
  decide +kernel

theorem row_1 : ∀ b, b < 23 → answer 1 b = (1 + b) % 23 := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 1 b table_ok h.1, h.2]

theorem fast_2 : ∀ b, b < 23 →
    (fastOk E1 E2 32 2 b && fastAnswer E1 E2 W2 32 2 b == (2 + b) % 23) = true := by
  decide +kernel

theorem row_2 : ∀ b, b < 23 → answer 2 b = (2 + b) % 23 := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 2 b table_ok h.1, h.2]

theorem fast_3 : ∀ b, b < 23 →
    (fastOk E1 E2 32 3 b && fastAnswer E1 E2 W2 32 3 b == (3 + b) % 23) = true := by
  decide +kernel

theorem row_3 : ∀ b, b < 23 → answer 3 b = (3 + b) % 23 := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 3 b table_ok h.1, h.2]

theorem fast_4 : ∀ b, b < 23 →
    (fastOk E1 E2 32 4 b && fastAnswer E1 E2 W2 32 4 b == (4 + b) % 23) = true := by
  decide +kernel

theorem row_4 : ∀ b, b < 23 → answer 4 b = (4 + b) % 23 := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 4 b table_ok h.1, h.2]

theorem fast_5 : ∀ b, b < 23 →
    (fastOk E1 E2 32 5 b && fastAnswer E1 E2 W2 32 5 b == (5 + b) % 23) = true := by
  decide +kernel

theorem row_5 : ∀ b, b < 23 → answer 5 b = (5 + b) % 23 := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 5 b table_ok h.1, h.2]

theorem fast_6 : ∀ b, b < 23 →
    (fastOk E1 E2 32 6 b && fastAnswer E1 E2 W2 32 6 b == (6 + b) % 23) = true := by
  decide +kernel

theorem row_6 : ∀ b, b < 23 → answer 6 b = (6 + b) % 23 := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 6 b table_ok h.1, h.2]

theorem fast_7 : ∀ b, b < 23 →
    (fastOk E1 E2 32 7 b && fastAnswer E1 E2 W2 32 7 b == (7 + b) % 23) = true := by
  decide +kernel

theorem row_7 : ∀ b, b < 23 → answer 7 b = (7 + b) % 23 := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 7 b table_ok h.1, h.2]

theorem fast_8 : ∀ b, b < 23 →
    (fastOk E1 E2 32 8 b && fastAnswer E1 E2 W2 32 8 b == (8 + b) % 23) = true := by
  decide +kernel

theorem row_8 : ∀ b, b < 23 → answer 8 b = (8 + b) % 23 := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 8 b table_ok h.1, h.2]

theorem fast_9 : ∀ b, b < 23 →
    (fastOk E1 E2 32 9 b && fastAnswer E1 E2 W2 32 9 b == (9 + b) % 23) = true := by
  decide +kernel

theorem row_9 : ∀ b, b < 23 → answer 9 b = (9 + b) % 23 := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 9 b table_ok h.1, h.2]

theorem fast_10 : ∀ b, b < 23 →
    (fastOk E1 E2 32 10 b && fastAnswer E1 E2 W2 32 10 b == (10 + b) % 23) = true := by
  decide +kernel

theorem row_10 : ∀ b, b < 23 → answer 10 b = (10 + b) % 23 := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 10 b table_ok h.1, h.2]

theorem fast_11 : ∀ b, b < 23 →
    (fastOk E1 E2 32 11 b && fastAnswer E1 E2 W2 32 11 b == (11 + b) % 23) = true := by
  decide +kernel

theorem row_11 : ∀ b, b < 23 → answer 11 b = (11 + b) % 23 := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 11 b table_ok h.1, h.2]

theorem fast_12 : ∀ b, b < 23 →
    (fastOk E1 E2 32 12 b && fastAnswer E1 E2 W2 32 12 b == (12 + b) % 23) = true := by
  decide +kernel

theorem row_12 : ∀ b, b < 23 → answer 12 b = (12 + b) % 23 := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 12 b table_ok h.1, h.2]

theorem fast_13 : ∀ b, b < 23 →
    (fastOk E1 E2 32 13 b && fastAnswer E1 E2 W2 32 13 b == (13 + b) % 23) = true := by
  decide +kernel

theorem row_13 : ∀ b, b < 23 → answer 13 b = (13 + b) % 23 := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 13 b table_ok h.1, h.2]

theorem fast_14 : ∀ b, b < 23 →
    (fastOk E1 E2 32 14 b && fastAnswer E1 E2 W2 32 14 b == (14 + b) % 23) = true := by
  decide +kernel

theorem row_14 : ∀ b, b < 23 → answer 14 b = (14 + b) % 23 := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 14 b table_ok h.1, h.2]

theorem fast_15 : ∀ b, b < 23 →
    (fastOk E1 E2 32 15 b && fastAnswer E1 E2 W2 32 15 b == (15 + b) % 23) = true := by
  decide +kernel

theorem row_15 : ∀ b, b < 23 → answer 15 b = (15 + b) % 23 := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 15 b table_ok h.1, h.2]

theorem fast_16 : ∀ b, b < 23 →
    (fastOk E1 E2 32 16 b && fastAnswer E1 E2 W2 32 16 b == (16 + b) % 23) = true := by
  decide +kernel

theorem row_16 : ∀ b, b < 23 → answer 16 b = (16 + b) % 23 := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 16 b table_ok h.1, h.2]

theorem fast_17 : ∀ b, b < 23 →
    (fastOk E1 E2 32 17 b && fastAnswer E1 E2 W2 32 17 b == (17 + b) % 23) = true := by
  decide +kernel

theorem row_17 : ∀ b, b < 23 → answer 17 b = (17 + b) % 23 := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 17 b table_ok h.1, h.2]

theorem fast_18 : ∀ b, b < 23 →
    (fastOk E1 E2 32 18 b && fastAnswer E1 E2 W2 32 18 b == (18 + b) % 23) = true := by
  decide +kernel

theorem row_18 : ∀ b, b < 23 → answer 18 b = (18 + b) % 23 := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 18 b table_ok h.1, h.2]

theorem fast_19 : ∀ b, b < 23 →
    (fastOk E1 E2 32 19 b && fastAnswer E1 E2 W2 32 19 b == (19 + b) % 23) = true := by
  decide +kernel

theorem row_19 : ∀ b, b < 23 → answer 19 b = (19 + b) % 23 := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 19 b table_ok h.1, h.2]

theorem fast_20 : ∀ b, b < 23 →
    (fastOk E1 E2 32 20 b && fastAnswer E1 E2 W2 32 20 b == (20 + b) % 23) = true := by
  decide +kernel

theorem row_20 : ∀ b, b < 23 → answer 20 b = (20 + b) % 23 := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 20 b table_ok h.1, h.2]

theorem fast_21 : ∀ b, b < 23 →
    (fastOk E1 E2 32 21 b && fastAnswer E1 E2 W2 32 21 b == (21 + b) % 23) = true := by
  decide +kernel

theorem row_21 : ∀ b, b < 23 → answer 21 b = (21 + b) % 23 := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 21 b table_ok h.1, h.2]

theorem fast_22 : ∀ b, b < 23 →
    (fastOk E1 E2 32 22 b && fastAnswer E1 E2 W2 32 22 b == (22 + b) % 23) = true := by
  decide +kernel

theorem row_22 : ∀ b, b < 23 → answer 22 b = (22 + b) % 23 := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 32 22 b table_ok h.1, h.2]

theorem adds_mod_23 : ∀ a, a < 23 → ∀ b, b < 23 → answer a b = (a + b) % 23 := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_0
  | 1, _ => exact row_1
  | 2, _ => exact row_2
  | 3, _ => exact row_3
  | 4, _ => exact row_4
  | 5, _ => exact row_5
  | 6, _ => exact row_6
  | 7, _ => exact row_7
  | 8, _ => exact row_8
  | 9, _ => exact row_9
  | 10, _ => exact row_10
  | 11, _ => exact row_11
  | 12, _ => exact row_12
  | 13, _ => exact row_13
  | 14, _ => exact row_14
  | 15, _ => exact row_15
  | 16, _ => exact row_16
  | 17, _ => exact row_17
  | 18, _ => exact row_18
  | 19, _ => exact row_19
  | 20, _ => exact row_20
  | 21, _ => exact row_21
  | 22, _ => exact row_22
  | n + 23, h => exact absurd h (by omega)

end LeanCheckedNetwork.Net
```
