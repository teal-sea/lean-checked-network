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

theorem table_ok : tableOk W2 128 = true := by decide +kernel

theorem fast_0 : ∀ b, b < 113 →
    (fastOk E1 E2 128 0 b && fastAnswer E1 E2 W2 128 0 b == (0 + b) % 113) = true := by
  decide +kernel

theorem row_0 : ∀ b, b < 113 → answer 0 b = (0 + b) % 113 := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 0 b table_ok h.1, h.2]

theorem fast_1 : ∀ b, b < 113 →
    (fastOk E1 E2 128 1 b && fastAnswer E1 E2 W2 128 1 b == (1 + b) % 113) = true := by
  decide +kernel

theorem row_1 : ∀ b, b < 113 → answer 1 b = (1 + b) % 113 := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 1 b table_ok h.1, h.2]

theorem fast_2 : ∀ b, b < 113 →
    (fastOk E1 E2 128 2 b && fastAnswer E1 E2 W2 128 2 b == (2 + b) % 113) = true := by
  decide +kernel

theorem row_2 : ∀ b, b < 113 → answer 2 b = (2 + b) % 113 := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 2 b table_ok h.1, h.2]

theorem fast_3 : ∀ b, b < 113 →
    (fastOk E1 E2 128 3 b && fastAnswer E1 E2 W2 128 3 b == (3 + b) % 113) = true := by
  decide +kernel

theorem row_3 : ∀ b, b < 113 → answer 3 b = (3 + b) % 113 := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 3 b table_ok h.1, h.2]

theorem fast_4 : ∀ b, b < 113 →
    (fastOk E1 E2 128 4 b && fastAnswer E1 E2 W2 128 4 b == (4 + b) % 113) = true := by
  decide +kernel

theorem row_4 : ∀ b, b < 113 → answer 4 b = (4 + b) % 113 := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 4 b table_ok h.1, h.2]

theorem fast_5 : ∀ b, b < 113 →
    (fastOk E1 E2 128 5 b && fastAnswer E1 E2 W2 128 5 b == (5 + b) % 113) = true := by
  decide +kernel

theorem row_5 : ∀ b, b < 113 → answer 5 b = (5 + b) % 113 := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 5 b table_ok h.1, h.2]

theorem fast_6 : ∀ b, b < 113 →
    (fastOk E1 E2 128 6 b && fastAnswer E1 E2 W2 128 6 b == (6 + b) % 113) = true := by
  decide +kernel

theorem row_6 : ∀ b, b < 113 → answer 6 b = (6 + b) % 113 := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 6 b table_ok h.1, h.2]

theorem fast_7 : ∀ b, b < 113 →
    (fastOk E1 E2 128 7 b && fastAnswer E1 E2 W2 128 7 b == (7 + b) % 113) = true := by
  decide +kernel

theorem row_7 : ∀ b, b < 113 → answer 7 b = (7 + b) % 113 := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 7 b table_ok h.1, h.2]

theorem fast_8 : ∀ b, b < 113 →
    (fastOk E1 E2 128 8 b && fastAnswer E1 E2 W2 128 8 b == (8 + b) % 113) = true := by
  decide +kernel

theorem row_8 : ∀ b, b < 113 → answer 8 b = (8 + b) % 113 := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 8 b table_ok h.1, h.2]

theorem fast_9 : ∀ b, b < 113 →
    (fastOk E1 E2 128 9 b && fastAnswer E1 E2 W2 128 9 b == (9 + b) % 113) = true := by
  decide +kernel

theorem row_9 : ∀ b, b < 113 → answer 9 b = (9 + b) % 113 := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 9 b table_ok h.1, h.2]

theorem fast_10 : ∀ b, b < 113 →
    (fastOk E1 E2 128 10 b && fastAnswer E1 E2 W2 128 10 b == (10 + b) % 113) = true := by
  decide +kernel

theorem row_10 : ∀ b, b < 113 → answer 10 b = (10 + b) % 113 := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 10 b table_ok h.1, h.2]

theorem fast_11 : ∀ b, b < 113 →
    (fastOk E1 E2 128 11 b && fastAnswer E1 E2 W2 128 11 b == (11 + b) % 113) = true := by
  decide +kernel

theorem row_11 : ∀ b, b < 113 → answer 11 b = (11 + b) % 113 := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 11 b table_ok h.1, h.2]

theorem fast_12 : ∀ b, b < 113 →
    (fastOk E1 E2 128 12 b && fastAnswer E1 E2 W2 128 12 b == (12 + b) % 113) = true := by
  decide +kernel

theorem row_12 : ∀ b, b < 113 → answer 12 b = (12 + b) % 113 := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 12 b table_ok h.1, h.2]

theorem fast_13 : ∀ b, b < 113 →
    (fastOk E1 E2 128 13 b && fastAnswer E1 E2 W2 128 13 b == (13 + b) % 113) = true := by
  decide +kernel

theorem row_13 : ∀ b, b < 113 → answer 13 b = (13 + b) % 113 := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 13 b table_ok h.1, h.2]

theorem fast_14 : ∀ b, b < 113 →
    (fastOk E1 E2 128 14 b && fastAnswer E1 E2 W2 128 14 b == (14 + b) % 113) = true := by
  decide +kernel

theorem row_14 : ∀ b, b < 113 → answer 14 b = (14 + b) % 113 := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 14 b table_ok h.1, h.2]

theorem fast_15 : ∀ b, b < 113 →
    (fastOk E1 E2 128 15 b && fastAnswer E1 E2 W2 128 15 b == (15 + b) % 113) = true := by
  decide +kernel

theorem row_15 : ∀ b, b < 113 → answer 15 b = (15 + b) % 113 := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 15 b table_ok h.1, h.2]

theorem fast_16 : ∀ b, b < 113 →
    (fastOk E1 E2 128 16 b && fastAnswer E1 E2 W2 128 16 b == (16 + b) % 113) = true := by
  decide +kernel

theorem row_16 : ∀ b, b < 113 → answer 16 b = (16 + b) % 113 := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 16 b table_ok h.1, h.2]

theorem fast_17 : ∀ b, b < 113 →
    (fastOk E1 E2 128 17 b && fastAnswer E1 E2 W2 128 17 b == (17 + b) % 113) = true := by
  decide +kernel

theorem row_17 : ∀ b, b < 113 → answer 17 b = (17 + b) % 113 := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 17 b table_ok h.1, h.2]

theorem fast_18 : ∀ b, b < 113 →
    (fastOk E1 E2 128 18 b && fastAnswer E1 E2 W2 128 18 b == (18 + b) % 113) = true := by
  decide +kernel

theorem row_18 : ∀ b, b < 113 → answer 18 b = (18 + b) % 113 := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 18 b table_ok h.1, h.2]

theorem fast_19 : ∀ b, b < 113 →
    (fastOk E1 E2 128 19 b && fastAnswer E1 E2 W2 128 19 b == (19 + b) % 113) = true := by
  decide +kernel

theorem row_19 : ∀ b, b < 113 → answer 19 b = (19 + b) % 113 := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 19 b table_ok h.1, h.2]

theorem fast_20 : ∀ b, b < 113 →
    (fastOk E1 E2 128 20 b && fastAnswer E1 E2 W2 128 20 b == (20 + b) % 113) = true := by
  decide +kernel

theorem row_20 : ∀ b, b < 113 → answer 20 b = (20 + b) % 113 := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 20 b table_ok h.1, h.2]

theorem fast_21 : ∀ b, b < 113 →
    (fastOk E1 E2 128 21 b && fastAnswer E1 E2 W2 128 21 b == (21 + b) % 113) = true := by
  decide +kernel

theorem row_21 : ∀ b, b < 113 → answer 21 b = (21 + b) % 113 := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 21 b table_ok h.1, h.2]

theorem fast_22 : ∀ b, b < 113 →
    (fastOk E1 E2 128 22 b && fastAnswer E1 E2 W2 128 22 b == (22 + b) % 113) = true := by
  decide +kernel

theorem row_22 : ∀ b, b < 113 → answer 22 b = (22 + b) % 113 := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 22 b table_ok h.1, h.2]

theorem fast_23 : ∀ b, b < 113 →
    (fastOk E1 E2 128 23 b && fastAnswer E1 E2 W2 128 23 b == (23 + b) % 113) = true := by
  decide +kernel

theorem row_23 : ∀ b, b < 113 → answer 23 b = (23 + b) % 113 := by
  intro b hb
  have h := fast_23 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 23 b table_ok h.1, h.2]

theorem fast_24 : ∀ b, b < 113 →
    (fastOk E1 E2 128 24 b && fastAnswer E1 E2 W2 128 24 b == (24 + b) % 113) = true := by
  decide +kernel

theorem row_24 : ∀ b, b < 113 → answer 24 b = (24 + b) % 113 := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 24 b table_ok h.1, h.2]

theorem fast_25 : ∀ b, b < 113 →
    (fastOk E1 E2 128 25 b && fastAnswer E1 E2 W2 128 25 b == (25 + b) % 113) = true := by
  decide +kernel

theorem row_25 : ∀ b, b < 113 → answer 25 b = (25 + b) % 113 := by
  intro b hb
  have h := fast_25 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 25 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 25 b table_ok h.1, h.2]

theorem fast_26 : ∀ b, b < 113 →
    (fastOk E1 E2 128 26 b && fastAnswer E1 E2 W2 128 26 b == (26 + b) % 113) = true := by
  decide +kernel

theorem row_26 : ∀ b, b < 113 → answer 26 b = (26 + b) % 113 := by
  intro b hb
  have h := fast_26 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 26 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 26 b table_ok h.1, h.2]

theorem fast_27 : ∀ b, b < 113 →
    (fastOk E1 E2 128 27 b && fastAnswer E1 E2 W2 128 27 b == (27 + b) % 113) = true := by
  decide +kernel

theorem row_27 : ∀ b, b < 113 → answer 27 b = (27 + b) % 113 := by
  intro b hb
  have h := fast_27 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 27 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 27 b table_ok h.1, h.2]

theorem fast_28 : ∀ b, b < 113 →
    (fastOk E1 E2 128 28 b && fastAnswer E1 E2 W2 128 28 b == (28 + b) % 113) = true := by
  decide +kernel

theorem row_28 : ∀ b, b < 113 → answer 28 b = (28 + b) % 113 := by
  intro b hb
  have h := fast_28 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 28 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 28 b table_ok h.1, h.2]

theorem fast_29 : ∀ b, b < 113 →
    (fastOk E1 E2 128 29 b && fastAnswer E1 E2 W2 128 29 b == (29 + b) % 113) = true := by
  decide +kernel

theorem row_29 : ∀ b, b < 113 → answer 29 b = (29 + b) % 113 := by
  intro b hb
  have h := fast_29 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 29 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 29 b table_ok h.1, h.2]

theorem fast_30 : ∀ b, b < 113 →
    (fastOk E1 E2 128 30 b && fastAnswer E1 E2 W2 128 30 b == (30 + b) % 113) = true := by
  decide +kernel

theorem row_30 : ∀ b, b < 113 → answer 30 b = (30 + b) % 113 := by
  intro b hb
  have h := fast_30 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 30 b table_ok h.1, h.2]

theorem fast_31 : ∀ b, b < 113 →
    (fastOk E1 E2 128 31 b && fastAnswer E1 E2 W2 128 31 b == (31 + b) % 113) = true := by
  decide +kernel

theorem row_31 : ∀ b, b < 113 → answer 31 b = (31 + b) % 113 := by
  intro b hb
  have h := fast_31 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 31 b table_ok h.1, h.2]

theorem fast_32 : ∀ b, b < 113 →
    (fastOk E1 E2 128 32 b && fastAnswer E1 E2 W2 128 32 b == (32 + b) % 113) = true := by
  decide +kernel

theorem row_32 : ∀ b, b < 113 → answer 32 b = (32 + b) % 113 := by
  intro b hb
  have h := fast_32 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 32 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 32 b table_ok h.1, h.2]

theorem fast_33 : ∀ b, b < 113 →
    (fastOk E1 E2 128 33 b && fastAnswer E1 E2 W2 128 33 b == (33 + b) % 113) = true := by
  decide +kernel

theorem row_33 : ∀ b, b < 113 → answer 33 b = (33 + b) % 113 := by
  intro b hb
  have h := fast_33 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 33 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 33 b table_ok h.1, h.2]

theorem fast_34 : ∀ b, b < 113 →
    (fastOk E1 E2 128 34 b && fastAnswer E1 E2 W2 128 34 b == (34 + b) % 113) = true := by
  decide +kernel

theorem row_34 : ∀ b, b < 113 → answer 34 b = (34 + b) % 113 := by
  intro b hb
  have h := fast_34 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 34 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 34 b table_ok h.1, h.2]

theorem fast_35 : ∀ b, b < 113 →
    (fastOk E1 E2 128 35 b && fastAnswer E1 E2 W2 128 35 b == (35 + b) % 113) = true := by
  decide +kernel

theorem row_35 : ∀ b, b < 113 → answer 35 b = (35 + b) % 113 := by
  intro b hb
  have h := fast_35 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 35 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 35 b table_ok h.1, h.2]

theorem fast_36 : ∀ b, b < 113 →
    (fastOk E1 E2 128 36 b && fastAnswer E1 E2 W2 128 36 b == (36 + b) % 113) = true := by
  decide +kernel

theorem row_36 : ∀ b, b < 113 → answer 36 b = (36 + b) % 113 := by
  intro b hb
  have h := fast_36 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 36 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 36 b table_ok h.1, h.2]

theorem fast_37 : ∀ b, b < 113 →
    (fastOk E1 E2 128 37 b && fastAnswer E1 E2 W2 128 37 b == (37 + b) % 113) = true := by
  decide +kernel

theorem row_37 : ∀ b, b < 113 → answer 37 b = (37 + b) % 113 := by
  intro b hb
  have h := fast_37 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 37 b table_ok h.1, h.2]

theorem fast_38 : ∀ b, b < 113 →
    (fastOk E1 E2 128 38 b && fastAnswer E1 E2 W2 128 38 b == (38 + b) % 113) = true := by
  decide +kernel

theorem row_38 : ∀ b, b < 113 → answer 38 b = (38 + b) % 113 := by
  intro b hb
  have h := fast_38 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 38 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 38 b table_ok h.1, h.2]

theorem fast_39 : ∀ b, b < 113 →
    (fastOk E1 E2 128 39 b && fastAnswer E1 E2 W2 128 39 b == (39 + b) % 113) = true := by
  decide +kernel

theorem row_39 : ∀ b, b < 113 → answer 39 b = (39 + b) % 113 := by
  intro b hb
  have h := fast_39 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 39 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 39 b table_ok h.1, h.2]

theorem fast_40 : ∀ b, b < 113 →
    (fastOk E1 E2 128 40 b && fastAnswer E1 E2 W2 128 40 b == (40 + b) % 113) = true := by
  decide +kernel

theorem row_40 : ∀ b, b < 113 → answer 40 b = (40 + b) % 113 := by
  intro b hb
  have h := fast_40 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 40 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 40 b table_ok h.1, h.2]

theorem fast_41 : ∀ b, b < 113 →
    (fastOk E1 E2 128 41 b && fastAnswer E1 E2 W2 128 41 b == (41 + b) % 113) = true := by
  decide +kernel

theorem row_41 : ∀ b, b < 113 → answer 41 b = (41 + b) % 113 := by
  intro b hb
  have h := fast_41 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 41 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 41 b table_ok h.1, h.2]

theorem fast_42 : ∀ b, b < 113 →
    (fastOk E1 E2 128 42 b && fastAnswer E1 E2 W2 128 42 b == (42 + b) % 113) = true := by
  decide +kernel

theorem row_42 : ∀ b, b < 113 → answer 42 b = (42 + b) % 113 := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 42 b table_ok h.1, h.2]

theorem fast_43 : ∀ b, b < 113 →
    (fastOk E1 E2 128 43 b && fastAnswer E1 E2 W2 128 43 b == (43 + b) % 113) = true := by
  decide +kernel

theorem row_43 : ∀ b, b < 113 → answer 43 b = (43 + b) % 113 := by
  intro b hb
  have h := fast_43 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 43 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 43 b table_ok h.1, h.2]

theorem fast_44 : ∀ b, b < 113 →
    (fastOk E1 E2 128 44 b && fastAnswer E1 E2 W2 128 44 b == (44 + b) % 113) = true := by
  decide +kernel

theorem row_44 : ∀ b, b < 113 → answer 44 b = (44 + b) % 113 := by
  intro b hb
  have h := fast_44 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 44 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 44 b table_ok h.1, h.2]

theorem fast_45 : ∀ b, b < 113 →
    (fastOk E1 E2 128 45 b && fastAnswer E1 E2 W2 128 45 b == (45 + b) % 113) = true := by
  decide +kernel

theorem row_45 : ∀ b, b < 113 → answer 45 b = (45 + b) % 113 := by
  intro b hb
  have h := fast_45 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 45 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 45 b table_ok h.1, h.2]

theorem fast_46 : ∀ b, b < 113 →
    (fastOk E1 E2 128 46 b && fastAnswer E1 E2 W2 128 46 b == (46 + b) % 113) = true := by
  decide +kernel

theorem row_46 : ∀ b, b < 113 → answer 46 b = (46 + b) % 113 := by
  intro b hb
  have h := fast_46 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 46 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 46 b table_ok h.1, h.2]

theorem fast_47 : ∀ b, b < 113 →
    (fastOk E1 E2 128 47 b && fastAnswer E1 E2 W2 128 47 b == (47 + b) % 113) = true := by
  decide +kernel

theorem row_47 : ∀ b, b < 113 → answer 47 b = (47 + b) % 113 := by
  intro b hb
  have h := fast_47 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 47 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 47 b table_ok h.1, h.2]

theorem fast_48 : ∀ b, b < 113 →
    (fastOk E1 E2 128 48 b && fastAnswer E1 E2 W2 128 48 b == (48 + b) % 113) = true := by
  decide +kernel

theorem row_48 : ∀ b, b < 113 → answer 48 b = (48 + b) % 113 := by
  intro b hb
  have h := fast_48 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 48 b table_ok h.1, h.2]

theorem fast_49 : ∀ b, b < 113 →
    (fastOk E1 E2 128 49 b && fastAnswer E1 E2 W2 128 49 b == (49 + b) % 113) = true := by
  decide +kernel

theorem row_49 : ∀ b, b < 113 → answer 49 b = (49 + b) % 113 := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 49 b table_ok h.1, h.2]

theorem fast_50 : ∀ b, b < 113 →
    (fastOk E1 E2 128 50 b && fastAnswer E1 E2 W2 128 50 b == (50 + b) % 113) = true := by
  decide +kernel

theorem row_50 : ∀ b, b < 113 → answer 50 b = (50 + b) % 113 := by
  intro b hb
  have h := fast_50 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 50 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 50 b table_ok h.1, h.2]

theorem fast_51 : ∀ b, b < 113 →
    (fastOk E1 E2 128 51 b && fastAnswer E1 E2 W2 128 51 b == (51 + b) % 113) = true := by
  decide +kernel

theorem row_51 : ∀ b, b < 113 → answer 51 b = (51 + b) % 113 := by
  intro b hb
  have h := fast_51 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 51 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 51 b table_ok h.1, h.2]

theorem fast_52 : ∀ b, b < 113 →
    (fastOk E1 E2 128 52 b && fastAnswer E1 E2 W2 128 52 b == (52 + b) % 113) = true := by
  decide +kernel

theorem row_52 : ∀ b, b < 113 → answer 52 b = (52 + b) % 113 := by
  intro b hb
  have h := fast_52 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 52 b table_ok h.1, h.2]

theorem fast_53 : ∀ b, b < 113 →
    (fastOk E1 E2 128 53 b && fastAnswer E1 E2 W2 128 53 b == (53 + b) % 113) = true := by
  decide +kernel

theorem row_53 : ∀ b, b < 113 → answer 53 b = (53 + b) % 113 := by
  intro b hb
  have h := fast_53 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 53 b table_ok h.1, h.2]

theorem fast_54 : ∀ b, b < 113 →
    (fastOk E1 E2 128 54 b && fastAnswer E1 E2 W2 128 54 b == (54 + b) % 113) = true := by
  decide +kernel

theorem row_54 : ∀ b, b < 113 → answer 54 b = (54 + b) % 113 := by
  intro b hb
  have h := fast_54 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 54 b table_ok h.1, h.2]

theorem fast_55 : ∀ b, b < 113 →
    (fastOk E1 E2 128 55 b && fastAnswer E1 E2 W2 128 55 b == (55 + b) % 113) = true := by
  decide +kernel

theorem row_55 : ∀ b, b < 113 → answer 55 b = (55 + b) % 113 := by
  intro b hb
  have h := fast_55 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 55 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 55 b table_ok h.1, h.2]

theorem fast_56 : ∀ b, b < 113 →
    (fastOk E1 E2 128 56 b && fastAnswer E1 E2 W2 128 56 b == (56 + b) % 113) = true := by
  decide +kernel

theorem row_56 : ∀ b, b < 113 → answer 56 b = (56 + b) % 113 := by
  intro b hb
  have h := fast_56 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 56 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 56 b table_ok h.1, h.2]

theorem fast_57 : ∀ b, b < 113 →
    (fastOk E1 E2 128 57 b && fastAnswer E1 E2 W2 128 57 b == (57 + b) % 113) = true := by
  decide +kernel

theorem row_57 : ∀ b, b < 113 → answer 57 b = (57 + b) % 113 := by
  intro b hb
  have h := fast_57 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 57 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 57 b table_ok h.1, h.2]

theorem fast_58 : ∀ b, b < 113 →
    (fastOk E1 E2 128 58 b && fastAnswer E1 E2 W2 128 58 b == (58 + b) % 113) = true := by
  decide +kernel

theorem row_58 : ∀ b, b < 113 → answer 58 b = (58 + b) % 113 := by
  intro b hb
  have h := fast_58 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 58 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 58 b table_ok h.1, h.2]

theorem fast_59 : ∀ b, b < 113 →
    (fastOk E1 E2 128 59 b && fastAnswer E1 E2 W2 128 59 b == (59 + b) % 113) = true := by
  decide +kernel

theorem row_59 : ∀ b, b < 113 → answer 59 b = (59 + b) % 113 := by
  intro b hb
  have h := fast_59 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 59 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 59 b table_ok h.1, h.2]

theorem fast_60 : ∀ b, b < 113 →
    (fastOk E1 E2 128 60 b && fastAnswer E1 E2 W2 128 60 b == (60 + b) % 113) = true := by
  decide +kernel

theorem row_60 : ∀ b, b < 113 → answer 60 b = (60 + b) % 113 := by
  intro b hb
  have h := fast_60 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 60 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 60 b table_ok h.1, h.2]

theorem fast_61 : ∀ b, b < 113 →
    (fastOk E1 E2 128 61 b && fastAnswer E1 E2 W2 128 61 b == (61 + b) % 113) = true := by
  decide +kernel

theorem row_61 : ∀ b, b < 113 → answer 61 b = (61 + b) % 113 := by
  intro b hb
  have h := fast_61 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 61 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 61 b table_ok h.1, h.2]

theorem fast_62 : ∀ b, b < 113 →
    (fastOk E1 E2 128 62 b && fastAnswer E1 E2 W2 128 62 b == (62 + b) % 113) = true := by
  decide +kernel

theorem row_62 : ∀ b, b < 113 → answer 62 b = (62 + b) % 113 := by
  intro b hb
  have h := fast_62 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 62 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 62 b table_ok h.1, h.2]

theorem fast_63 : ∀ b, b < 113 →
    (fastOk E1 E2 128 63 b && fastAnswer E1 E2 W2 128 63 b == (63 + b) % 113) = true := by
  decide +kernel

theorem row_63 : ∀ b, b < 113 → answer 63 b = (63 + b) % 113 := by
  intro b hb
  have h := fast_63 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 63 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 63 b table_ok h.1, h.2]

theorem fast_64 : ∀ b, b < 113 →
    (fastOk E1 E2 128 64 b && fastAnswer E1 E2 W2 128 64 b == (64 + b) % 113) = true := by
  decide +kernel

theorem row_64 : ∀ b, b < 113 → answer 64 b = (64 + b) % 113 := by
  intro b hb
  have h := fast_64 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 64 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 64 b table_ok h.1, h.2]

theorem fast_65 : ∀ b, b < 113 →
    (fastOk E1 E2 128 65 b && fastAnswer E1 E2 W2 128 65 b == (65 + b) % 113) = true := by
  decide +kernel

theorem row_65 : ∀ b, b < 113 → answer 65 b = (65 + b) % 113 := by
  intro b hb
  have h := fast_65 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 65 b table_ok h.1, h.2]

theorem fast_66 : ∀ b, b < 113 →
    (fastOk E1 E2 128 66 b && fastAnswer E1 E2 W2 128 66 b == (66 + b) % 113) = true := by
  decide +kernel

theorem row_66 : ∀ b, b < 113 → answer 66 b = (66 + b) % 113 := by
  intro b hb
  have h := fast_66 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 66 b table_ok h.1, h.2]

theorem fast_67 : ∀ b, b < 113 →
    (fastOk E1 E2 128 67 b && fastAnswer E1 E2 W2 128 67 b == (67 + b) % 113) = true := by
  decide +kernel

theorem row_67 : ∀ b, b < 113 → answer 67 b = (67 + b) % 113 := by
  intro b hb
  have h := fast_67 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 67 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 67 b table_ok h.1, h.2]

theorem fast_68 : ∀ b, b < 113 →
    (fastOk E1 E2 128 68 b && fastAnswer E1 E2 W2 128 68 b == (68 + b) % 113) = true := by
  decide +kernel

theorem row_68 : ∀ b, b < 113 → answer 68 b = (68 + b) % 113 := by
  intro b hb
  have h := fast_68 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 68 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 68 b table_ok h.1, h.2]

theorem fast_69 : ∀ b, b < 113 →
    (fastOk E1 E2 128 69 b && fastAnswer E1 E2 W2 128 69 b == (69 + b) % 113) = true := by
  decide +kernel

theorem row_69 : ∀ b, b < 113 → answer 69 b = (69 + b) % 113 := by
  intro b hb
  have h := fast_69 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 69 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 69 b table_ok h.1, h.2]

theorem fast_70 : ∀ b, b < 113 →
    (fastOk E1 E2 128 70 b && fastAnswer E1 E2 W2 128 70 b == (70 + b) % 113) = true := by
  decide +kernel

theorem row_70 : ∀ b, b < 113 → answer 70 b = (70 + b) % 113 := by
  intro b hb
  have h := fast_70 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 70 b table_ok h.1, h.2]

theorem fast_71 : ∀ b, b < 113 →
    (fastOk E1 E2 128 71 b && fastAnswer E1 E2 W2 128 71 b == (71 + b) % 113) = true := by
  decide +kernel

theorem row_71 : ∀ b, b < 113 → answer 71 b = (71 + b) % 113 := by
  intro b hb
  have h := fast_71 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 71 b table_ok h.1, h.2]

theorem fast_72 : ∀ b, b < 113 →
    (fastOk E1 E2 128 72 b && fastAnswer E1 E2 W2 128 72 b == (72 + b) % 113) = true := by
  decide +kernel

theorem row_72 : ∀ b, b < 113 → answer 72 b = (72 + b) % 113 := by
  intro b hb
  have h := fast_72 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 72 b table_ok h.1, h.2]

theorem fast_73 : ∀ b, b < 113 →
    (fastOk E1 E2 128 73 b && fastAnswer E1 E2 W2 128 73 b == (73 + b) % 113) = true := by
  decide +kernel

theorem row_73 : ∀ b, b < 113 → answer 73 b = (73 + b) % 113 := by
  intro b hb
  have h := fast_73 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 73 b table_ok h.1, h.2]

theorem fast_74 : ∀ b, b < 113 →
    (fastOk E1 E2 128 74 b && fastAnswer E1 E2 W2 128 74 b == (74 + b) % 113) = true := by
  decide +kernel

theorem row_74 : ∀ b, b < 113 → answer 74 b = (74 + b) % 113 := by
  intro b hb
  have h := fast_74 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 74 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 74 b table_ok h.1, h.2]

theorem fast_75 : ∀ b, b < 113 →
    (fastOk E1 E2 128 75 b && fastAnswer E1 E2 W2 128 75 b == (75 + b) % 113) = true := by
  decide +kernel

theorem row_75 : ∀ b, b < 113 → answer 75 b = (75 + b) % 113 := by
  intro b hb
  have h := fast_75 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 75 b table_ok h.1, h.2]

theorem fast_76 : ∀ b, b < 113 →
    (fastOk E1 E2 128 76 b && fastAnswer E1 E2 W2 128 76 b == (76 + b) % 113) = true := by
  decide +kernel

theorem row_76 : ∀ b, b < 113 → answer 76 b = (76 + b) % 113 := by
  intro b hb
  have h := fast_76 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 76 b table_ok h.1, h.2]

theorem fast_77 : ∀ b, b < 113 →
    (fastOk E1 E2 128 77 b && fastAnswer E1 E2 W2 128 77 b == (77 + b) % 113) = true := by
  decide +kernel

theorem row_77 : ∀ b, b < 113 → answer 77 b = (77 + b) % 113 := by
  intro b hb
  have h := fast_77 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 77 b table_ok h.1, h.2]

theorem fast_78 : ∀ b, b < 113 →
    (fastOk E1 E2 128 78 b && fastAnswer E1 E2 W2 128 78 b == (78 + b) % 113) = true := by
  decide +kernel

theorem row_78 : ∀ b, b < 113 → answer 78 b = (78 + b) % 113 := by
  intro b hb
  have h := fast_78 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 78 b table_ok h.1, h.2]

theorem fast_79 : ∀ b, b < 113 →
    (fastOk E1 E2 128 79 b && fastAnswer E1 E2 W2 128 79 b == (79 + b) % 113) = true := by
  decide +kernel

theorem row_79 : ∀ b, b < 113 → answer 79 b = (79 + b) % 113 := by
  intro b hb
  have h := fast_79 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 79 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 79 b table_ok h.1, h.2]

theorem fast_80 : ∀ b, b < 113 →
    (fastOk E1 E2 128 80 b && fastAnswer E1 E2 W2 128 80 b == (80 + b) % 113) = true := by
  decide +kernel

theorem row_80 : ∀ b, b < 113 → answer 80 b = (80 + b) % 113 := by
  intro b hb
  have h := fast_80 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 80 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 80 b table_ok h.1, h.2]

theorem fast_81 : ∀ b, b < 113 →
    (fastOk E1 E2 128 81 b && fastAnswer E1 E2 W2 128 81 b == (81 + b) % 113) = true := by
  decide +kernel

theorem row_81 : ∀ b, b < 113 → answer 81 b = (81 + b) % 113 := by
  intro b hb
  have h := fast_81 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 81 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 81 b table_ok h.1, h.2]

theorem fast_82 : ∀ b, b < 113 →
    (fastOk E1 E2 128 82 b && fastAnswer E1 E2 W2 128 82 b == (82 + b) % 113) = true := by
  decide +kernel

theorem row_82 : ∀ b, b < 113 → answer 82 b = (82 + b) % 113 := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 82 b table_ok h.1, h.2]

theorem fast_83 : ∀ b, b < 113 →
    (fastOk E1 E2 128 83 b && fastAnswer E1 E2 W2 128 83 b == (83 + b) % 113) = true := by
  decide +kernel

theorem row_83 : ∀ b, b < 113 → answer 83 b = (83 + b) % 113 := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 83 b table_ok h.1, h.2]

theorem fast_84 : ∀ b, b < 113 →
    (fastOk E1 E2 128 84 b && fastAnswer E1 E2 W2 128 84 b == (84 + b) % 113) = true := by
  decide +kernel

theorem row_84 : ∀ b, b < 113 → answer 84 b = (84 + b) % 113 := by
  intro b hb
  have h := fast_84 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 84 b table_ok h.1, h.2]

theorem fast_85 : ∀ b, b < 113 →
    (fastOk E1 E2 128 85 b && fastAnswer E1 E2 W2 128 85 b == (85 + b) % 113) = true := by
  decide +kernel

theorem row_85 : ∀ b, b < 113 → answer 85 b = (85 + b) % 113 := by
  intro b hb
  have h := fast_85 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 85 b table_ok h.1, h.2]

theorem fast_86 : ∀ b, b < 113 →
    (fastOk E1 E2 128 86 b && fastAnswer E1 E2 W2 128 86 b == (86 + b) % 113) = true := by
  decide +kernel

theorem row_86 : ∀ b, b < 113 → answer 86 b = (86 + b) % 113 := by
  intro b hb
  have h := fast_86 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 86 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 86 b table_ok h.1, h.2]

theorem fast_87 : ∀ b, b < 113 →
    (fastOk E1 E2 128 87 b && fastAnswer E1 E2 W2 128 87 b == (87 + b) % 113) = true := by
  decide +kernel

theorem row_87 : ∀ b, b < 113 → answer 87 b = (87 + b) % 113 := by
  intro b hb
  have h := fast_87 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 87 b table_ok h.1, h.2]

theorem fast_88 : ∀ b, b < 113 →
    (fastOk E1 E2 128 88 b && fastAnswer E1 E2 W2 128 88 b == (88 + b) % 113) = true := by
  decide +kernel

theorem row_88 : ∀ b, b < 113 → answer 88 b = (88 + b) % 113 := by
  intro b hb
  have h := fast_88 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 88 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 88 b table_ok h.1, h.2]

theorem fast_89 : ∀ b, b < 113 →
    (fastOk E1 E2 128 89 b && fastAnswer E1 E2 W2 128 89 b == (89 + b) % 113) = true := by
  decide +kernel

theorem row_89 : ∀ b, b < 113 → answer 89 b = (89 + b) % 113 := by
  intro b hb
  have h := fast_89 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 89 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 89 b table_ok h.1, h.2]

theorem fast_90 : ∀ b, b < 113 →
    (fastOk E1 E2 128 90 b && fastAnswer E1 E2 W2 128 90 b == (90 + b) % 113) = true := by
  decide +kernel

theorem row_90 : ∀ b, b < 113 → answer 90 b = (90 + b) % 113 := by
  intro b hb
  have h := fast_90 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 90 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 90 b table_ok h.1, h.2]

theorem fast_91 : ∀ b, b < 113 →
    (fastOk E1 E2 128 91 b && fastAnswer E1 E2 W2 128 91 b == (91 + b) % 113) = true := by
  decide +kernel

theorem row_91 : ∀ b, b < 113 → answer 91 b = (91 + b) % 113 := by
  intro b hb
  have h := fast_91 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 91 b table_ok h.1, h.2]

theorem fast_92 : ∀ b, b < 113 →
    (fastOk E1 E2 128 92 b && fastAnswer E1 E2 W2 128 92 b == (92 + b) % 113) = true := by
  decide +kernel

theorem row_92 : ∀ b, b < 113 → answer 92 b = (92 + b) % 113 := by
  intro b hb
  have h := fast_92 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 92 b table_ok h.1, h.2]

theorem fast_93 : ∀ b, b < 113 →
    (fastOk E1 E2 128 93 b && fastAnswer E1 E2 W2 128 93 b == (93 + b) % 113) = true := by
  decide +kernel

theorem row_93 : ∀ b, b < 113 → answer 93 b = (93 + b) % 113 := by
  intro b hb
  have h := fast_93 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 93 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 93 b table_ok h.1, h.2]

theorem fast_94 : ∀ b, b < 113 →
    (fastOk E1 E2 128 94 b && fastAnswer E1 E2 W2 128 94 b == (94 + b) % 113) = true := by
  decide +kernel

theorem row_94 : ∀ b, b < 113 → answer 94 b = (94 + b) % 113 := by
  intro b hb
  have h := fast_94 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 94 b table_ok h.1, h.2]

theorem fast_95 : ∀ b, b < 113 →
    (fastOk E1 E2 128 95 b && fastAnswer E1 E2 W2 128 95 b == (95 + b) % 113) = true := by
  decide +kernel

theorem row_95 : ∀ b, b < 113 → answer 95 b = (95 + b) % 113 := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 95 b table_ok h.1, h.2]

theorem fast_96 : ∀ b, b < 113 →
    (fastOk E1 E2 128 96 b && fastAnswer E1 E2 W2 128 96 b == (96 + b) % 113) = true := by
  decide +kernel

theorem row_96 : ∀ b, b < 113 → answer 96 b = (96 + b) % 113 := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 96 b table_ok h.1, h.2]

theorem fast_97 : ∀ b, b < 113 →
    (fastOk E1 E2 128 97 b && fastAnswer E1 E2 W2 128 97 b == (97 + b) % 113) = true := by
  decide +kernel

theorem row_97 : ∀ b, b < 113 → answer 97 b = (97 + b) % 113 := by
  intro b hb
  have h := fast_97 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 97 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 97 b table_ok h.1, h.2]

theorem fast_98 : ∀ b, b < 113 →
    (fastOk E1 E2 128 98 b && fastAnswer E1 E2 W2 128 98 b == (98 + b) % 113) = true := by
  decide +kernel

theorem row_98 : ∀ b, b < 113 → answer 98 b = (98 + b) % 113 := by
  intro b hb
  have h := fast_98 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 98 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 98 b table_ok h.1, h.2]

theorem fast_99 : ∀ b, b < 113 →
    (fastOk E1 E2 128 99 b && fastAnswer E1 E2 W2 128 99 b == (99 + b) % 113) = true := by
  decide +kernel

theorem row_99 : ∀ b, b < 113 → answer 99 b = (99 + b) % 113 := by
  intro b hb
  have h := fast_99 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 99 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 99 b table_ok h.1, h.2]

theorem fast_100 : ∀ b, b < 113 →
    (fastOk E1 E2 128 100 b && fastAnswer E1 E2 W2 128 100 b == (100 + b) % 113) = true := by
  decide +kernel

theorem row_100 : ∀ b, b < 113 → answer 100 b = (100 + b) % 113 := by
  intro b hb
  have h := fast_100 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 100 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 100 b table_ok h.1, h.2]

theorem fast_101 : ∀ b, b < 113 →
    (fastOk E1 E2 128 101 b && fastAnswer E1 E2 W2 128 101 b == (101 + b) % 113) = true := by
  decide +kernel

theorem row_101 : ∀ b, b < 113 → answer 101 b = (101 + b) % 113 := by
  intro b hb
  have h := fast_101 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 101 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 101 b table_ok h.1, h.2]

theorem fast_102 : ∀ b, b < 113 →
    (fastOk E1 E2 128 102 b && fastAnswer E1 E2 W2 128 102 b == (102 + b) % 113) = true := by
  decide +kernel

theorem row_102 : ∀ b, b < 113 → answer 102 b = (102 + b) % 113 := by
  intro b hb
  have h := fast_102 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 102 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 102 b table_ok h.1, h.2]

theorem fast_103 : ∀ b, b < 113 →
    (fastOk E1 E2 128 103 b && fastAnswer E1 E2 W2 128 103 b == (103 + b) % 113) = true := by
  decide +kernel

theorem row_103 : ∀ b, b < 113 → answer 103 b = (103 + b) % 113 := by
  intro b hb
  have h := fast_103 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 103 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 103 b table_ok h.1, h.2]

theorem fast_104 : ∀ b, b < 113 →
    (fastOk E1 E2 128 104 b && fastAnswer E1 E2 W2 128 104 b == (104 + b) % 113) = true := by
  decide +kernel

theorem row_104 : ∀ b, b < 113 → answer 104 b = (104 + b) % 113 := by
  intro b hb
  have h := fast_104 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 104 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 104 b table_ok h.1, h.2]

theorem fast_105 : ∀ b, b < 113 →
    (fastOk E1 E2 128 105 b && fastAnswer E1 E2 W2 128 105 b == (105 + b) % 113) = true := by
  decide +kernel

theorem row_105 : ∀ b, b < 113 → answer 105 b = (105 + b) % 113 := by
  intro b hb
  have h := fast_105 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 105 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 105 b table_ok h.1, h.2]

theorem fast_106 : ∀ b, b < 113 →
    (fastOk E1 E2 128 106 b && fastAnswer E1 E2 W2 128 106 b == (106 + b) % 113) = true := by
  decide +kernel

theorem row_106 : ∀ b, b < 113 → answer 106 b = (106 + b) % 113 := by
  intro b hb
  have h := fast_106 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 106 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 106 b table_ok h.1, h.2]

theorem fast_107 : ∀ b, b < 113 →
    (fastOk E1 E2 128 107 b && fastAnswer E1 E2 W2 128 107 b == (107 + b) % 113) = true := by
  decide +kernel

theorem row_107 : ∀ b, b < 113 → answer 107 b = (107 + b) % 113 := by
  intro b hb
  have h := fast_107 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 107 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 107 b table_ok h.1, h.2]

theorem fast_108 : ∀ b, b < 113 →
    (fastOk E1 E2 128 108 b && fastAnswer E1 E2 W2 128 108 b == (108 + b) % 113) = true := by
  decide +kernel

theorem row_108 : ∀ b, b < 113 → answer 108 b = (108 + b) % 113 := by
  intro b hb
  have h := fast_108 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 108 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 108 b table_ok h.1, h.2]

theorem fast_109 : ∀ b, b < 113 →
    (fastOk E1 E2 128 109 b && fastAnswer E1 E2 W2 128 109 b == (109 + b) % 113) = true := by
  decide +kernel

theorem row_109 : ∀ b, b < 113 → answer 109 b = (109 + b) % 113 := by
  intro b hb
  have h := fast_109 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 109 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 109 b table_ok h.1, h.2]

theorem fast_110 : ∀ b, b < 113 →
    (fastOk E1 E2 128 110 b && fastAnswer E1 E2 W2 128 110 b == (110 + b) % 113) = true := by
  decide +kernel

theorem row_110 : ∀ b, b < 113 → answer 110 b = (110 + b) % 113 := by
  intro b hb
  have h := fast_110 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 110 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 110 b table_ok h.1, h.2]

theorem fast_111 : ∀ b, b < 113 →
    (fastOk E1 E2 128 111 b && fastAnswer E1 E2 W2 128 111 b == (111 + b) % 113) = true := by
  decide +kernel

theorem row_111 : ∀ b, b < 113 → answer 111 b = (111 + b) % 113 := by
  intro b hb
  have h := fast_111 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 111 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 111 b table_ok h.1, h.2]

theorem fast_112 : ∀ b, b < 113 →
    (fastOk E1 E2 128 112 b && fastAnswer E1 E2 W2 128 112 b == (112 + b) % 113) = true := by
  decide +kernel

theorem row_112 : ∀ b, b < 113 → answer 112 b = (112 + b) % 113 := by
  intro b hb
  have h := fast_112 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 112 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 112 b table_ok h.1, h.2]

theorem adds_mod_113 : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 := by
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
  | 23, _ => exact row_23
  | 24, _ => exact row_24
  | 25, _ => exact row_25
  | 26, _ => exact row_26
  | 27, _ => exact row_27
  | 28, _ => exact row_28
  | 29, _ => exact row_29
  | 30, _ => exact row_30
  | 31, _ => exact row_31
  | 32, _ => exact row_32
  | 33, _ => exact row_33
  | 34, _ => exact row_34
  | 35, _ => exact row_35
  | 36, _ => exact row_36
  | 37, _ => exact row_37
  | 38, _ => exact row_38
  | 39, _ => exact row_39
  | 40, _ => exact row_40
  | 41, _ => exact row_41
  | 42, _ => exact row_42
  | 43, _ => exact row_43
  | 44, _ => exact row_44
  | 45, _ => exact row_45
  | 46, _ => exact row_46
  | 47, _ => exact row_47
  | 48, _ => exact row_48
  | 49, _ => exact row_49
  | 50, _ => exact row_50
  | 51, _ => exact row_51
  | 52, _ => exact row_52
  | 53, _ => exact row_53
  | 54, _ => exact row_54
  | 55, _ => exact row_55
  | 56, _ => exact row_56
  | 57, _ => exact row_57
  | 58, _ => exact row_58
  | 59, _ => exact row_59
  | 60, _ => exact row_60
  | 61, _ => exact row_61
  | 62, _ => exact row_62
  | 63, _ => exact row_63
  | 64, _ => exact row_64
  | 65, _ => exact row_65
  | 66, _ => exact row_66
  | 67, _ => exact row_67
  | 68, _ => exact row_68
  | 69, _ => exact row_69
  | 70, _ => exact row_70
  | 71, _ => exact row_71
  | 72, _ => exact row_72
  | 73, _ => exact row_73
  | 74, _ => exact row_74
  | 75, _ => exact row_75
  | 76, _ => exact row_76
  | 77, _ => exact row_77
  | 78, _ => exact row_78
  | 79, _ => exact row_79
  | 80, _ => exact row_80
  | 81, _ => exact row_81
  | 82, _ => exact row_82
  | 83, _ => exact row_83
  | 84, _ => exact row_84
  | 85, _ => exact row_85
  | 86, _ => exact row_86
  | 87, _ => exact row_87
  | 88, _ => exact row_88
  | 89, _ => exact row_89
  | 90, _ => exact row_90
  | 91, _ => exact row_91
  | 92, _ => exact row_92
  | 93, _ => exact row_93
  | 94, _ => exact row_94
  | 95, _ => exact row_95
  | 96, _ => exact row_96
  | 97, _ => exact row_97
  | 98, _ => exact row_98
  | 99, _ => exact row_99
  | 100, _ => exact row_100
  | 101, _ => exact row_101
  | 102, _ => exact row_102
  | 103, _ => exact row_103
  | 104, _ => exact row_104
  | 105, _ => exact row_105
  | 106, _ => exact row_106
  | 107, _ => exact row_107
  | 108, _ => exact row_108
  | 109, _ => exact row_109
  | 110, _ => exact row_110
  | 111, _ => exact row_111
  | 112, _ => exact row_112
  | n + 113, h => exact absurd h (by omega)

end LeanCheckedNetwork.Net
```
