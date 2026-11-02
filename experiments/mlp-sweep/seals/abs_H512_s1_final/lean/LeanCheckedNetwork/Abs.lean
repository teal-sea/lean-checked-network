import LeanCheckedNetwork.Fast

/-!
# The same network with the absolute value in place of the square

`Network.lean` squares each hidden entry. This file defines the network that instead takes the
absolute value of each hidden entry, with everything else unchanged: row `a` of `E1` plus row `b`
of `E2`, one entry per neuron, scores `dot (row c of W2) hidden`, answer the first index of the
highest score.

The absolute value is written as `Int.ofNat (Int.natAbs x)`: `Int.natAbs` sends an integer to its
size, so the kernel evaluates it by one match on the integer's constructor.

The fast evaluator of `Fast.lean` never uses that the hidden entries are squares, only that they
are not negative, which the absolute value guarantees as well. `answerA_eq_fastAnswerA` is the
proof of `answerR_eq_fastAnswerR` in `Relu.lean` with `hiddenA` in place of `hiddenR`, step for
step.
-/

namespace LeanCheckedNetwork

/-- The hidden layer: `|x + y|` entry by entry. -/
def hiddenA : List Int → List Int → List Int
  | x :: xs, y :: ys => Int.ofNat (Int.natAbs (Int.add x y)) :: hiddenA xs ys
  | _, _ => []

/-- The absolute-value network's answer for the pair `(a, b)`, given its weight tables. -/
def answerA (E1 E2 W2 : List (List Int)) (a b : Nat) : Nat :=
  argmax (scores (hiddenA (nth E1 a) (nth E2 b)) W2)

/-- The absolute-value network's answer, computed with packed big numbers. -/
def fastAnswerA (E1 E2 W2 : List (List Int)) (H : Nat) (a b : Nat) : Nat :=
  let y := (hiddenA (nth E1 a) (nth E2 b)).map Int.toNat
  let C := colsPk (W2.map (·.map shiftW)) (List.replicate H 0)
  argmax ((unpk W2.length (dotN y C)).map Int.ofNat)

/-- Cheap checks under which `fastAnswerA` is exact. -/
def fastOkA (E1 E2 : List (List Int)) (H : Nat) (a b : Nat) : Bool :=
  let h := hiddenA (nth E1 a) (nth E2 b)
  h.length == H && h.all (0 ≤ ·) && decide (255 * (h.map Int.toNat).sum < B)

theorem answerA_eq_fastAnswerA (E1 E2 W2 : List (List Int)) (H a b : Nat)
    (ht : tableOk W2 H = true) (hf : fastOkA E1 E2 H a b = true) :
    answerA E1 E2 W2 a b = fastAnswerA E1 E2 W2 H a b := by
  simp only [tableOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  unfold fastAnswerA answerA
  simp only [fastOkA] at hf
  generalize hiddenA (nth E1 a) (nth E2 b) = h at hf ⊢
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

/-- One hidden entry of the absolute-value network: the sum when it is not negative, minus the sum
otherwise. -/
theorem abs_entry (x y : Int) :
    Int.ofNat (Int.natAbs (Int.add x y)) = if 0 ≤ x + y then x + y else -(x + y) := by
  show ((x + y).natAbs : Int) = _
  split <;> omega

/-- `hiddenA` is the absolute value, entry by entry. -/
theorem hiddenA_cons (x y : Int) (xs ys : List Int) :
    hiddenA (x :: xs) (y :: ys) = (if 0 ≤ x + y then x + y else -(x + y)) :: hiddenA xs ys := by
  rw [hiddenA, abs_entry]

end LeanCheckedNetwork
