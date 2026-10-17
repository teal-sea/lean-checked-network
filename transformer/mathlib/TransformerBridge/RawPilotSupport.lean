import Transformer.Raw
import TransformerBridge.Bridge

/-! Reusable exact contraction transport. No concrete weights or table data imports. -/
namespace TransformerBridge.RawPilot

/-- A kernel-friendly finite sum; no floating-point or machine arithmetic. -/
def sumN : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => Int.add (sumN n f) (f n)

theorem sumN_eq (n : Nat) (f : Nat → Int) : sumN n f = ∑ i : Fin n, f i := by
  have h : sumN n f = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => simp [sumN]
    | succ n ih => rw [sumN, Finset.sum_range_succ, ih]
  rw [h, Finset.sum_range]

/-- Evaluate only the specified finite integer contraction. -/
def contract {n : Nat} (f g : Fin n → Int) : Int :=
  sumN n (fun k => if hk : k < n then Int.mul (f ⟨k, hk⟩) (g ⟨k, hk⟩) else 0)

theorem contract_eq {n : Nat} (f g : Fin n → Int) :
    contract f g = ∑ i, f i * g i := by
  rw [contract, sumN_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

/-- Transport an independently certified value vector through the unchanged output projection. -/
theorem ovec_of_vvec (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (v : Fin 32 → Int) (hv : ∀ l, W.vvec h tk j l = v l) (d : Fin 128) :
    W.ovec h tk j d = contract v (fun l => W.WO h l d) := by
  rw [Transformer.Weights.ovec, contract_eq]
  apply Finset.sum_congr rfl
  intro l _
  rw [hv]

/-- Transport an independently certified output vector into the unchanged raw table definition. -/
theorem TI_of_ovec (W : Transformer.Weights) (S : Nat) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (o : Fin 128 → Int) (ho : ∀ d, W.ovec h tk j d = o d)
    (valid : ¬ (j = 2 ∧ tk ≠ 113)) (i : Fin 512) :
    (W.rawTables S).TI h j tk i = contract o (fun d => W.Win d i) := by
  change (if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.Win d i) = _
  rw [if_neg valid, contract_eq]
  apply Finset.sum_congr rfl
  intro d _
  rw [ho]

end TransformerBridge.RawPilot
