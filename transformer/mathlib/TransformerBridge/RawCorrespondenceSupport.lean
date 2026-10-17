import TransformerBridge.RawPackedSupport

/-! Affine signed packing and complete table extensionality. No learned data imports. -/
namespace TransformerBridge.RawCorrespondence

open TransformerBridge.RawPilot (contract contract_eq)
open TransformerBridge.RawPacked

/-- Biases have their own bound; a packed collision cannot certify a false affine identity. -/
theorem affine_eq_of_packed {m n : Nat} (o : Fin m → Int)
    (W : Fin m → Fin n → Int) (r : Fin m → Int) (b t : Fin n → Int)
    (Ko Kw Kb : Nat) (hr : ∀ d, pack (W d) = r d)
    (ho : ∀ d, -(Ko : Int) ≤ o d ∧ o d ≤ Ko)
    (hw : ∀ d i, -(Kw : Int) ≤ W d i ∧ W d i ≤ Kw)
    (hb : ∀ i, -(Kb : Int) ≤ b i ∧ b i ≤ Kb)
    (ht : ∀ i, -((m * Ko * Kw + Kb : Nat) : Int) ≤ t i ∧
      t i ≤ (m * Ko * Kw + Kb : Nat))
    (hB : 2 * (m * Ko * Kw + Kb) < TransformerCore.B)
    (hp : contract o r + pack b = pack t) :
    ∀ i, contract o (fun d => W d i) + b i = t i := by
  have hf : ∀ i, -((m * Ko * Kw + Kb : Nat) : Int) ≤
      contract o (fun d => W d i) + b i ∧
      contract o (fun d => W d i) + b i ≤ (m * Ko * Kw + Kb : Nat) := by
    intro i
    have hc := contract_bounded o W Ko Kw ho hw i
    have hb' := hb i
    simp only [Nat.cast_add]
    constructor <;> omega
  apply pack_injective_bounded _ t (m * Ko * Kw + Kb) hf ht hB
  rw [pack_add, pack_contract]
  have he : (fun d => pack (W d)) = r := funext hr
  rw [he]
  exact hp

/-- Scaling the input before contraction is exact over integers. -/
theorem contract_scale {m : Nat} (c : Int) (x w : Fin m → Int) :
    contract (fun d => c * x d) w = c * contract x w := by
  simp only [contract_eq, Finset.mul_sum, mul_assoc]

/-- CI transport uses the original scale, residual embedding and bias. -/
theorem CI_of_affine (W : Transformer.Weights) (S : Nat) (i : Fin 512) :
    (W.rawTables S).CI i =
      contract (fun d => (S : Int) ^ 2 * W.xhat 113 2 d) (fun d => W.Win d i) + W.bin i := by
  rw [contract_scale, contract_eq]
  rfl

/-- Both definitions agree even in all 113 unused position-2 token slots. -/
theorem unused_slots (W : Transformer.Weights) (S : Nat) (T : TransformerCore.Tab)
    (h : Fin 4) (tk : Fin 114) (htk : tk ≠ 113) :
    (W.rawTables S).sc h 2 tk = (TransformerBridge.toTables T).sc h 2 tk ∧
    (∀ i, (W.rawTables S).TI h 2 tk i = (TransformerBridge.toTables T).TI h 2 tk i) ∧
    (∀ k, (W.rawTables S).TU h 2 tk k = (TransformerBridge.toTables T).TU h 2 tk k) := by
  simp [Transformer.Weights.rawTables, TransformerBridge.toTables, htk]

/-- All six complete field functions are necessary for this structure equality. -/
theorem tables_eq (T R : Transformer.Tables)
    (hsc : T.sc = R.sc) (hTI : T.TI = R.TI) (hTU : T.TU = R.TU)
    (hCI : T.CI = R.CI) (hCU : T.CU = R.CU) (hG : T.G = R.G) : T = R := by
  cases T
  cases R
  cases hsc
  cases hTI
  cases hTU
  cases hCI
  cases hCU
  cases hG
  rfl

end TransformerBridge.RawCorrespondence
