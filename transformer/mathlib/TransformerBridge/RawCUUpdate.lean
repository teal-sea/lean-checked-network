import TransformerBridge.RawCorrespondenceLinear

namespace TransformerBridge.RawCUUpdate
open TransformerBridge.RawPilot (contract contract_eq)
open TransformerBridge.RawCorrespondence (contract_add_left CU_of_contract)

/-- A single exact additive coefficient update changes a contraction by that coordinate. -/
theorem contract_update {m : Nat} (x w : Fin m → Int) (d : Fin m) :
    contract (fun i => x i + if i = d then 1 else 0) w = contract x w + w d := by
  rw [contract_add_left]
  simp [contract_eq, ite_mul]

/-- Only bout changes; every embedding, scale and U coefficient remains the original one. -/
theorem CU_bout_update (W : Transformer.Weights) (S : Nat) (d : Fin 128) (k : Fin 113) :
    (({ W with bout := fun i => W.bout i + if i = d then 1 else 0 } : Transformer.Weights).rawTables S).CU k =
      (W.rawTables S).CU k + W.U d k := by
  rw [CU_of_contract, CU_of_contract]
  simpa only [Transformer.Weights.xhat, add_assoc] using
    (contract_update (fun i => (S : Int) ^ 4 * W.xhat 113 2 i + W.bout i) (fun i => W.U i k) d)

end TransformerBridge.RawCUUpdate
