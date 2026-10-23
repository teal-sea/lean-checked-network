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
  let changed : Transformer.Weights :=
    { W with bout := fun i => W.bout i + if i = d then 1 else 0 }
  have hU : changed.U = W.U := rfl
  have hinput :
      (fun i : Fin 128 => (S : Int) ^ 4 * changed.xhat 113 2 i + changed.bout i) =
      (fun i : Fin 128 => ((S : Int) ^ 4 * W.xhat 113 2 i + W.bout i) +
        if i = d then 1 else 0) := by
    funext i
    change (S : Int) ^ 4 * W.xhat 113 2 i + (W.bout i + if i = d then 1 else 0) =
      ((S : Int) ^ 4 * W.xhat 113 2 i + W.bout i) + if i = d then 1 else 0
    exact (add_assoc _ _ _).symm
  have hcu := CU_of_contract changed S k
  rw [hU] at hcu
  calc
    (changed.rawTables S).CU k =
        contract (fun i => (S : Int) ^ 4 * changed.xhat 113 2 i + changed.bout i)
          (fun i => W.U i k) := hcu
    _ = contract (fun i => ((S : Int) ^ 4 * W.xhat 113 2 i + W.bout i) +
          if i = d then 1 else 0) (fun i => W.U i k) :=
      congrArg (fun input : Fin 128 → Int => contract input (fun i => W.U i k)) hinput
    _ = contract (fun i => (S : Int) ^ 4 * W.xhat 113 2 i + W.bout i)
          (fun i => W.U i k) + W.U d k :=
      contract_update (fun i => (S : Int) ^ 4 * W.xhat 113 2 i + W.bout i)
        (fun i => W.U i k) d
    _ = (W.rawTables S).CU k + W.U d k :=
      congrArg (fun value : Int => value + W.U d k) (CU_of_contract W S k).symm

end TransformerBridge.RawCUUpdate
