import TransformerBridge.RawCUUpdate

namespace TransformerBridge.RawTUUpdate
open TransformerBridge.RawPilot (contract contract_eq)
open TransformerBridge.RawCorrespondence (TU_of_ovec)

/-- Right coefficient perturbation, independent of any concrete model data. -/
theorem contract_update_right {m : Nat} (x w : Fin m → Int) (d : Fin m) :
    contract x (fun i => w i + if i = d then 1 else 0) = contract x w + x d := by
  have comm (a b : Fin m → Int) : contract a b = contract b a := by
    simp only [contract_eq, mul_comm]
  calc
    contract x (fun i => w i + if i = d then 1 else 0) =
        contract (fun i => w i + if i = d then 1 else 0) x := comm _ _
    _ = contract w x + x d := TransformerBridge.RawCUUpdate.contract_update w x d
    _ = contract x w + x d := congrArg (fun value : Int => value + x d) (comm w x)

/-- U alone changes; the original O vector and every other raw field stay unchanged. -/
theorem TU_U_update (W : Transformer.Weights) (S : Nat) (h : Fin 4)
    (tk : Fin 114) (j : Fin 3) (d : Fin 128) (k : Fin 113)
    (valid : ¬ (j = 2 ∧ tk ≠ 113)) :
    (({ W with U := fun e l => W.U e l + if e = d ∧ l = k then 1 else 0 } : Transformer.Weights).rawTables S).TU h j tk k =
      (W.rawTables S).TU h j tk k + W.ovec h tk j d := by
  let changed : Transformer.Weights :=
    { W with U := fun e l => W.U e l + if e = d ∧ l = k then 1 else 0 }
  have hO (e : Fin 128) : changed.ovec h tk j e = W.ovec h tk j e := rfl
  have hU : (fun e : Fin 128 => changed.U e k) =
      (fun e : Fin 128 => W.U e k + if e = d then 1 else 0) := by
    funext e
    simp [changed]
  have ht := TU_of_ovec changed S h tk j (W.ovec h tk j) hO valid k
  rw [hU] at ht
  calc
    (changed.rawTables S).TU h j tk k =
        contract (W.ovec h tk j) (fun e => W.U e k + if e = d then 1 else 0) := ht
    _ = contract (W.ovec h tk j) (fun e => W.U e k) + W.ovec h tk j d :=
      contract_update_right (W.ovec h tk j) (fun e => W.U e k) d
    _ = (W.rawTables S).TU h j tk k + W.ovec h tk j d :=
      congrArg (fun value : Int => value + W.ovec h tk j d)
        (TU_of_ovec W S h tk j (W.ovec h tk j) (fun _ => rfl) valid k).symm

end TransformerBridge.RawTUUpdate
