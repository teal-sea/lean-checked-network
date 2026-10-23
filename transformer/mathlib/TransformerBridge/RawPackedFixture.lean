import TransformerBridge.RawPackedSupport

namespace TransformerBridge.RawPackedFixture

open TransformerBridge.RawPacked

/-- Signed digit carry gives a genuine collision without the bound hypothesis. -/
theorem carry_collision :
    TransformerCore.pkI [(TransformerCore.B : Int), 0] = TransformerCore.pkI [0, 1] := by
  decide +kernel

/-- A tiny signed contraction exercises the complete bounded transport. -/
theorem signed_transport (i : Fin 2) :
    TransformerBridge.RawPilot.contract
      (fun d : Fin 2 => if d = 0 then -2 else 3)
      (fun d => (if d = 0 then (fun k : Fin 2 => if k = 0 then -1 else 2)
                         else (fun k : Fin 2 => if k = 0 then 4 else -3)) i) =
      (if i = 0 then 14 else -13) := by
  exact contract_eq_of_packed
    (fun d : Fin 2 => if d = 0 then -2 else 3)
    (fun d : Fin 2 => if d = 0 then (fun k : Fin 2 => if k = 0 then -1 else 2)
                       else (fun k : Fin 2 => if k = 0 then 4 else -3))
    (fun d : Fin 2 => if d = 0 then -1 + (TransformerCore.B : Int) * 2
                       else 4 + (TransformerCore.B : Int) * (-3))
    (fun k : Fin 2 => if k = 0 then 14 else -13) 3 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) i

end TransformerBridge.RawPackedFixture
