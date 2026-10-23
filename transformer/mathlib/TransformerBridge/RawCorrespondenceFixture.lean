import TransformerBridge.RawCorrespondenceSupport

namespace TransformerBridge.RawCorrespondenceFixture

open TransformerBridge.RawCorrespondence TransformerBridge.RawPacked

/-- Signed affine transport: includes a negative bias and a scaled input. -/
theorem signed_affine (i : Fin 2) :
    TransformerBridge.RawPilot.contract
      (fun d : Fin 2 => if d = 0 then -4 else 6)
      (fun d => (if d = 0 then (fun k : Fin 2 => if k = 0 then -1 else 2)
                         else (fun k : Fin 2 => if k = 0 then 4 else -3)) i) +
      (if i = 0 then -5 else 7) = (if i = 0 then 23 else -19) := by
  exact affine_eq_of_packed
    (fun d : Fin 2 => if d = 0 then -4 else 6)
    (fun d : Fin 2 => if d = 0 then (fun k : Fin 2 => if k = 0 then -1 else 2)
                       else (fun k : Fin 2 => if k = 0 then 4 else -3))
    (fun d : Fin 2 => if d = 0 then -1 + (TransformerCore.B : Int) * 2
                       else 4 + (TransformerCore.B : Int) * (-3))
    (fun k : Fin 2 => if k = 0 then -5 else 7)
    (fun k : Fin 2 => if k = 0 then 23 else -19) 6 4 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) i

end TransformerBridge.RawCorrespondenceFixture
