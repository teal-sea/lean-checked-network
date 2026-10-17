import Transformer.Cached

-- Deliberately altered packed literal. CI must reject this equality in the kernel.
def alteredPackedLiteral : Int := -6
theorem alteredPackedLiteral_eq : alteredPackedLiteral = Transformer.pkI [-7] := by
  decide +kernel
