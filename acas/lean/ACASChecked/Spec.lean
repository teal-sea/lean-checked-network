import ACASChecked.Net
namespace Frozen
open Spec TorchLean TorchLean.Tensor
noncomputable def lo : Fin 5 → ℝ := ![3/5, -1/2, -1/2, 9/20, -1/2]
noncomputable def hi : Fin 5 → ℝ := ![679857769/1000000000, 1/2, 1/2, 1/2, -9/20]
noncomputable def threshold : ℝ := 3991125645861615/1000000000000000
/-- Frozen real safety statement; deliberately no proof. Inputs already normalized.
ONNX importer correspondence, IEEE execution and aircraft behavior are outside this Prop. -/
def ACASXu_1_1_Property1 : Prop :=
  ∀ x : Tensor ℝ [5],
    (∀ i : Fin 5, lo i ≤ x.getScalar i ∧ x.getScalar i ≤ hi i) →
    (network.model.forward x).getScalar 0 < threshold
end Frozen
