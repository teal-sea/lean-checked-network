import ACASChecked.Parameters0
import ACASChecked.Parameters1
import ACASChecked.Parameters2
import ACASChecked.Parameters3
import ACASChecked.Parameters4
import ACASChecked.Parameters5
import ACASChecked.Parameters6
import ACASChecked.FrozenEvaluation
noncomputable section
namespace FrozenLink
open Spec TorchLean TorchLean.Tensor CertSound RouteA RouteNC ACASCommon

theorem hidden_weights : ∀ k < 5, ∀ (i j : Fin 50),
    (matrix (weights (k+1)) i j : Rat) = (Q : Rat)*get2 (hiddenW k) j i := by
  intro k hk i j
  interval_cases k
  · exact paramW1 i j
  · exact paramW2 i j
  · exact paramW3 i j
  · exact paramW4 i j
  · exact paramW5 i j
theorem hidden_biases : ∀ k < 5, ∀ j : Fin 50,
    ((biases (k+1)).getD j 0 : Rat) = (Q : Rat)*(hiddenB k).getScalar j := by
  intro k hk j
  interval_cases k
  · exact paramB1 j
  · exact paramB2 j
  · exact paramB3 j
  · exact paramB4 j
  · exact paramB5 j
theorem model_correspondence (x : Tensor ℝ [5]) :
    (execution x).z 6 (0 : Fin 50) = (Q : ℝ)*(Frozen.network.model.forward x).getScalar 0 :=
  output_matches x paramW0 paramB0 hidden_weights hidden_biases (fun i => paramW6 i 0) paramB6

#print axioms model_correspondence
end FrozenLink
