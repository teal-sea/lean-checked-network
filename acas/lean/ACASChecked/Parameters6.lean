import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW6 : ∀ (i : Fin 50) (j : Fin 1),
    ((matrix (weights 6) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w6 (0 : Fin 5) i := by decide +kernel
theorem paramB6 : (((biases 6).getD 0 0 : Int) : Rat) = (Q : Rat)*Frozen.b6.getScalar 0 := by decide +kernel
#print axioms paramW6
#print axioms paramB6
end ACASCommon
