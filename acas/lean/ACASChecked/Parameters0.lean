import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW0 : ∀ (i : Fin 5) (j : Fin 50),
    ((matrix (weights 0) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w0 j i := by decide +kernel
theorem paramB0 : ∀ j : Fin 50,
    (((biases 0).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b0.getScalar j := by decide +kernel
#print axioms paramW0
#print axioms paramB0
end ACASCommon
