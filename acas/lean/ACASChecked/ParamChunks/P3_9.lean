import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row45 : ∀ i : Fin 50,
    ((matrix (weights 3) i 45 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨45,by decide⟩ i := by decide +kernel
theorem paramW3row46 : ∀ i : Fin 50,
    ((matrix (weights 3) i 46 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨46,by decide⟩ i := by decide +kernel
theorem paramW3row47 : ∀ i : Fin 50,
    ((matrix (weights 3) i 47 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨47,by decide⟩ i := by decide +kernel
theorem paramW3row48 : ∀ i : Fin 50,
    ((matrix (weights 3) i 48 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨48,by decide⟩ i := by decide +kernel
theorem paramW3row49 : ∀ i : Fin 50,
    ((matrix (weights 3) i 49 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨49,by decide⟩ i := by decide +kernel
end ACASCommon
