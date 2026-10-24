import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row45 : ∀ i : Fin 50,
    ((matrix (weights 4) i 45 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨45,by decide⟩ i := by decide +kernel
theorem paramW4row46 : ∀ i : Fin 50,
    ((matrix (weights 4) i 46 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨46,by decide⟩ i := by decide +kernel
theorem paramW4row47 : ∀ i : Fin 50,
    ((matrix (weights 4) i 47 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨47,by decide⟩ i := by decide +kernel
theorem paramW4row48 : ∀ i : Fin 50,
    ((matrix (weights 4) i 48 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨48,by decide⟩ i := by decide +kernel
theorem paramW4row49 : ∀ i : Fin 50,
    ((matrix (weights 4) i 49 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨49,by decide⟩ i := by decide +kernel
end ACASCommon
