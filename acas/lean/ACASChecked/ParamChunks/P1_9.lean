import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row45 : ∀ i : Fin 50,
    ((matrix (weights 1) i 45 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨45,by decide⟩ i := by decide +kernel
theorem paramW1row46 : ∀ i : Fin 50,
    ((matrix (weights 1) i 46 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨46,by decide⟩ i := by decide +kernel
theorem paramW1row47 : ∀ i : Fin 50,
    ((matrix (weights 1) i 47 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨47,by decide⟩ i := by decide +kernel
theorem paramW1row48 : ∀ i : Fin 50,
    ((matrix (weights 1) i 48 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨48,by decide⟩ i := by decide +kernel
theorem paramW1row49 : ∀ i : Fin 50,
    ((matrix (weights 1) i 49 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨49,by decide⟩ i := by decide +kernel
end ACASCommon
