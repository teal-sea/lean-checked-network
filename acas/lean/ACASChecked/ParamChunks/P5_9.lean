import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row45 : ∀ i : Fin 50,
    ((matrix (weights 5) i 45 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨45,by decide⟩ i := by decide +kernel
theorem paramW5row46 : ∀ i : Fin 50,
    ((matrix (weights 5) i 46 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨46,by decide⟩ i := by decide +kernel
theorem paramW5row47 : ∀ i : Fin 50,
    ((matrix (weights 5) i 47 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨47,by decide⟩ i := by decide +kernel
theorem paramW5row48 : ∀ i : Fin 50,
    ((matrix (weights 5) i 48 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨48,by decide⟩ i := by decide +kernel
theorem paramW5row49 : ∀ i : Fin 50,
    ((matrix (weights 5) i 49 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨49,by decide⟩ i := by decide +kernel
end ACASCommon
