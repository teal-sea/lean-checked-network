import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row5 : ∀ i : Fin 50,
    ((matrix (weights 5) i 5 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨5,by decide⟩ i := by decide +kernel
theorem paramW5row6 : ∀ i : Fin 50,
    ((matrix (weights 5) i 6 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨6,by decide⟩ i := by decide +kernel
theorem paramW5row7 : ∀ i : Fin 50,
    ((matrix (weights 5) i 7 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨7,by decide⟩ i := by decide +kernel
theorem paramW5row8 : ∀ i : Fin 50,
    ((matrix (weights 5) i 8 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨8,by decide⟩ i := by decide +kernel
theorem paramW5row9 : ∀ i : Fin 50,
    ((matrix (weights 5) i 9 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨9,by decide⟩ i := by decide +kernel
end ACASCommon
