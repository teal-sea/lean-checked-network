import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row25 : ∀ i : Fin 50,
    ((matrix (weights 5) i 25 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨25,by decide⟩ i := by decide +kernel
theorem paramW5row26 : ∀ i : Fin 50,
    ((matrix (weights 5) i 26 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨26,by decide⟩ i := by decide +kernel
theorem paramW5row27 : ∀ i : Fin 50,
    ((matrix (weights 5) i 27 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨27,by decide⟩ i := by decide +kernel
theorem paramW5row28 : ∀ i : Fin 50,
    ((matrix (weights 5) i 28 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨28,by decide⟩ i := by decide +kernel
theorem paramW5row29 : ∀ i : Fin 50,
    ((matrix (weights 5) i 29 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨29,by decide⟩ i := by decide +kernel
end ACASCommon
