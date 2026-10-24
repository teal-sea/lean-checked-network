import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row25 : ∀ i : Fin 50,
    ((matrix (weights 1) i 25 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨25,by decide⟩ i := by decide +kernel
theorem paramW1row26 : ∀ i : Fin 50,
    ((matrix (weights 1) i 26 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨26,by decide⟩ i := by decide +kernel
theorem paramW1row27 : ∀ i : Fin 50,
    ((matrix (weights 1) i 27 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨27,by decide⟩ i := by decide +kernel
theorem paramW1row28 : ∀ i : Fin 50,
    ((matrix (weights 1) i 28 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨28,by decide⟩ i := by decide +kernel
theorem paramW1row29 : ∀ i : Fin 50,
    ((matrix (weights 1) i 29 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨29,by decide⟩ i := by decide +kernel
end ACASCommon
