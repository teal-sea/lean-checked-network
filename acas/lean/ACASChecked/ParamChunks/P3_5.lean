import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row25 : ∀ i : Fin 50,
    ((matrix (weights 3) i 25 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨25,by decide⟩ i := by decide +kernel
theorem paramW3row26 : ∀ i : Fin 50,
    ((matrix (weights 3) i 26 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨26,by decide⟩ i := by decide +kernel
theorem paramW3row27 : ∀ i : Fin 50,
    ((matrix (weights 3) i 27 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨27,by decide⟩ i := by decide +kernel
theorem paramW3row28 : ∀ i : Fin 50,
    ((matrix (weights 3) i 28 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨28,by decide⟩ i := by decide +kernel
theorem paramW3row29 : ∀ i : Fin 50,
    ((matrix (weights 3) i 29 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨29,by decide⟩ i := by decide +kernel
end ACASCommon
