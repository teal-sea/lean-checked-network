import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row25 : ∀ i : Fin 50,
    ((matrix (weights 4) i 25 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨25,by decide⟩ i := by decide +kernel
theorem paramW4row26 : ∀ i : Fin 50,
    ((matrix (weights 4) i 26 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨26,by decide⟩ i := by decide +kernel
theorem paramW4row27 : ∀ i : Fin 50,
    ((matrix (weights 4) i 27 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨27,by decide⟩ i := by decide +kernel
theorem paramW4row28 : ∀ i : Fin 50,
    ((matrix (weights 4) i 28 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨28,by decide⟩ i := by decide +kernel
theorem paramW4row29 : ∀ i : Fin 50,
    ((matrix (weights 4) i 29 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨29,by decide⟩ i := by decide +kernel
end ACASCommon
