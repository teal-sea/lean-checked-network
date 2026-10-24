import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row10 : ∀ i : Fin 50,
    ((matrix (weights 1) i 10 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨10,by decide⟩ i := by decide +kernel
theorem paramW1row11 : ∀ i : Fin 50,
    ((matrix (weights 1) i 11 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨11,by decide⟩ i := by decide +kernel
theorem paramW1row12 : ∀ i : Fin 50,
    ((matrix (weights 1) i 12 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨12,by decide⟩ i := by decide +kernel
theorem paramW1row13 : ∀ i : Fin 50,
    ((matrix (weights 1) i 13 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨13,by decide⟩ i := by decide +kernel
theorem paramW1row14 : ∀ i : Fin 50,
    ((matrix (weights 1) i 14 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨14,by decide⟩ i := by decide +kernel
end ACASCommon
