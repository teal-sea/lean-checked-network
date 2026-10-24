import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row10 : ∀ i : Fin 50,
    ((matrix (weights 5) i 10 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨10,by decide⟩ i := by decide +kernel
theorem paramW5row11 : ∀ i : Fin 50,
    ((matrix (weights 5) i 11 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨11,by decide⟩ i := by decide +kernel
theorem paramW5row12 : ∀ i : Fin 50,
    ((matrix (weights 5) i 12 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨12,by decide⟩ i := by decide +kernel
theorem paramW5row13 : ∀ i : Fin 50,
    ((matrix (weights 5) i 13 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨13,by decide⟩ i := by decide +kernel
theorem paramW5row14 : ∀ i : Fin 50,
    ((matrix (weights 5) i 14 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨14,by decide⟩ i := by decide +kernel
end ACASCommon
