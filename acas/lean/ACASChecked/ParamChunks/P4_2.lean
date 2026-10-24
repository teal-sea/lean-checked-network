import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row10 : ∀ i : Fin 50,
    ((matrix (weights 4) i 10 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨10,by decide⟩ i := by decide +kernel
theorem paramW4row11 : ∀ i : Fin 50,
    ((matrix (weights 4) i 11 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨11,by decide⟩ i := by decide +kernel
theorem paramW4row12 : ∀ i : Fin 50,
    ((matrix (weights 4) i 12 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨12,by decide⟩ i := by decide +kernel
theorem paramW4row13 : ∀ i : Fin 50,
    ((matrix (weights 4) i 13 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨13,by decide⟩ i := by decide +kernel
theorem paramW4row14 : ∀ i : Fin 50,
    ((matrix (weights 4) i 14 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨14,by decide⟩ i := by decide +kernel
end ACASCommon
