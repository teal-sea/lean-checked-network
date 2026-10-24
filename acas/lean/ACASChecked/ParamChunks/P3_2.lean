import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row10 : ∀ i : Fin 50,
    ((matrix (weights 3) i 10 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨10,by decide⟩ i := by decide +kernel
theorem paramW3row11 : ∀ i : Fin 50,
    ((matrix (weights 3) i 11 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨11,by decide⟩ i := by decide +kernel
theorem paramW3row12 : ∀ i : Fin 50,
    ((matrix (weights 3) i 12 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨12,by decide⟩ i := by decide +kernel
theorem paramW3row13 : ∀ i : Fin 50,
    ((matrix (weights 3) i 13 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨13,by decide⟩ i := by decide +kernel
theorem paramW3row14 : ∀ i : Fin 50,
    ((matrix (weights 3) i 14 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨14,by decide⟩ i := by decide +kernel
end ACASCommon
