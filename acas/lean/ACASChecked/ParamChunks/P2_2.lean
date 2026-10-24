import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row10 : ∀ i : Fin 50,
    ((matrix (weights 2) i 10 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨10,by decide⟩ i := by decide +kernel
theorem paramW2row11 : ∀ i : Fin 50,
    ((matrix (weights 2) i 11 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨11,by decide⟩ i := by decide +kernel
theorem paramW2row12 : ∀ i : Fin 50,
    ((matrix (weights 2) i 12 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨12,by decide⟩ i := by decide +kernel
theorem paramW2row13 : ∀ i : Fin 50,
    ((matrix (weights 2) i 13 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨13,by decide⟩ i := by decide +kernel
theorem paramW2row14 : ∀ i : Fin 50,
    ((matrix (weights 2) i 14 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨14,by decide⟩ i := by decide +kernel
end ACASCommon
