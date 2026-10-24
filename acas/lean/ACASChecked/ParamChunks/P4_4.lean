import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row20 : ∀ i : Fin 50,
    ((matrix (weights 4) i 20 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨20,by decide⟩ i := by decide +kernel
theorem paramW4row21 : ∀ i : Fin 50,
    ((matrix (weights 4) i 21 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨21,by decide⟩ i := by decide +kernel
theorem paramW4row22 : ∀ i : Fin 50,
    ((matrix (weights 4) i 22 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨22,by decide⟩ i := by decide +kernel
theorem paramW4row23 : ∀ i : Fin 50,
    ((matrix (weights 4) i 23 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨23,by decide⟩ i := by decide +kernel
theorem paramW4row24 : ∀ i : Fin 50,
    ((matrix (weights 4) i 24 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨24,by decide⟩ i := by decide +kernel
end ACASCommon
