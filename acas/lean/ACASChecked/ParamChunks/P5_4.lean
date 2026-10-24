import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row20 : ∀ i : Fin 50,
    ((matrix (weights 5) i 20 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨20,by decide⟩ i := by decide +kernel
theorem paramW5row21 : ∀ i : Fin 50,
    ((matrix (weights 5) i 21 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨21,by decide⟩ i := by decide +kernel
theorem paramW5row22 : ∀ i : Fin 50,
    ((matrix (weights 5) i 22 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨22,by decide⟩ i := by decide +kernel
theorem paramW5row23 : ∀ i : Fin 50,
    ((matrix (weights 5) i 23 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨23,by decide⟩ i := by decide +kernel
theorem paramW5row24 : ∀ i : Fin 50,
    ((matrix (weights 5) i 24 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨24,by decide⟩ i := by decide +kernel
end ACASCommon
