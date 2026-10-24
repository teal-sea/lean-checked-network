import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row20 : ∀ i : Fin 50,
    ((matrix (weights 1) i 20 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨20,by decide⟩ i := by decide +kernel
theorem paramW1row21 : ∀ i : Fin 50,
    ((matrix (weights 1) i 21 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨21,by decide⟩ i := by decide +kernel
theorem paramW1row22 : ∀ i : Fin 50,
    ((matrix (weights 1) i 22 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨22,by decide⟩ i := by decide +kernel
theorem paramW1row23 : ∀ i : Fin 50,
    ((matrix (weights 1) i 23 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨23,by decide⟩ i := by decide +kernel
theorem paramW1row24 : ∀ i : Fin 50,
    ((matrix (weights 1) i 24 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨24,by decide⟩ i := by decide +kernel
end ACASCommon
