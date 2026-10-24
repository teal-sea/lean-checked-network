import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row20 : ∀ i : Fin 50,
    ((matrix (weights 3) i 20 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨20,by decide⟩ i := by decide +kernel
theorem paramW3row21 : ∀ i : Fin 50,
    ((matrix (weights 3) i 21 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨21,by decide⟩ i := by decide +kernel
theorem paramW3row22 : ∀ i : Fin 50,
    ((matrix (weights 3) i 22 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨22,by decide⟩ i := by decide +kernel
theorem paramW3row23 : ∀ i : Fin 50,
    ((matrix (weights 3) i 23 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨23,by decide⟩ i := by decide +kernel
theorem paramW3row24 : ∀ i : Fin 50,
    ((matrix (weights 3) i 24 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨24,by decide⟩ i := by decide +kernel
end ACASCommon
