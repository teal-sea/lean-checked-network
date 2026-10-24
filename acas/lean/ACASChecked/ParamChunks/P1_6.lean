import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row30 : ∀ i : Fin 50,
    ((matrix (weights 1) i 30 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨30,by decide⟩ i := by decide +kernel
theorem paramW1row31 : ∀ i : Fin 50,
    ((matrix (weights 1) i 31 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨31,by decide⟩ i := by decide +kernel
theorem paramW1row32 : ∀ i : Fin 50,
    ((matrix (weights 1) i 32 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨32,by decide⟩ i := by decide +kernel
theorem paramW1row33 : ∀ i : Fin 50,
    ((matrix (weights 1) i 33 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨33,by decide⟩ i := by decide +kernel
theorem paramW1row34 : ∀ i : Fin 50,
    ((matrix (weights 1) i 34 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨34,by decide⟩ i := by decide +kernel
end ACASCommon
