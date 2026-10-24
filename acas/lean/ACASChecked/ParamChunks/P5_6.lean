import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row30 : ∀ i : Fin 50,
    ((matrix (weights 5) i 30 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨30,by decide⟩ i := by decide +kernel
theorem paramW5row31 : ∀ i : Fin 50,
    ((matrix (weights 5) i 31 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨31,by decide⟩ i := by decide +kernel
theorem paramW5row32 : ∀ i : Fin 50,
    ((matrix (weights 5) i 32 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨32,by decide⟩ i := by decide +kernel
theorem paramW5row33 : ∀ i : Fin 50,
    ((matrix (weights 5) i 33 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨33,by decide⟩ i := by decide +kernel
theorem paramW5row34 : ∀ i : Fin 50,
    ((matrix (weights 5) i 34 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨34,by decide⟩ i := by decide +kernel
end ACASCommon
