import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row15 : ∀ i : Fin 50,
    ((matrix (weights 5) i 15 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨15,by decide⟩ i := by decide +kernel
theorem paramW5row16 : ∀ i : Fin 50,
    ((matrix (weights 5) i 16 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨16,by decide⟩ i := by decide +kernel
theorem paramW5row17 : ∀ i : Fin 50,
    ((matrix (weights 5) i 17 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨17,by decide⟩ i := by decide +kernel
theorem paramW5row18 : ∀ i : Fin 50,
    ((matrix (weights 5) i 18 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨18,by decide⟩ i := by decide +kernel
theorem paramW5row19 : ∀ i : Fin 50,
    ((matrix (weights 5) i 19 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨19,by decide⟩ i := by decide +kernel
end ACASCommon
