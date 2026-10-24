import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row40 : ∀ i : Fin 50,
    ((matrix (weights 5) i 40 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨40,by decide⟩ i := by decide +kernel
theorem paramW5row41 : ∀ i : Fin 50,
    ((matrix (weights 5) i 41 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨41,by decide⟩ i := by decide +kernel
theorem paramW5row42 : ∀ i : Fin 50,
    ((matrix (weights 5) i 42 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨42,by decide⟩ i := by decide +kernel
theorem paramW5row43 : ∀ i : Fin 50,
    ((matrix (weights 5) i 43 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨43,by decide⟩ i := by decide +kernel
theorem paramW5row44 : ∀ i : Fin 50,
    ((matrix (weights 5) i 44 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨44,by decide⟩ i := by decide +kernel
end ACASCommon
