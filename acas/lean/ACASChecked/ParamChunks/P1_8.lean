import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row40 : ∀ i : Fin 50,
    ((matrix (weights 1) i 40 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨40,by decide⟩ i := by decide +kernel
theorem paramW1row41 : ∀ i : Fin 50,
    ((matrix (weights 1) i 41 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨41,by decide⟩ i := by decide +kernel
theorem paramW1row42 : ∀ i : Fin 50,
    ((matrix (weights 1) i 42 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨42,by decide⟩ i := by decide +kernel
theorem paramW1row43 : ∀ i : Fin 50,
    ((matrix (weights 1) i 43 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨43,by decide⟩ i := by decide +kernel
theorem paramW1row44 : ∀ i : Fin 50,
    ((matrix (weights 1) i 44 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨44,by decide⟩ i := by decide +kernel
end ACASCommon
