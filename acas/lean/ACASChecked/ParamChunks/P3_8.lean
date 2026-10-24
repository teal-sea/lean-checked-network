import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row40 : ∀ i : Fin 50,
    ((matrix (weights 3) i 40 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨40,by decide⟩ i := by decide +kernel
theorem paramW3row41 : ∀ i : Fin 50,
    ((matrix (weights 3) i 41 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨41,by decide⟩ i := by decide +kernel
theorem paramW3row42 : ∀ i : Fin 50,
    ((matrix (weights 3) i 42 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨42,by decide⟩ i := by decide +kernel
theorem paramW3row43 : ∀ i : Fin 50,
    ((matrix (weights 3) i 43 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨43,by decide⟩ i := by decide +kernel
theorem paramW3row44 : ∀ i : Fin 50,
    ((matrix (weights 3) i 44 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨44,by decide⟩ i := by decide +kernel
end ACASCommon
