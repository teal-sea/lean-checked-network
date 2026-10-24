import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row40 : ∀ i : Fin 50,
    ((matrix (weights 4) i 40 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨40,by decide⟩ i := by decide +kernel
theorem paramW4row41 : ∀ i : Fin 50,
    ((matrix (weights 4) i 41 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨41,by decide⟩ i := by decide +kernel
theorem paramW4row42 : ∀ i : Fin 50,
    ((matrix (weights 4) i 42 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨42,by decide⟩ i := by decide +kernel
theorem paramW4row43 : ∀ i : Fin 50,
    ((matrix (weights 4) i 43 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨43,by decide⟩ i := by decide +kernel
theorem paramW4row44 : ∀ i : Fin 50,
    ((matrix (weights 4) i 44 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨44,by decide⟩ i := by decide +kernel
end ACASCommon
