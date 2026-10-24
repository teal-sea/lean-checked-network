import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row40 : ∀ i : Fin 50,
    ((matrix (weights 2) i 40 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨40,by decide⟩ i := by decide +kernel
theorem paramW2row41 : ∀ i : Fin 50,
    ((matrix (weights 2) i 41 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨41,by decide⟩ i := by decide +kernel
theorem paramW2row42 : ∀ i : Fin 50,
    ((matrix (weights 2) i 42 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨42,by decide⟩ i := by decide +kernel
theorem paramW2row43 : ∀ i : Fin 50,
    ((matrix (weights 2) i 43 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨43,by decide⟩ i := by decide +kernel
theorem paramW2row44 : ∀ i : Fin 50,
    ((matrix (weights 2) i 44 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨44,by decide⟩ i := by decide +kernel
end ACASCommon
