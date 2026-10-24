import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row15 : ∀ i : Fin 50,
    ((matrix (weights 1) i 15 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨15,by decide⟩ i := by decide +kernel
theorem paramW1row16 : ∀ i : Fin 50,
    ((matrix (weights 1) i 16 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨16,by decide⟩ i := by decide +kernel
theorem paramW1row17 : ∀ i : Fin 50,
    ((matrix (weights 1) i 17 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨17,by decide⟩ i := by decide +kernel
theorem paramW1row18 : ∀ i : Fin 50,
    ((matrix (weights 1) i 18 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨18,by decide⟩ i := by decide +kernel
theorem paramW1row19 : ∀ i : Fin 50,
    ((matrix (weights 1) i 19 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨19,by decide⟩ i := by decide +kernel
end ACASCommon
