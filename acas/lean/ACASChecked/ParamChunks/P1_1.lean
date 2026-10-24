import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row5 : ∀ i : Fin 50,
    ((matrix (weights 1) i 5 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨5,by decide⟩ i := by decide +kernel
theorem paramW1row6 : ∀ i : Fin 50,
    ((matrix (weights 1) i 6 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨6,by decide⟩ i := by decide +kernel
theorem paramW1row7 : ∀ i : Fin 50,
    ((matrix (weights 1) i 7 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨7,by decide⟩ i := by decide +kernel
theorem paramW1row8 : ∀ i : Fin 50,
    ((matrix (weights 1) i 8 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨8,by decide⟩ i := by decide +kernel
theorem paramW1row9 : ∀ i : Fin 50,
    ((matrix (weights 1) i 9 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨9,by decide⟩ i := by decide +kernel
end ACASCommon
