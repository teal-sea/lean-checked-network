import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row5 : ∀ i : Fin 50,
    ((matrix (weights 3) i 5 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨5,by decide⟩ i := by decide +kernel
theorem paramW3row6 : ∀ i : Fin 50,
    ((matrix (weights 3) i 6 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨6,by decide⟩ i := by decide +kernel
theorem paramW3row7 : ∀ i : Fin 50,
    ((matrix (weights 3) i 7 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨7,by decide⟩ i := by decide +kernel
theorem paramW3row8 : ∀ i : Fin 50,
    ((matrix (weights 3) i 8 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨8,by decide⟩ i := by decide +kernel
theorem paramW3row9 : ∀ i : Fin 50,
    ((matrix (weights 3) i 9 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨9,by decide⟩ i := by decide +kernel
end ACASCommon
