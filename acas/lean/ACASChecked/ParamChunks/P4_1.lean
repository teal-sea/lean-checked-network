import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row5 : ∀ i : Fin 50,
    ((matrix (weights 4) i 5 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨5,by decide⟩ i := by decide +kernel
theorem paramW4row6 : ∀ i : Fin 50,
    ((matrix (weights 4) i 6 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨6,by decide⟩ i := by decide +kernel
theorem paramW4row7 : ∀ i : Fin 50,
    ((matrix (weights 4) i 7 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨7,by decide⟩ i := by decide +kernel
theorem paramW4row8 : ∀ i : Fin 50,
    ((matrix (weights 4) i 8 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨8,by decide⟩ i := by decide +kernel
theorem paramW4row9 : ∀ i : Fin 50,
    ((matrix (weights 4) i 9 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨9,by decide⟩ i := by decide +kernel
end ACASCommon
