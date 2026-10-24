import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row5 : ∀ i : Fin 50,
    ((matrix (weights 2) i 5 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨5,by decide⟩ i := by decide +kernel
theorem paramW2row6 : ∀ i : Fin 50,
    ((matrix (weights 2) i 6 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨6,by decide⟩ i := by decide +kernel
theorem paramW2row7 : ∀ i : Fin 50,
    ((matrix (weights 2) i 7 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨7,by decide⟩ i := by decide +kernel
theorem paramW2row8 : ∀ i : Fin 50,
    ((matrix (weights 2) i 8 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨8,by decide⟩ i := by decide +kernel
theorem paramW2row9 : ∀ i : Fin 50,
    ((matrix (weights 2) i 9 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨9,by decide⟩ i := by decide +kernel
end ACASCommon
