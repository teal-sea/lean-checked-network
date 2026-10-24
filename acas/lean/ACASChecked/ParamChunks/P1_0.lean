import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row0 : ∀ i : Fin 50,
    ((matrix (weights 1) i 0 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨0,by decide⟩ i := by decide +kernel
theorem paramW1row1 : ∀ i : Fin 50,
    ((matrix (weights 1) i 1 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨1,by decide⟩ i := by decide +kernel
theorem paramW1row2 : ∀ i : Fin 50,
    ((matrix (weights 1) i 2 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨2,by decide⟩ i := by decide +kernel
theorem paramW1row3 : ∀ i : Fin 50,
    ((matrix (weights 1) i 3 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨3,by decide⟩ i := by decide +kernel
theorem paramW1row4 : ∀ i : Fin 50,
    ((matrix (weights 1) i 4 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨4,by decide⟩ i := by decide +kernel
end ACASCommon
