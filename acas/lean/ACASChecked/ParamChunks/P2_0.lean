import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row0 : ∀ i : Fin 50,
    ((matrix (weights 2) i 0 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨0,by decide⟩ i := by decide +kernel
theorem paramW2row1 : ∀ i : Fin 50,
    ((matrix (weights 2) i 1 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨1,by decide⟩ i := by decide +kernel
theorem paramW2row2 : ∀ i : Fin 50,
    ((matrix (weights 2) i 2 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨2,by decide⟩ i := by decide +kernel
theorem paramW2row3 : ∀ i : Fin 50,
    ((matrix (weights 2) i 3 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨3,by decide⟩ i := by decide +kernel
theorem paramW2row4 : ∀ i : Fin 50,
    ((matrix (weights 2) i 4 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨4,by decide⟩ i := by decide +kernel
end ACASCommon
