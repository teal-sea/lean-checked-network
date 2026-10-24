import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row0 : ∀ i : Fin 50,
    ((matrix (weights 4) i 0 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨0,by decide⟩ i := by decide +kernel
theorem paramW4row1 : ∀ i : Fin 50,
    ((matrix (weights 4) i 1 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨1,by decide⟩ i := by decide +kernel
theorem paramW4row2 : ∀ i : Fin 50,
    ((matrix (weights 4) i 2 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨2,by decide⟩ i := by decide +kernel
theorem paramW4row3 : ∀ i : Fin 50,
    ((matrix (weights 4) i 3 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨3,by decide⟩ i := by decide +kernel
theorem paramW4row4 : ∀ i : Fin 50,
    ((matrix (weights 4) i 4 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨4,by decide⟩ i := by decide +kernel
end ACASCommon
