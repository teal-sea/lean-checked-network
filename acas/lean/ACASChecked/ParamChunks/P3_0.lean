import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row0 : ∀ i : Fin 50,
    ((matrix (weights 3) i 0 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨0,by decide⟩ i := by decide +kernel
theorem paramW3row1 : ∀ i : Fin 50,
    ((matrix (weights 3) i 1 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨1,by decide⟩ i := by decide +kernel
theorem paramW3row2 : ∀ i : Fin 50,
    ((matrix (weights 3) i 2 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨2,by decide⟩ i := by decide +kernel
theorem paramW3row3 : ∀ i : Fin 50,
    ((matrix (weights 3) i 3 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨3,by decide⟩ i := by decide +kernel
theorem paramW3row4 : ∀ i : Fin 50,
    ((matrix (weights 3) i 4 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨4,by decide⟩ i := by decide +kernel
end ACASCommon
