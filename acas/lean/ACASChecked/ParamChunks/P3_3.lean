import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row15 : ∀ i : Fin 50,
    ((matrix (weights 3) i 15 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨15,by decide⟩ i := by decide +kernel
theorem paramW3row16 : ∀ i : Fin 50,
    ((matrix (weights 3) i 16 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨16,by decide⟩ i := by decide +kernel
theorem paramW3row17 : ∀ i : Fin 50,
    ((matrix (weights 3) i 17 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨17,by decide⟩ i := by decide +kernel
theorem paramW3row18 : ∀ i : Fin 50,
    ((matrix (weights 3) i 18 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨18,by decide⟩ i := by decide +kernel
theorem paramW3row19 : ∀ i : Fin 50,
    ((matrix (weights 3) i 19 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨19,by decide⟩ i := by decide +kernel
end ACASCommon
