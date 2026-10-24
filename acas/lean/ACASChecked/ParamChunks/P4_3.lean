import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row15 : ∀ i : Fin 50,
    ((matrix (weights 4) i 15 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨15,by decide⟩ i := by decide +kernel
theorem paramW4row16 : ∀ i : Fin 50,
    ((matrix (weights 4) i 16 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨16,by decide⟩ i := by decide +kernel
theorem paramW4row17 : ∀ i : Fin 50,
    ((matrix (weights 4) i 17 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨17,by decide⟩ i := by decide +kernel
theorem paramW4row18 : ∀ i : Fin 50,
    ((matrix (weights 4) i 18 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨18,by decide⟩ i := by decide +kernel
theorem paramW4row19 : ∀ i : Fin 50,
    ((matrix (weights 4) i 19 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨19,by decide⟩ i := by decide +kernel
end ACASCommon
