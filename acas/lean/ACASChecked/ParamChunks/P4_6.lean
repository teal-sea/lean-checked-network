import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row30 : ∀ i : Fin 50,
    ((matrix (weights 4) i 30 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨30,by decide⟩ i := by decide +kernel
theorem paramW4row31 : ∀ i : Fin 50,
    ((matrix (weights 4) i 31 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨31,by decide⟩ i := by decide +kernel
theorem paramW4row32 : ∀ i : Fin 50,
    ((matrix (weights 4) i 32 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨32,by decide⟩ i := by decide +kernel
theorem paramW4row33 : ∀ i : Fin 50,
    ((matrix (weights 4) i 33 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨33,by decide⟩ i := by decide +kernel
theorem paramW4row34 : ∀ i : Fin 50,
    ((matrix (weights 4) i 34 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨34,by decide⟩ i := by decide +kernel
end ACASCommon
