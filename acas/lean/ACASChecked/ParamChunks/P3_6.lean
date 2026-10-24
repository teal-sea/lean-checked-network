import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row30 : ∀ i : Fin 50,
    ((matrix (weights 3) i 30 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨30,by decide⟩ i := by decide +kernel
theorem paramW3row31 : ∀ i : Fin 50,
    ((matrix (weights 3) i 31 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨31,by decide⟩ i := by decide +kernel
theorem paramW3row32 : ∀ i : Fin 50,
    ((matrix (weights 3) i 32 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨32,by decide⟩ i := by decide +kernel
theorem paramW3row33 : ∀ i : Fin 50,
    ((matrix (weights 3) i 33 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨33,by decide⟩ i := by decide +kernel
theorem paramW3row34 : ∀ i : Fin 50,
    ((matrix (weights 3) i 34 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨34,by decide⟩ i := by decide +kernel
end ACASCommon
