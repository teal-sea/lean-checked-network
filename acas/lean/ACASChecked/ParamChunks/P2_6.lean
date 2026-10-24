import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row30 : ∀ i : Fin 50,
    ((matrix (weights 2) i 30 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨30,by decide⟩ i := by decide +kernel
theorem paramW2row31 : ∀ i : Fin 50,
    ((matrix (weights 2) i 31 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨31,by decide⟩ i := by decide +kernel
theorem paramW2row32 : ∀ i : Fin 50,
    ((matrix (weights 2) i 32 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨32,by decide⟩ i := by decide +kernel
theorem paramW2row33 : ∀ i : Fin 50,
    ((matrix (weights 2) i 33 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨33,by decide⟩ i := by decide +kernel
theorem paramW2row34 : ∀ i : Fin 50,
    ((matrix (weights 2) i 34 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨34,by decide⟩ i := by decide +kernel
end ACASCommon
