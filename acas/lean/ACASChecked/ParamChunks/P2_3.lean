import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row15 : ∀ i : Fin 50,
    ((matrix (weights 2) i 15 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨15,by decide⟩ i := by decide +kernel
theorem paramW2row16 : ∀ i : Fin 50,
    ((matrix (weights 2) i 16 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨16,by decide⟩ i := by decide +kernel
theorem paramW2row17 : ∀ i : Fin 50,
    ((matrix (weights 2) i 17 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨17,by decide⟩ i := by decide +kernel
theorem paramW2row18 : ∀ i : Fin 50,
    ((matrix (weights 2) i 18 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨18,by decide⟩ i := by decide +kernel
theorem paramW2row19 : ∀ i : Fin 50,
    ((matrix (weights 2) i 19 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨19,by decide⟩ i := by decide +kernel
end ACASCommon
