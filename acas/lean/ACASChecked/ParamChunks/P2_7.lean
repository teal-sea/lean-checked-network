import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row35 : ∀ i : Fin 50,
    ((matrix (weights 2) i 35 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨35,by decide⟩ i := by decide +kernel
theorem paramW2row36 : ∀ i : Fin 50,
    ((matrix (weights 2) i 36 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨36,by decide⟩ i := by decide +kernel
theorem paramW2row37 : ∀ i : Fin 50,
    ((matrix (weights 2) i 37 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨37,by decide⟩ i := by decide +kernel
theorem paramW2row38 : ∀ i : Fin 50,
    ((matrix (weights 2) i 38 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨38,by decide⟩ i := by decide +kernel
theorem paramW2row39 : ∀ i : Fin 50,
    ((matrix (weights 2) i 39 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨39,by decide⟩ i := by decide +kernel
end ACASCommon
