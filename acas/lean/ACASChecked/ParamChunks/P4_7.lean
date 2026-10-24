import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4row35 : ∀ i : Fin 50,
    ((matrix (weights 4) i 35 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨35,by decide⟩ i := by decide +kernel
theorem paramW4row36 : ∀ i : Fin 50,
    ((matrix (weights 4) i 36 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨36,by decide⟩ i := by decide +kernel
theorem paramW4row37 : ∀ i : Fin 50,
    ((matrix (weights 4) i 37 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨37,by decide⟩ i := by decide +kernel
theorem paramW4row38 : ∀ i : Fin 50,
    ((matrix (weights 4) i 38 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨38,by decide⟩ i := by decide +kernel
theorem paramW4row39 : ∀ i : Fin 50,
    ((matrix (weights 4) i 39 : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 ⟨39,by decide⟩ i := by decide +kernel
end ACASCommon
