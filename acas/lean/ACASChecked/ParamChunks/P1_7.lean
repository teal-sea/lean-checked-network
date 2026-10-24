import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1row35 : ∀ i : Fin 50,
    ((matrix (weights 1) i 35 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨35,by decide⟩ i := by decide +kernel
theorem paramW1row36 : ∀ i : Fin 50,
    ((matrix (weights 1) i 36 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨36,by decide⟩ i := by decide +kernel
theorem paramW1row37 : ∀ i : Fin 50,
    ((matrix (weights 1) i 37 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨37,by decide⟩ i := by decide +kernel
theorem paramW1row38 : ∀ i : Fin 50,
    ((matrix (weights 1) i 38 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨38,by decide⟩ i := by decide +kernel
theorem paramW1row39 : ∀ i : Fin 50,
    ((matrix (weights 1) i 39 : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 ⟨39,by decide⟩ i := by decide +kernel
end ACASCommon
