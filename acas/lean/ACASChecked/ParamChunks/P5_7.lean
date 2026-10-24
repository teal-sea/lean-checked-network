import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5row35 : ∀ i : Fin 50,
    ((matrix (weights 5) i 35 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨35,by decide⟩ i := by decide +kernel
theorem paramW5row36 : ∀ i : Fin 50,
    ((matrix (weights 5) i 36 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨36,by decide⟩ i := by decide +kernel
theorem paramW5row37 : ∀ i : Fin 50,
    ((matrix (weights 5) i 37 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨37,by decide⟩ i := by decide +kernel
theorem paramW5row38 : ∀ i : Fin 50,
    ((matrix (weights 5) i 38 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨38,by decide⟩ i := by decide +kernel
theorem paramW5row39 : ∀ i : Fin 50,
    ((matrix (weights 5) i 39 : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 ⟨39,by decide⟩ i := by decide +kernel
end ACASCommon
