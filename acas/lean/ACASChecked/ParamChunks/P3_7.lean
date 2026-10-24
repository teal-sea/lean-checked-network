import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3row35 : ∀ i : Fin 50,
    ((matrix (weights 3) i 35 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨35,by decide⟩ i := by decide +kernel
theorem paramW3row36 : ∀ i : Fin 50,
    ((matrix (weights 3) i 36 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨36,by decide⟩ i := by decide +kernel
theorem paramW3row37 : ∀ i : Fin 50,
    ((matrix (weights 3) i 37 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨37,by decide⟩ i := by decide +kernel
theorem paramW3row38 : ∀ i : Fin 50,
    ((matrix (weights 3) i 38 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨38,by decide⟩ i := by decide +kernel
theorem paramW3row39 : ∀ i : Fin 50,
    ((matrix (weights 3) i 39 : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 ⟨39,by decide⟩ i := by decide +kernel
end ACASCommon
