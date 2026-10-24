import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row45 : ∀ i : Fin 50,
    ((matrix (weights 2) i 45 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨45,by decide⟩ i := by decide +kernel
theorem paramW2row46 : ∀ i : Fin 50,
    ((matrix (weights 2) i 46 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨46,by decide⟩ i := by decide +kernel
theorem paramW2row47 : ∀ i : Fin 50,
    ((matrix (weights 2) i 47 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨47,by decide⟩ i := by decide +kernel
theorem paramW2row48 : ∀ i : Fin 50,
    ((matrix (weights 2) i 48 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨48,by decide⟩ i := by decide +kernel
theorem paramW2row49 : ∀ i : Fin 50,
    ((matrix (weights 2) i 49 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨49,by decide⟩ i := by decide +kernel
end ACASCommon
