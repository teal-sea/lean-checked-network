import ACASChecked.Common
import ACASChecked.Net
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2row20 : ∀ i : Fin 50,
    ((matrix (weights 2) i 20 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨20,by decide⟩ i := by decide +kernel
theorem paramW2row21 : ∀ i : Fin 50,
    ((matrix (weights 2) i 21 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨21,by decide⟩ i := by decide +kernel
theorem paramW2row22 : ∀ i : Fin 50,
    ((matrix (weights 2) i 22 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨22,by decide⟩ i := by decide +kernel
theorem paramW2row23 : ∀ i : Fin 50,
    ((matrix (weights 2) i 23 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨23,by decide⟩ i := by decide +kernel
theorem paramW2row24 : ∀ i : Fin 50,
    ((matrix (weights 2) i 24 : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 ⟨24,by decide⟩ i := by decide +kernel
end ACASCommon
