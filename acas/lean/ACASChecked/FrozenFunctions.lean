import ACASChecked.Common
import ACASChecked.TensorBridge
noncomputable section
namespace FrozenLink
open Spec TorchLean TorchLean.Tensor CertSound

def hiddenW : Nat → Tensor Rat [50,50]
  | 0 => Frozen.w1 | 1 => Frozen.w2 | 2 => Frozen.w3 | 3 => Frozen.w4 | _ => Frozen.w5
def hiddenB : Nat → Tensor Rat [50]
  | 0 => Frozen.b1 | 1 => Frozen.b2 | 2 => Frozen.b3 | 3 => Frozen.b4 | _ => Frozen.b5

def hidden (x : Tensor ℝ [5]) : Nat → Tensor ℝ [50]
  | 0 => realAffine Frozen.w0 Frozen.b0 x
  | k+1 => realAffine (hiddenW k) (hiddenB k) (Activation.reluSpec (hidden x k))

def output (x : Tensor ℝ [5]) : Tensor ℝ [5] :=
  realAffine Frozen.w6 Frozen.b6 (Activation.reluSpec (hidden x 5))

theorem forward_eq (x : Tensor ℝ [5]) : Frozen.network.model.forward x = output x := by rfl

#print axioms forward_eq
end FrozenLink
