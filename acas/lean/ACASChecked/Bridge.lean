import ACASChecked.Net
namespace Frozen
open Spec TorchLean TorchLean.Tensor
open NN.Verification.Cert.CROWNQuery
open NN.Verification.Cert.RationalReflection
open scoped Spec.RationalAlgebraic
/-- Exact rational execution embeds into the frozen real module semantics. -/
theorem evalQ_real {n m : Nat} (net : Network n m) (x : Tensor Rat [n]) :
    realTensor (evalQ net x) = net.model.forward (realTensor x) := by
  induction net with
  | linear l =>
    simp [evalQ, Network.model, Module.Chain.forward, Module.linear, linearSpec,
      realTensor_add, realTensor_matVecMul]
  | relu a =>
    simp [evalQ, Network.model, Module.Chain.forward, Module.relu, realTensor_relu]
  | comp a b ha hb =>
    simp [evalQ, Network.model, Module.Chain.forward, ← ha, ← hb]
#print axioms evalQ_real
end Frozen
