import ACASChecked.RawLeafSound
import ACASChecked.FrozenEvaluation
import ACASChecked.CoverageInstance
noncomputable section
namespace CertSound
open Spec TorchLean TorchLean.Tensor RouteNC ACASCoverage TreePilot

theorem frozen_leaf_safe (r : RawReceipt) (h : r.Valid) (hw : r.w = ACASCommon.weights) (hb : r.b = ACASCommon.biases)
    (x : Tensor ℝ [5]) (hx : InBox (r.boxl.zip r.boxu) (scaledPoint x))
    (hmodel : (FrozenLink.execution x).z 6 (0 : Fin 50) =
      (Q : ℝ)*(Frozen.network.model.forward x).getScalar 0) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  let e := r.net.run (fun i => (Q : ℝ)*x.getScalar i)
  have hbox := box_coordinates r.boxl r.boxu h.boxllen h.boxulen x hx
  have hv : e.z 6 (0 : Fin 50) = (Q : ℝ)*(Frozen.network.model.forward x).getScalar 0 := by
    dsimp only [e,RawReceipt.net]
    rw [hw,hb]
    exact hmodel
  exact h.safe e hbox _ hv

#print axioms frozen_leaf_safe
end CertSound
