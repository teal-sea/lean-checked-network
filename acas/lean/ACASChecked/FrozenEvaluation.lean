import ACASChecked.FrozenFunctions
noncomputable section
namespace FrozenLink
open Spec TorchLean TorchLean.Tensor CertSound RouteA RouteNC Finset

def execution (x : Tensor ℝ [5]) : GridExecution ACASCommon.net :=
  ACASCommon.net.run (fun i => (Q : ℝ)*x.getScalar i)

theorem hidden_matches (x : Tensor ℝ [5])
    (hw0 : ∀ (i : Fin 5) (j : Fin 50),
      (matrix (ACASCommon.weights 0) i j : Rat) = (Q : Rat)*get2 Frozen.w0 j i)
    (hb0 : ∀ j : Fin 50, ((ACASCommon.biases 0).getD j 0 : Rat) = (Q : Rat)*Frozen.b0.getScalar j)
    (hwh : ∀ k < 5, ∀ (i j : Fin 50),
      (matrix (ACASCommon.weights (k+1)) i j : Rat) = (Q : Rat)*get2 (hiddenW k) j i)
    (hbh : ∀ k < 5, ∀ j : Fin 50,
      ((ACASCommon.biases (k+1)).getD j 0 : Rat) = (Q : Rat)*(hiddenB k).getScalar j) :
    ∀ k ≤ 5, ∀ j : Fin 50, (execution x).z k j = (Q : ℝ)*(hidden x k).getScalar j := by
  intro k
  induction k with
  | zero =>
    intro _ j
    exact grid_affine_matches Frozen.w0 Frozen.b0 j
      (fun i => matrix (ACASCommon.weights 0) i j) ((ACASCommon.biases 0).getD j 0)
      x ((execution x).y 0) ((execution x).z 0 j)
      (fun i => hw0 i j) (hb0 j) (fun i => rfl) ((execution x).affine 0 j)
  | succ k ih =>
    intro hk j
    apply grid_affine_matches (hiddenW k) (hiddenB k) j
      (fun i => matrix (ACASCommon.weights (k+1)) i j) ((ACASCommon.biases (k+1)).getD j 0)
      (Activation.reluSpec (hidden x k)) ((execution x).y (k+1)) ((execution x).z (k+1) j)
      (hwh k (by omega) · j) (hbh k (by omega) j) ?_ ((execution x).affine (k+1) j)
    intro i
    rw [(execution x).relu k i,ih (by omega) i,scaled_relu,tensor_relu_scalar]

theorem output_matches (x : Tensor ℝ [5])
    (hw0 : ∀ (i : Fin 5) (j : Fin 50),
      (matrix (ACASCommon.weights 0) i j : Rat) = (Q : Rat)*get2 Frozen.w0 j i)
    (hb0 : ∀ j : Fin 50, ((ACASCommon.biases 0).getD j 0 : Rat) = (Q : Rat)*Frozen.b0.getScalar j)
    (hwh : ∀ k < 5, ∀ (i j : Fin 50),
      (matrix (ACASCommon.weights (k+1)) i j : Rat) = (Q : Rat)*get2 (hiddenW k) j i)
    (hbh : ∀ k < 5, ∀ j : Fin 50,
      ((ACASCommon.biases (k+1)).getD j 0 : Rat) = (Q : Rat)*(hiddenB k).getScalar j)
    (hw6 : ∀ i : Fin 50,
      (matrix (ACASCommon.weights 6) i 0 : Rat) = (Q : Rat)*get2 Frozen.w6 (0 : Fin 5) i)
    (hb6 : ((ACASCommon.biases 6).getD 0 0 : Rat) = (Q : Rat)*Frozen.b6.getScalar 0) :
    (execution x).z 6 (0 : Fin 50) = (Q : ℝ)*(Frozen.network.model.forward x).getScalar 0 := by
  rw [forward_eq]
  apply grid_affine_matches Frozen.w6 Frozen.b6 (0 : Fin 5)
    (fun i => matrix (ACASCommon.weights 6) i 0) ((ACASCommon.biases 6).getD 0 0)
    (Activation.reluSpec (hidden x 5)) ((execution x).y 6) ((execution x).z 6 (0 : Fin 50))
    hw6 hb6 ?_ ((execution x).affine 6 (0 : Fin 50))
  intro i
  rw [(execution x).relu 5 i,hidden_matches x hw0 hb0 hwh hbh 5 (by omega) i,
    scaled_relu,tensor_relu_scalar]

#print axioms output_matches
end FrozenLink
