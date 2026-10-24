import ACASChecked.GridEvaluation
import ACASChecked.Spec
noncomputable section
namespace CertSound
open RouteNC Finset Spec TorchLean TorchLean.Tensor
open NN.Verification.Cert.RationalReflection

def realAffine {n m : Nat} (w : Tensor Rat [m,n]) (b : Tensor Rat [m]) (x : Tensor ℝ [n]) : Tensor ℝ [m] :=
  linearSpec ⟨realTensor w,realTensor b⟩ x

theorem realAffine_scalar {n m : Nat} (w : Tensor Rat [m,n]) (b : Tensor Rat [m])
    (x : Tensor ℝ [n]) (j : Fin m) :
    (realAffine w b x).getScalar j = (b.getScalar j : ℝ) + ∑ i, ((get2 w j i : Rat) : ℝ)*x.getScalar i := by
  simp only [realAffine,linearSpec,Spec.getScalar_add_spec,
    Proofs.TensorAlgebra.getScalar_mat_vec_mul_spec,realTensor_get2,realTensor_getScalar]
  ring

theorem scaled_relu (x : ℝ) : max 0 ((Q : ℝ)*x) = (Q : ℝ)*max 0 x := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_left hx,max_eq_left (mul_nonpos_of_nonneg_of_nonpos (le_of_lt Q_pos) hx)]
    ring
  · rw [max_eq_right hx,max_eq_right (mul_nonneg (le_of_lt Q_pos) hx)]

theorem tensor_relu_scalar {n : Nat} (x : Tensor ℝ [n]) (i : Fin n) :
    (Activation.reluSpec x).getScalar i = max 0 (x.getScalar i) := by
  simp [Activation.reluSpec,Activation.Math.relu_zero_branch_eq_max,max_comm]

theorem grid_affine_matches {n m : Nat} (w : Tensor Rat [m,n]) (b : Tensor Rat [m])
    (j : Fin m) (wi : Fin n → Int) (bi : Int) (x : Tensor ℝ [n]) (y : Fin n → ℝ) (z : ℝ)
    (hw : ∀ i, (wi i : Rat) = (Q : Rat)*get2 w j i)
    (hb : (bi : Rat) = (Q : Rat)*b.getScalar j)
    (hy : ∀ i, y i = (Q : ℝ)*x.getScalar i)
    (hz : (Q : ℝ)*z = (Q : ℝ)*(bi : ℝ) + ∑ i, (wi i : ℝ)*y i) :
    z = (Q : ℝ)*(realAffine w b x).getScalar j := by
  have hwR : ∀ i, (wi i : ℝ) = (Q : ℝ)*((get2 w j i : Rat) : ℝ) := by
    intro i
    exact_mod_cast hw i
  have hbR : (bi : ℝ) = (Q : ℝ)*(b.getScalar j : ℝ) := by exact_mod_cast hb
  apply mul_left_cancel₀ (ne_of_gt Q_pos)
  rw [hz,realAffine_scalar,hbR]
  simp_rw [hwR,hy]
  simp only [mul_add,mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

#print axioms grid_affine_matches
end CertSound
