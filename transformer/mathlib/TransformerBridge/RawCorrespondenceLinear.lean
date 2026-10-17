import TransformerBridge.RawCorrespondenceSupport

/-! Shared finite linear algebra for subsequent field gates. No learned or frozen data. -/
namespace TransformerBridge.RawCorrespondence

open TransformerBridge.RawPilot (contract contract_eq)

/-- Token and position contributions can be certified once and combined symbolically. -/
theorem contract_add_left {m : Nat} (x y w : Fin m → Int) :
    contract (fun d => x d + y d) w = contract x w + contract y w := by
  simp only [contract_eq, add_mul, Finset.sum_add_distrib]

/-- Move a projection onto the shared matrix rather than re-evaluate each site. -/
theorem contract_compose {m n : Nat} (x : Fin m → Int)
    (A : Fin m → Fin n → Int) (w : Fin n → Int) :
    contract (fun i => contract x (fun d => A d i)) w =
      contract x (fun d => contract (A d) w) := by
  simp only [contract_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The fixed query collapses score verification to a linear function of xhat. -/
theorem score_composed (W : Transformer.Weights) (h : Fin 4) (j : Fin 3) (tk : Fin 114) :
    W.score h j tk = contract (W.xhat tk j)
      (fun d => contract (W.WK h d) (W.qvec h)) := by
  unfold Transformer.Weights.score Transformer.Weights.kvec
  simp only [contract_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- All vvec inputs split into the same token contribution plus a position contribution. -/
theorem vvec_split (W : Transformer.Weights) (h : Fin 4) (tk : Fin 114)
    (j : Fin 3) (l : Fin 32) :
    W.vvec h tk j l = contract (W.tok tk) (fun d => W.WV h d l) +
      contract (W.pos j) (fun d => W.WV h d l) := by
  simp only [Transformer.Weights.vvec, Transformer.Weights.xhat, contract_eq,
    add_mul, Finset.sum_add_distrib]

/-- TI and TU share both projections; the destination matrix is the only parameter. -/
theorem output_composed {n : Nat} (W : Transformer.Weights) (h : Fin 4)
    (tk : Fin 114) (j : Fin 3) (M : Fin 128 → Fin n → Int) (i : Fin n) :
    contract (W.ovec h tk j) (fun d => M d i) =
      contract (W.xhat tk j) (fun d => contract (W.WV h d)
        (fun l => contract (W.WO h l) (fun e => M e i))) := by
  have hO : W.ovec h tk j =
      (fun d => contract (W.vvec h tk j) (fun l => W.WO h l d)) := by
    funext d
    exact (contract_eq _ _).symm
  rw [hO, contract_compose]
  have hV : W.vvec h tk j =
      (fun l => contract (W.xhat tk j) (fun d => W.WV h d l)) := by
    funext l
    exact (contract_eq _ _).symm
  rw [hV, contract_compose]

/-- A single token certificate serves every position, plus three position corrections. -/
theorem xhat_contract_split (W : Transformer.Weights) (tk : Fin 114)
    (j : Fin 3) (w : Fin 128 → Int) :
    contract (W.xhat tk j) w = contract (W.tok tk) w + contract (W.pos j) w := by
  exact contract_add_left (W.tok tk) (W.pos j) w

/-- The same certified O128 vector serves both TI512 and TU113. -/
theorem TU_of_ovec (W : Transformer.Weights) (S : Nat) (h : Fin 4) (tk : Fin 114) (j : Fin 3)
    (o : Fin 128 → Int) (ho : ∀ d, W.ovec h tk j d = o d)
    (valid : ¬ (j = 2 ∧ tk ≠ 113)) (k : Fin 113) :
    (W.rawTables S).TU h j tk k = contract o (fun d => W.U d k) := by
  change (if j = 2 ∧ tk ≠ 113 then 0 else ∑ d, W.ovec h tk j d * W.U d k) = _
  rw [ite_eq_right valid, contract_eq]
  apply Finset.sum_congr rfl
  intro d _
  rw [ho]

/-- CU113 uses one combined scaled residual/bout input and the same U rows as TU and G. -/
theorem CU_of_contract (W : Transformer.Weights) (S : Nat) (k : Fin 113) :
    (W.rawTables S).CU k = contract
      (fun d => (S : Int) ^ 4 * W.xhat 113 2 d + W.bout d) (fun d => W.U d k) := by
  rw [contract_add_left, contract_scale, contract_eq, contract_eq]
  rfl

/-- G512x113 has the identical U contraction contract, one Wout row per input. -/
theorem G_of_contract (W : Transformer.Weights) (S : Nat) (i : Fin 512) (k : Fin 113) :
    (W.rawTables S).G i k = contract (W.Wout i) (fun d => W.U d k) := by
  rw [contract_eq]
  rfl

end TransformerBridge.RawCorrespondence
