import ACASChecked.Injectivity
open Finset
namespace RouteA
/-- The mathematical certificate rule used by each packed output coordinate.
The executable list/offset bridge remains a separate obligation. -/
theorem packed_product_sound {n t : Nat} (B K G H : Int)
 (w : Fin n → Int) (v : Fin n → Fin t → Int) (c : Fin t → Int)
 (hbase : 2*K < B) (hg : 0 ≤ G) (hh : 0 ≤ H)
 (hw : ∀ i, |w i| ≤ G) (hv : ∀ i j, |v i j| ≤ H)
 (hc : ∀ j, |c j| ≤ K) (hsize : (n : Int)*G*H ≤ K)
 (he : ∑ j, c j * B^(j : Nat) = ∑ i, w i * ∑ j, v i j * B^(j : Nat)) :
 ∀ j, c j = ∑ i, w i * v i j := by
 apply packed_inj B K hbase t c (fun j => ∑ i, w i * v i j) hc
 · intro j
   calc |∑ i, w i * v i j| ≤ ∑ i, |w i * v i j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, G*H := sum_le_sum (fun i _ => by
          rw [abs_mul]; exact mul_le_mul (hw i) (hv i j) (abs_nonneg _) hg)
        _ = (n : Int)*G*H := by simp; ring
        _ ≤ K := hsize
 · rw [he]
   simp_rw [mul_sum, sum_mul]
   rw [sum_comm]
   apply sum_congr rfl
   intro i _
   apply sum_congr rfl
   intro j _
   ring
#print axioms packed_product_sound
end RouteA
