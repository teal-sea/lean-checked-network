import ACASChecked.RawReceipt
noncomputable section
namespace CertSound
open RouteA RouteNC Finset

theorem RawReceipt.Valid.cost_col {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6)
    (j : Fin (columns k)) :
    (r.cost k).getD j 0 = ∑ i : Fin 50,
      (minZ ((r.l k).getD i 0) ((r.u k).getD i 0) (matrix (r.a k) i j) (matrix (r.v k) i j) +
        (r.b k).getD i 0 * Q * matrix (r.v k) i j) :=
  contrib_col_list 50 (columns k) _ _ _ _ _ (h.llen k hk) (h.ulen k hk) (h.blen k hk)
    (h.ashape k hk).1 (h.vlen k hk) (h.ashape k hk).2 (h.vrows k hk) j

theorem RawReceipt.Valid.balance {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6)
    (i : Fin (dim k)) (j : Fin (columns k)) :
    matrix (r.c k) i j = ∑ a : Fin 50, matrix (r.w k) i a * matrix (r.v k) a j := by
  have hp := block_sound_fin (m := dim k) (n := 50) (t := columns k) (by omega)
    (fun i a => matrix (r.w k) i a) (fun a j => matrix (r.v k) a j)
    (fun i j => matrix (r.c k) i j)
    (by simpa only [ofFn_matrix _ _ _ (h.wlen k hk) (h.wrows k hk),
      ofFn_matrix _ _ _ (h.vlen k hk) (h.vrows k hk),
      ofFn_matrix _ _ _ (h.clen k hk) (h.crows k hk)] using h.blocks k hk)
  exact hp i j

theorem RawReceipt.Valid.a_even {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (i j : Fin 50) : matrix (r.a k) i (2*j.val) = Q * matrix (r.w (k+1)) i j := by
  rw [h.a_eq k hk]
  unfold matrix
  rw [getD_ofFn]
  rw [getD_append_front _ _ _ _ (by simp; omega), signs_even, scale_getD, getD_ofFn]

theorem RawReceipt.Valid.a_odd {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (i j : Fin 50) : matrix (r.a k) i (2*j.val+1) = -(Q * matrix (r.w (k+1)) i j) := by
  rw [h.a_eq k hk]
  unfold matrix
  rw [getD_ofFn]
  rw [getD_append_front _ _ _ _ (by simp; omega), signs_odd, scale_getD, getD_ofFn]

theorem RawReceipt.Valid.a_back {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (i : Fin 50) (j : Fin (columns (k+1))) : matrix (r.a k) i (100+j.val) = matrix (r.c (k+1)) i j := by
  rw [h.a_eq k hk]
  unfold matrix
  rw [getD_ofFn]
  have he : (signs (scale Q (List.ofFn (fun j : Fin 50 => (r.w (k+1)).getD i [] |>.getD j 0)))).length = 100 := by simp
  rw [← he, getD_append_back]
  exact getD_ofFn _ j 0

theorem RawReceipt.Valid.s_even {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (j : Fin 50) : (r.s k).getD (2*j.val) 0 =
      Q*Q*(r.b (k+1)).getD j 0 + (r.cost k).getD (2*j.val) 0 := by
  rw [h.tails k hk, s_front _ _ _ _ (by rw [h.blen (k+1) (by omega)]; omega), signs_even]

theorem RawReceipt.Valid.s_odd {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (j : Fin 50) : (r.s k).getD (2*j.val+1) 0 =
      Q*Q*(-(r.b (k+1)).getD j 0) + (r.cost k).getD (2*j.val+1) 0 := by
  rw [h.tails k hk, s_front _ _ _ _ (by rw [h.blen (k+1) (by omega)]; omega), signs_odd]

theorem RawReceipt.Valid.s_back {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 5)
    (j : Nat) : (r.s k).getD (100+j) 0 =
      (r.s (k+1)).getD j 0 + (r.cost k).getD (100+j) 0 := by
  have hh := CertSound.s_back (r.b (k+1)) (r.s (k+1)) (r.cost k) j
  rw [h.blen (k+1) (by omega)] at hh
  simpa only [h.tails k hk] using hh

theorem RawReceipt.Valid.s_last {r : RawReceipt} (h : r.Valid) :
    (r.s 5).getD 0 0 = -(Q*Q)*(r.b 6).getD 0 0 + (r.cost 5).getD 0 0 := by
  rw [h.last, addV_getD, scale_getD]
  cases hb : r.b 6 <;> rfl

theorem RawReceipt.Valid.claim_col {r : RawReceipt} (h : r.Valid) (j : Fin 501) :
    r.claims.getD j 0 = (r.s 0).getD j 0 + ∑ i : Fin 5,
      min (matrix (r.c 0) i j * r.boxl.getD i 0) (matrix (r.c 0) i j * r.boxu.getD i 0) := by
  unfold RawReceipt.claims
  rw [addV_getD]
  rw [inputCost_col_list 5 501 _ _ _ h.boxllen h.boxulen (h.clen 0 (by omega))
    (h.crows 0 (by omega)) j]

#print axioms RawReceipt.Valid.balance
#print axioms RawReceipt.Valid.cost_col
end CertSound
