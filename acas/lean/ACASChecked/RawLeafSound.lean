import ACASChecked.SelectedWitness
import ACASChecked.FinalWitness
import ACASChecked.SliceLists
noncomputable section
namespace CertSound
open RouteA RouteNC Finset

theorem ofFn_nonneg (xs : List Int) (n : Nat) (hn : xs.length = n) :
    List.ofFn (fun i : Fin n => max 0 (xs.getD i 0)) = nonneg xs := by
  unfold nonneg
  conv_rhs => rw [← ofFn_getD xs 0 n hn, List.map_ofFn]
  rfl

theorem RawReceipt.Valid.transpose_eq {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6) :
    List.ofFn (fun j : Fin 50 => List.ofFn (fun i : Fin (dim k) => matrix (r.w k) i j)) = transpose (r.w k) := by
  have hd : 0 < dim k := by cases k <;> norm_num [dim]
  have hh := transpose_ofFn hd (fun i : Fin (dim k) => fun j : Fin 50 => matrix (r.w k) i j)
  rw [ofFn_matrix _ _ _ (h.wlen k hk) (h.wrows k hk)] at hh
  exact hh.symm

theorem RawReceipt.Valid.enclosures {r : RawReceipt} (h : r.Valid) (e : GridExecution r.net)
    (hbox : ∀ i : Fin (r.net.dim 0), (r.boxl.getD i 0 : ℝ) ≤ e.y 0 i ∧ e.y 0 i ≤ (r.boxu.getD i 0 : ℝ)) :
    ∀ k < 6, ∀ j, (r.lower k j : ℝ) ≤ e.z k j ∧ e.z k j ≤ (r.upper k j : ℝ) := by
  apply leaf_enclosures r.net 6 r.lower r.upper
    (fun i => r.boxl.getD i 0) (fun i => r.boxu.getD i 0)
    (fun k => (r.claims.drop (100*(k-1))).take 100)
    (fun k j => r.selected k j ⟨0,by omega⟩)
    (fun k j => r.selected k j ⟨1,by omega⟩) ?_ ?_ ?_ e hbox
  · intro k hk
    have hl : List.ofFn (r.lower k) = r.l k := ofFn_getD _ 0 50 (h.llen k hk)
    have hu : List.ofFn (r.upper k) = r.u k := ofFn_getD _ 0 50 (h.ulen k hk)
    have hb : List.ofFn (r.net.b k) = r.b k := ofFn_getD _ 0 50 (h.blen k hk)
    have hw : List.ofFn (fun j => List.ofFn (r.net.w k j)) = transpose (r.w k) := h.transpose_eq k hk
    have hpl : List.ofFn (previousLo (fun i => r.boxl.getD i 0) r.lower k) =
        if k = 0 then r.boxl else nonneg (r.l (k-1)) := by
      cases k with
      | zero => exact ofFn_getD _ 0 5 h.boxllen
      | succ k => exact ofFn_nonneg _ 50 (h.llen k (by omega))
    have hpu : List.ofFn (previousHi (fun i => r.boxu.getD i 0) r.upper k) =
        if k = 0 then r.boxu else nonneg (r.u (k-1)) := by
      cases k with
      | zero => exact ofFn_getD _ 0 5 h.boxulen
      | succ k => exact ofFn_nonneg _ 50 (h.ulen k (by omega))
    rw [hl,hu,hb,hw,hpl,hpu]
    exact h.endpoints k hk
  · intro k hk hkp j
    refine ⟨h.selected_valid k hkp (by omega) j ⟨0,by omega⟩,?_⟩
    dsimp only [RawReceipt.selected,targetCol,Fin.val_mk]
    rw [getD_take _ 100 _ _ (by have hj : j.val < 50 := j.isLt; omega),getD_drop] <;> congr 1 <;> omega
  · intro k hk hkp j
    refine ⟨h.selected_valid k hkp (by omega) j ⟨1,by omega⟩,?_⟩
    dsimp only [RawReceipt.selected,targetCol,Fin.val_mk]
    rw [getD_take _ 100 _ _ (by have hj : j.val < 50 := j.isLt; omega),getD_drop] <;> congr 1 <;> omega

theorem RawReceipt.Valid.safe {r : RawReceipt} (h : r.Valid) (e : GridExecution r.net)
    (hbox : ∀ i : Fin (r.net.dim 0), (r.boxl.getD i 0 : ℝ) ≤ e.y 0 i ∧ e.y 0 i ≤ (r.boxu.getD i 0 : ℝ))
    (value : ℝ) (hvalue : e.z 6 ⟨0,by change 0 < 50; omega⟩ = (Q : ℝ)*value) :
    value < (3991125645861615 : ℝ)/1000000000000000 := by
  exact leaf_safe r.net 6 (by omega) r.lower r.upper
    (fun i => r.boxl.getD i 0) (fun i => r.boxu.getD i 0)
    r.finalWitness ⟨0,by change 0 < 50; omega⟩ h.final_valid e value hvalue
    (h.enclosures e hbox) hbox h.margin

#print axioms RawReceipt.Valid.enclosures
#print axioms RawReceipt.Valid.safe
end CertSound
