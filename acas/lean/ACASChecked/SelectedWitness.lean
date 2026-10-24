import ACASChecked.RawColumns
noncomputable section
namespace CertSound
open RouteA RouteNC Finset

def sideSign (e : Fin 2) : Int := if e.val = 0 then 1 else -1
def targetCol (t : Nat) (j : Fin 50) (e : Fin 2) (k : Nat) : Nat :=
  100*(t-1-k)+2*j.val+e.val

theorem targetCol_lt (t : Nat) (ht : t ≤ 5) (j : Fin 50) (e : Fin 2) (k : Nat) (hk : k < t) :
    targetCol t j e k < columns k := by
  dsimp [targetCol,columns]
  omega

theorem targetCol_step (t : Nat) (j : Fin 50) (e : Fin 2) (k : Nat) (hk : k < t-1) :
    targetCol t j e k = 100 + targetCol t j e (k+1) := by
  dsimp [targetCol]
  omega

def RawReceipt.selected (r : RawReceipt) (t : Nat) (j : Fin 50) (e : Fin 2) : DualWitness r.net t where
  nu k i := matrix (r.v k) i (targetCol t j e k)
  c k i := if k = t then sideSign e*Q*matrix (r.w t) i j else matrix (r.c k) i (targetCol t j e k)
  r k := (r.cost k).getD (targetCol t j e k) 0
  s k := (r.s k).getD (targetCol t j e k) 0
  beta := sideSign e*Q*Q*(r.b t).getD j 0
  claim := r.claims.getD (targetCol t j e 0) 0

theorem RawReceipt.Valid.selected_a {r : RawReceipt} (h : r.Valid)
    (t : Nat) (ht : 0 < t) (ht5 : t ≤ 5) (j : Fin 50) (e : Fin 2)
    (k : Nat) (hk : k < t) (i : Fin 50) :
    matrix (r.a k) i (targetCol t j e k) = (r.selected t j e).c (k+1) i := by
  by_cases he : k+1 = t
  · subst t
    have hcol : targetCol (k+1) j e k = 2*j.val+e.val := by dsimp [targetCol]; omega
    rw [hcol]
    fin_cases e
    · simpa only [RawReceipt.selected, sideSign, Fin.val_zero, Fin.val_mk, zero_add,
        add_zero, ite_true, one_mul] using h.a_even k (by omega) i j
    · have hh := h.a_odd k (by omega) i j
      simpa [RawReceipt.selected, sideSign] using hh
  · have hk' : k < t-1 := by omega
    rw [targetCol_step t j e k hk']
    have hh := h.a_back k (by omega) i
      ⟨targetCol t j e (k+1),targetCol_lt t ht5 j e (k+1) (by omega)⟩
    simpa only [RawReceipt.selected, RawReceipt.net, dim, if_neg he] using hh

theorem RawReceipt.Valid.selected_valid {r : RawReceipt} (h : r.Valid)
    (t : Nat) (ht : 0 < t) (ht5 : t ≤ 5) (j : Fin 50) (e : Fin 2) :
    (r.selected t j e).Valid r.lower r.upper
      (fun i => r.boxl.getD i 0) (fun i => r.boxu.getD i 0) j (sideSign e) := by
  constructor
  · intro k hk i
    have hh := h.balance k (by omega) i ⟨targetCol t j e k,targetCol_lt t ht5 j e k hk⟩
    dsimp only [RawReceipt.selected, RawReceipt.net, dim]
    rw [if_neg (show k ≠ t by omega)]
    exact hh
  · intro k hk
    have hh := h.cost_col k (by omega) ⟨targetCol t j e k,targetCol_lt t ht5 j e k hk⟩
    change (r.cost k).getD (targetCol t j e k) 0 = _
    rw [hh]
    apply sum_congr rfl
    intro i _
    rw [h.selected_a t ht ht5 j e k hk i]
    rfl
  · intro k hk
    have he := targetCol_step t j e k hk
    change (r.s k).getD (targetCol t j e k) 0 =
      (r.s (k+1)).getD (targetCol t j e (k+1)) 0 + (r.cost k).getD (targetCol t j e k) 0
    rw [he,h.s_back k (by omega)]
  · have hk : t-1 < 5 := by omega
    have he : targetCol t j e (t-1) = 2*j.val+e.val := by dsimp [targetCol]; omega
    have hit : t-1+1 = t := by omega
    change (r.s (t-1)).getD (targetCol t j e (t-1)) 0 =
      sideSign e*Q*Q*(r.b t).getD j 0 + (r.cost (t-1)).getD (targetCol t j e (t-1)) 0
    rw [he]
    fin_cases e
    · simpa [sideSign,hit] using h.s_even (t-1) hk j
    · have hh := h.s_odd (t-1) hk j
      simpa [sideSign,hit] using hh
  · have hc := h.claim_col ⟨targetCol t j e 0,by have := targetCol_lt t ht5 j e 0 ht; simpa [columns] using this⟩
    dsimp only [RawReceipt.selected, RawReceipt.net, dim]
    simp only [if_neg (show 0 ≠ t by omega)]
    exact hc
  · intro i
    simp only [RawReceipt.selected, ite_true]
  · rfl

#print axioms RawReceipt.Valid.selected_valid
end CertSound
