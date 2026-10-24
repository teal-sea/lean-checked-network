import ACASChecked.RawColumns
noncomputable section
namespace CertSound
open RouteA RouteNC Finset

def finalCol (k : Nat) : Nat := 100*(5-k)
def RawReceipt.finalWitness (r : RawReceipt) : DualWitness r.net 6 where
  nu k i := matrix (r.v k) i (finalCol k)
  c k i := if k = 6 then -Q*matrix (r.w 6) i 0 else matrix (r.c k) i (finalCol k)
  r k := (r.cost k).getD (finalCol k) 0
  s k := (r.s k).getD (finalCol k) 0
  beta := -(Q*Q)*(r.b 6).getD 0 0
  claim := r.claims.getD 500 0

theorem RawReceipt.Valid.final_a {r : RawReceipt} (h : r.Valid) (k : Nat) (hk : k < 6)
    (i : Fin 50) : matrix (r.a k) i (finalCol k) = r.finalWitness.c (k+1) i := by
  by_cases he : k = 5
  · subst k
    simpa only [RawReceipt.a, RawReceipt.finalWitness, finalCol, ite_true,
      Nat.sub_self, Nat.mul_zero] using h.afinalvalue i
  · have heq : finalCol k = 100 + finalCol (k+1) := by dsimp [finalCol]; omega
    rw [heq]
    have hh := h.a_back k (by omega) i ⟨finalCol (k+1),by dsimp [finalCol,columns]; omega⟩
    simpa only [RawReceipt.finalWitness, if_neg (show k+1 ≠ 6 by omega)] using hh

theorem RawReceipt.Valid.final_valid {r : RawReceipt} (h : r.Valid) :
    r.finalWitness.Valid r.lower r.upper (fun i => r.boxl.getD i 0) (fun i => r.boxu.getD i 0) (⟨0, by change 0 < 50; omega⟩) (-1) := by
  constructor
  · intro k hk i
    have hh := h.balance k hk i ⟨finalCol k,by dsimp [finalCol,columns]; omega⟩
    dsimp only [RawReceipt.finalWitness, RawReceipt.net, dim]
    rw [if_neg (show k ≠ 6 by omega)]
    exact hh
  · intro k hk
    have hh := h.cost_col k hk ⟨finalCol k,by dsimp [finalCol,columns]; omega⟩
    change (r.cost k).getD (finalCol k) 0 = _
    rw [hh]
    apply sum_congr rfl
    intro i _
    rw [h.final_a k hk i]
    rfl
  · intro k hk
    have heq : finalCol k = 100+finalCol (k+1) := by dsimp [finalCol]; omega
    change (r.s k).getD (finalCol k) 0 = (r.s (k+1)).getD (finalCol (k+1)) 0 + (r.cost k).getD (finalCol k) 0
    rw [heq,h.s_back k (by omega)]
  · exact h.s_last
  · have hh := h.claim_col ⟨500,by omega⟩
    dsimp only [RawReceipt.finalWitness, RawReceipt.net, dim, finalCol]
    exact hh
  · intro i
    simp [RawReceipt.finalWitness,RawReceipt.net]
  · simp [RawReceipt.finalWitness,RawReceipt.net]

#print axioms RawReceipt.Valid.final_valid
end CertSound
