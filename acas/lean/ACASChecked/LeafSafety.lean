import ACASChecked.GridNetwork
import ACASChecked.EndpointCheck
namespace CertSound
open RouteA RouteNC

/-- Activation bounds consumed by the next affine layer. -/
def previousLo {g : GridNetwork} (box : Fin (g.dim 0) → Int)
    (l : ∀ k, Fin (g.dim (k+1)) → Int) : ∀ k, Fin (g.dim k) → Int
  | 0 => box
  | k+1 => fun i => max 0 (l k i)

def previousHi {g : GridNetwork} (box : Fin (g.dim 0) → Int)
    (u : ∀ k, Fin (g.dim (k+1)) → Int) : ∀ k, Fin (g.dim k) → Int
  | 0 => box
  | k+1 => fun i => max 0 (u k i)

/-- All tightened hidden endpoints follow in dependency order from the arithmetic receipts. -/
theorem leaf_enclosures (g : GridNetwork) (H : Nat)
    (l u : ∀ k, Fin (g.dim (k+1)) → Int)
    (boxl boxu : Fin (g.dim 0) → Int) (claims : Nat → List Int)
    (lower upper : ∀ k, Fin (g.dim (k+1)) → DualWitness g k)
    (hchecks : ∀ k < H, checkEndpoints (List.ofFn (l k)) (List.ofFn (u k))
      (List.ofFn (fun j => List.ofFn (g.w k j))) (List.ofFn (g.b k))
      (List.ofFn (previousLo boxl l k)) (List.ofFn (previousHi boxu u k))
      (claims k) (decide (k = 0)) = true)
    (hlower : ∀ k < H, 0 < k → ∀ j, (lower k j).Valid l u boxl boxu j 1 ∧
      (lower k j).claim = (claims k).getD (2*j.val) 0)
    (hupper : ∀ k < H, 0 < k → ∀ j, (upper k j).Valid l u boxl boxu j (-1) ∧
      (upper k j).claim = (claims k).getD (2*j.val+1) 0)
    (e : GridExecution g)
    (hbox : ∀ i, (boxl i : ℝ) ≤ e.y 0 i ∧ e.y 0 i ≤ (boxu i : ℝ)) :
    ∀ k < H, ∀ j, (l k j : ℝ) ≤ e.z k j ∧ e.z k j ≤ (u k j : ℝ) := by
  apply dependency_order (fun k => ∀ j, (l k j : ℝ) ≤ e.z k j ∧ e.z k j ≤ (u k j : ℝ)) H
  intro k hk ih
  apply checkEndpoints_sound (g.w k) (g.b k) (l k) (u k)
    (previousLo boxl l k) (previousHi boxu u k) (claims k) (decide (k=0)) (hchecks k hk)
    (e.y k) (e.z k)
  · cases k with
    | zero => exact hbox
    | succ k =>
      intro i
      have hh := ih k (by omega) i
      rw [e.relu k i]
      simp only [previousLo, previousHi, Int.cast_max, Int.cast_zero]
      exact ⟨max_le_max le_rfl hh.1, max_le_max le_rfl hh.2⟩
  · intro j
    simpa only [mul_comm (g.b k j : ℝ) (Q : ℝ)] using e.affine k j
  · intro hfirst j
    have hkp : 0 < k := by
      by_contra hn
      have he : k = 0 := by omega
      simp [he] at hfirst
    have hl := (lower k j).sound hkp l u boxl boxu j 1 (hlower k hk hkp j).1 e ih hbox
    have hu := (upper k j).sound hkp l u boxl boxu j (-1) (hupper k hk hkp j).1 e ih hbox
    rw [(hlower k hk hkp j).2] at hl
    rw [(hupper k hk hkp j).2] at hu
    constructor
    · simpa using hl
    · simpa using hu

/-- Close a real strict output bound after every endpoint dependency is justified. -/
theorem leaf_safe (g : GridNetwork) (H : Nat) (hH : 0 < H)
    (l u : ∀ k, Fin (g.dim (k+1)) → Int)
    (boxl boxu : Fin (g.dim 0) → Int)
    (v : DualWitness g H) (j : Fin (g.dim (H+1)))
    (hv : v.Valid l u boxl boxu j (-1))
    (e : GridExecution g) (value : ℝ) (hvalue : e.z H j = (Q : ℝ)*value)
    (hencl : ∀ k < H, ∀ j, (l k j : ℝ) ≤ e.z k j ∧ e.z k j ≤ (u k j : ℝ))
    (hbox : ∀ i, (boxl i : ℝ) ≤ e.y 0 i ∧ e.y 0 i ≤ (boxu i : ℝ))
    (hmargin : 0 < v.claim*1000000000000000 + 3991125645861615*(Q*Q*Q)) :
    value < (3991125645861615 : ℝ)/1000000000000000 := by
  have hh := v.sound hH l u boxl boxu j (-1) hv e hencl hbox
  rw [hvalue] at hh
  apply margin_sound v.claim 3991125645861615 1000000000000000 value (by norm_num) _ hmargin
  convert hh using 1 <;> push_cast <;> ring

#print axioms leaf_enclosures
#print axioms leaf_safe
end CertSound
