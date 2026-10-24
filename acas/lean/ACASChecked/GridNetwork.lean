import ACASChecked.DualSound
namespace CertSound
open Finset RouteNC

/-- Exact integer-grid parameters. The real semantics retain every real input. -/
structure GridNetwork where
  dim : Nat → Nat
  w : ∀ k, Fin (dim (k+1)) → Fin (dim k) → Int
  b : ∀ k, Fin (dim (k+1)) → Int

structure GridExecution (g : GridNetwork) where
  y : ∀ k, Fin (g.dim k) → ℝ
  z : ∀ k, Fin (g.dim (k+1)) → ℝ
  affine : ∀ k j, (Q : ℝ)*z k j = (Q : ℝ)*(g.b k j : ℝ) + ∑ i, (g.w k j i : ℝ)*y k i
  relu : ∀ k j, y (k+1) j = max 0 (z k j)

/-- Arbitrary supplied duals and balanced coefficients, for a selected target. -/
structure DualWitness (g : GridNetwork) (L : Nat) where
  nu : ∀ k, Fin (g.dim (k+1)) → Int
  c : ∀ k, Fin (g.dim k) → Int
  r : Nat → Int
  s : Nat → Int
  beta : Int
  claim : Int

/-- Arithmetic receipt obligations; no real-network safety is assumed. -/
structure DualWitness.Valid {g : GridNetwork} {L : Nat} (v : DualWitness g L)
    (l u : ∀ k, Fin (g.dim (k+1)) → Int)
    (boxl boxu : Fin (g.dim 0) → Int) (j : Fin (g.dim (L+1))) (sign : Int) : Prop where
  balance : ∀ k < L, ∀ i, v.c k i = ∑ j, g.w k j i*v.nu k j
  residual : ∀ k < L, v.r k = ∑ j, (minZ (l k j) (u k j) (v.c (k+1) j) (v.nu k j) + g.b k j*Q*v.nu k j)
  tail : ∀ k < L-1, v.s k = v.s (k+1) + v.r k
  last : v.s (L-1) = v.beta + v.r (L-1)
  input : v.claim = v.s 0 + ∑ i, min (v.c 0 i*boxl i) (v.c 0 i*boxu i)
  top : ∀ i, v.c L i = sign*Q*g.w L j i
  bias : v.beta = sign*Q*Q*g.b L j

theorem DualWitness.sound {g : GridNetwork} {L : Nat} (hL : 0 < L)
    (v : DualWitness g L) (l u : ∀ k, Fin (g.dim (k+1)) → Int)
    (boxl boxu : Fin (g.dim 0) → Int) (j : Fin (g.dim (L+1))) (sign : Int)
    (hv : v.Valid l u boxl boxu j sign) (e : GridExecution g)
    (hencl : ∀ k < L, ∀ j, (l k j : ℝ) ≤ e.z k j ∧ e.z k j ≤ (u k j : ℝ))
    (hbox : ∀ i, (boxl i : ℝ) ≤ e.y 0 i ∧ e.y 0 i ≤ (boxu i : ℝ)) :
    (v.claim : ℝ) ≤ (sign : ℝ)*(Q : ℝ)^2*e.z L j := by
  apply dual_receipt_sound g.dim L hL g.w g.b l u v.nu v.c e.y e.z boxl boxu
    v.r v.s v.beta v.claim _ (fun k _ => e.relu k) (fun k _ => e.affine k)
    hv.balance hencl hbox hv.residual hv.tail hv.last hv.input
  rw [hv.bias]
  simp only [hv.top, Int.cast_mul]
  have hz := e.affine L j
  rw [pow_two]
  calc
    (sign : ℝ)*Q*Q*(g.b L j : ℝ) + ∑ i, (sign : ℝ)*Q*(g.w L j i : ℝ)*e.y L i
        = (sign : ℝ)*(Q : ℝ)*((Q : ℝ)*(g.b L j : ℝ) + ∑ i, (g.w L j i : ℝ)*e.y L i) := by
          rw [mul_add, mul_sum]
          congr 1
          · ring
          · apply sum_congr rfl; intro i _; ring
    _ = (sign : ℝ)*(Q : ℝ)*((Q : ℝ)*e.z L j) := by rw [hz]
    _ = _ := by ring

#print axioms DualWitness.sound
end CertSound
