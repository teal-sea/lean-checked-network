import ACASChecked.GridNetwork
noncomputable section
namespace CertSound
open RouteNC Finset

def GridNetwork.runY (g : GridNetwork) (input : Fin (g.dim 0) → ℝ) : ∀ k, Fin (g.dim k) → ℝ
  | 0 => input
  | k+1 => fun j => max 0 (((Q : ℝ)*(g.b k j : ℝ) +
      ∑ i, (g.w k j i : ℝ)*g.runY input k i)/(Q : ℝ))

def GridNetwork.run (g : GridNetwork) (input : Fin (g.dim 0) → ℝ) : GridExecution g where
  y := g.runY input
  z k j := ((Q : ℝ)*(g.b k j : ℝ) + ∑ i, (g.w k j i : ℝ)*g.runY input k i)/(Q : ℝ)
  affine k j := by
    field_simp [ne_of_gt Q_pos]
  relu k j := rfl

#print axioms GridNetwork.run
end CertSound
