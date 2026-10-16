import Mathlib
import PhaseGrid.Network
import PhaseGrid.Trig

/-!
# The phase-grid network, defined

For a modulus `p`, a list of frequencies `S` and a scale `M`, the network has `8 |S|` neurons:
for each `k ∈ S`, the eight phase pairs `(j, l)` of `grid`, with `φ₁ = jπ/2` and `φ₂ = lπ/2`.
Its real weights are Gromov's analytic ones,
`E1[a] = cos(2πka/p + φ₁)`, `E2[b] = cos(2πkb/p + φ₂)`, `W2[c] = cos(2πkc/p + φ₁ + φ₂)`,
and its integer tables are those weights times `M`, rounded to the nearest integer
(`round x = ⌊x + 1/2⌋`). The network's answer is computed by `LeanCheckedNetwork.answer` from
`Network.lean`, copied verbatim from the first repository.
-/

namespace PhaseGrid
open Real

/-- The neurons for the frequency list `S`: for each `k ∈ S`, the eight phase pairs of `grid`,
as triples `(k, j, l)`. -/
def neurons (S : List ℕ) : List (ℕ × ℕ × ℕ) :=
  S.flatMap fun k => grid.map fun jl => (k, jl.1, jl.2)

theorem neurons_cons (k : ℕ) (S : List ℕ) :
    neurons (k :: S) = (grid.map fun jl => (k, jl.1, jl.2)) ++ neurons S := rfl

theorem neurons_length (S : List ℕ) : (neurons S).length = 8 * S.length := by
  induction S with
  | nil => rfl
  | cons k S ih =>
    rw [neurons_cons, List.length_append, ih, List.length_map, List.length_cons]
    simp [grid]; ring

/-- The angle `2πkx/p`. -/
noncomputable def θ (p k x : ℕ) : ℝ := 2 * π * k * x / p

/-- Real weight of neuron `(k, j, l)` for the first input `a`: `cos(2πka/p + jπ/2)`. -/
noncomputable def rE1 (p a : ℕ) (n : ℕ × ℕ × ℕ) : ℝ := cos (θ p n.1 a + n.2.1 * (π / 2))

/-- Real weight of neuron `(k, j, l)` for the second input `b`: `cos(2πkb/p + lπ/2)`. -/
noncomputable def rE2 (p b : ℕ) (n : ℕ × ℕ × ℕ) : ℝ := cos (θ p n.1 b + n.2.2 * (π / 2))

/-- Real read-out weight of neuron `(k, j, l)` for the answer `c`: `cos(2πkc/p + jπ/2 + lπ/2)`. -/
noncomputable def rW2 (p c : ℕ) (n : ℕ × ℕ × ℕ) : ℝ :=
  cos (θ p n.1 c + n.2.1 * (π / 2) + n.2.2 * (π / 2))

/-- The integer embedding table of the first input: row `a` holds `round(M · rE1 p a n)` for each
neuron `n`. -/
noncomputable def E1 (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun a : Fin p => (neurons S).map fun n => round ((M : ℝ) * rE1 p a n)

/-- The integer embedding table of the second input. -/
noncomputable def E2 (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun b : Fin p => (neurons S).map fun n => round ((M : ℝ) * rE2 p b n)

/-- The integer read-out table: row `c` holds the weights of the answer `c`. -/
noncomputable def W2 (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun c : Fin p => (neurons S).map fun n => round ((M : ℝ) * rW2 p c n)

/-- The integer network's answer for `(a, b)`, computed by the first repository's `answer`. -/
noncomputable def answer (p : ℕ) (S : List ℕ) (M : ℕ) (a b : ℕ) : ℕ :=
  LeanCheckedNetwork.answer (E1 p S M) (E2 p S M) (W2 p S M) a b

/-- The real-valued score of the answer `c` for the pair `(a, b)`:
`Σ over neurons of W2[c] (E1[a] + E2[b])²`. -/
noncomputable def realScore (p : ℕ) (S : List ℕ) (a b c : ℕ) : ℝ :=
  ((neurons S).map fun n => rW2 p c n * (rE1 p a n + rE2 p b n) ^ 2).sum

/-- The integer score of the answer `c` for the pair `(a, b)`: what `Network.lean` computes. -/
noncomputable def intScore (p : ℕ) (S : List ℕ) (M : ℕ) (a b c : ℕ) : ℤ :=
  ((neurons S).map fun n => round ((M : ℝ) * rW2 p c n) *
    ((round ((M : ℝ) * rE1 p a n) + round ((M : ℝ) * rE2 p b n)) *
      (round ((M : ℝ) * rE1 p a n) + round ((M : ℝ) * rE2 p b n)))).sum

/-- The wave sum `Σ_{k ∈ S} cos(2πks/p)` at a real shift `s`. -/
noncomputable def waveSum (p : ℕ) (S : List ℕ) (s : ℝ) : ℝ :=
  (S.map fun k : ℕ => cos (2 * π * (k : ℝ) * s / p)).sum

/-- The gap `g(S) = |S| − max_{0 < s < p} Σ_{k ∈ S} cos(2πks/p)`. `p ≥ 2` makes the range of `s`
nonempty. -/
noncomputable def gap (p : ℕ) (hp : 2 ≤ p) (S : List ℕ) : ℝ :=
  S.length - (Finset.Ico 1 p).sup' ⟨1, by simp; omega⟩ fun s : ℕ => waveSum p S s

end PhaseGrid
