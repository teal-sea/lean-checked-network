import ACASChecked.PackingBridge
import ACASChecked.RealRules
namespace CertSound
open RouteA RouteNC Finset

noncomputable def minZ (l u a n : Int) : Int :=
  let nq := n * Q
  let ml := (if l ≤ 0 then -nq else a-nq)*l
  let mu := (if u ≤ 0 then -nq else a-nq)*u
  if l ≤ 0 ∧ 0 ≤ u then min 0 (min ml mu) else min ml mu

theorem minZ_endpoints (l u a n : Int) :
    minZ l u a n ≤ a * max 0 l - n*Q*l ∧
    minZ l u a n ≤ a * max 0 u - n*Q*u ∧
    (l ≤ 0 ∧ 0 ≤ u → minZ l u a n ≤ 0) := by
  have he : ∀ x : Int, (if x ≤ 0 then -(n*Q) else a-n*Q)*x =
      a * max 0 x - n*Q*x := by
    intro x
    split_ifs with hx
    · rw [max_eq_left hx]; ring
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hx))]; ring
  unfold minZ
  simp only [he]
  split_ifs with h
  · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _), fun _ => min_le_left _ _⟩
  · exact ⟨min_le_left _ _, min_le_right _ _, fun hh => (h hh).elim⟩

theorem minZ_sound (l u a n : Int) (z : ℝ) (hl : (l : ℝ) ≤ z) (hu : z ≤ (u : ℝ)) :
    (minZ l u a n : ℝ) ≤ (a : ℝ) * max 0 z - (n : ℝ)*(Q : ℝ)*z := by
  have hh := minZ_endpoints l u a n
  apply residual_bound (a : ℝ) ((n : ℝ)*(Q : ℝ)) l u z (minZ l u a n) hl hu
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2.1
  · intro h
    have hh0 : l ≤ 0 ∧ 0 ≤ u := by exact_mod_cast h
    exact_mod_cast hh.2.2 hh0

theorem zipI_ofFn {t : Nat} (f : Int → Int → Int) (a b : Fin t → Int) :
    zipI f (List.ofFn a) (List.ofFn b) = List.ofFn (fun j => f (a j) (b j)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [List.ofFn_succ]
    change f (a 0) (b 0) :: zipI f (List.ofFn (fun i => a i.succ))
      (List.ofFn (fun i => b i.succ)) = _
    rw [ih]

theorem minima_ofFn {t : Nat} (l u : Int) (a n : Fin t → Int) :
    minima l u (List.ofFn a) (List.ofFn n) = List.ofFn (fun j => minZ l u (a j) (n j)) := by
  unfold minima
  rw [zipI_ofFn]
  apply congrArg List.ofFn
  funext j
  rfl

#print axioms minZ_sound
#print axioms minima_ofFn
end CertSound
