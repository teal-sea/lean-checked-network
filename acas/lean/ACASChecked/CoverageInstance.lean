import ACASChecked.CoverageSound
import ACASChecked.AllLeaves
import ACASChecked.Spec
import ACASChecked.SliceLists
noncomputable section
namespace ACASCoverage
open CertSound RouteNC TreePilot Spec TorchLean TorchLean.Tensor

def scaledPoint (x : Tensor ℝ [5]) (i : Nat) : ℝ :=
  if h : i < 5 then (Q : ℝ)*x.getScalar ⟨i,h⟩ else 0

theorem root_contains (x : Tensor ℝ [5])
    (h : ∀ i : Fin 5, Frozen.lo i ≤ x.getScalar i ∧ x.getScalar i ≤ Frozen.hi i) :
    InBox root (scaledPoint x) := by
  intro i hi
  have hi5 : i < 5 := by simpa only [root,List.length_cons,List.length_nil] using hi
  have hx := h ⟨i,hi5⟩
  interval_cases i
  all_goals
    norm_num [Frozen.lo,Frozen.hi,root,scaledPoint,Q] at hx ⊢
    constructor <;> nlinarith [hx.1,hx.2]

def leafIds : List Nat := [8,13,17,24,27,29,30,31,32,33,34,36,37,38,39,40,41,42,46,49,50,51,52,53,54,55,56,57,58,59,63,64,65,66]

theorem classified : ∀ i : Fin nodes.size,
    (match nodes[i].kind with | .leaf => true | _ => false) = true → i.val ∈ leafIds := by decide +kernel

theorem covered (x : Tensor ℝ [5])
    (h : ∀ i : Fin 5, Frozen.lo i ≤ x.getScalar i ∧ x.getScalar i ≤ Frozen.hi i) :
    ∃ (j : Nat) (node : Node), j ∈ leafIds ∧ nodes[j]? = some node ∧ InBox node.box (scaledPoint x) := by
  obtain ⟨j,node,hj,hkind,hbox⟩ := check_covers root nodes coverage_checked (scaledPoint x) (root_contains x h)
  have hjs : j < nodes.size := by
    by_contra hh
    have hn : nodes[j]? = none := by simp [Array.getElem?_eq_none (by omega : nodes.size ≤ j)]
    rw [hn] at hj
    contradiction
  have he : node = nodes[j] := by rw [Array.getElem?_eq_getElem hjs] at hj; exact (Option.some.inj hj).symm
  have hleaf := classified ⟨j,hjs⟩ (by
    change (match nodes[j].kind with | .leaf => true | _ => false) = true
    rw [←he,hkind])
  exact ⟨j,node,hleaf,hj,hbox⟩

theorem box_coordinates (l u : List Int) (hl : l.length = 5) (hu : u.length = 5)
    (x : Tensor ℝ [5]) (h : InBox (l.zip u) (scaledPoint x)) :
    ∀ i : Fin 5, (l.getD i 0 : ℝ) ≤ (Q : ℝ)*x.getScalar i ∧
      (Q : ℝ)*x.getScalar i ≤ (u.getD i 0 : ℝ) := by
  intro i
  have hi : i.val < (l.zip u).length := by simpa [hl,hu] using i.isLt
  have hx := h i hi
  rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
  simpa only [List.getElem_zip,scaledPoint,dif_pos i.isLt] using hx

theorem finish (hsafe : ∀ j ∈ leafIds, ∀ x : Tensor ℝ [5],
    InBox (nodes[j]!).box (scaledPoint x) →
      (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold) :
    Frozen.ACASXu_1_1_Property1 := by
  intro x hx
  obtain ⟨j,node,hmem,hnode,hbox⟩ := covered x hx
  have he : nodes[j]! = node := by
    have hjs : j < nodes.size := by
      by_contra hh
      have hz : nodes[j]? = none := Array.getElem?_eq_none (by omega)
      rw [hz] at hnode
      contradiction
    rw [getElem!_pos nodes j hjs]
    rw [Array.getElem?_eq_getElem hjs] at hnode
    exact Option.some.inj hnode
  apply hsafe j hmem x
  rw [he]
  exact hbox

#print axioms finish
#print axioms covered
#print axioms box_coordinates
end ACASCoverage
