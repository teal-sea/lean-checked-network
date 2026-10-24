import Mathlib
import ACASChecked.Coverage
namespace TreePilot

/-- Box membership in coordinates already multiplied by the positive grid scale. -/
def InBox (b : Box) (x : Nat → ℝ) : Prop :=
  ∀ i (hi : i < b.length), (b[i].1 : ℝ) ≤ x i ∧ x i ≤ (b[i].2 : ℝ)

theorem inBox_set (b : Box) (x : Nat → ℝ) (hb : InBox b x)
    (d : Nat) (p : Int × Int) (hp : (p.1 : ℝ) ≤ x d ∧ x d ≤ (p.2 : ℝ)) :
    InBox (b.set d p) x := by
  intro i hi
  have hib : i < b.length := by simpa using hi
  by_cases hid : d = i
  · subst i
    simpa using hp
  · simpa [List.getElem_set, hid] using hb i hib

theorem split_covers (b : Box) (x : Nat → ℝ) (hb : InBox b x)
    (d : Nat) (hd : d < b.length) (c : Int) :
    InBox (b.set d (b[d].1,c)) x ∨ InBox (b.set d (c,b[d].2)) x := by
  rcases le_total (x d) (c : ℝ) with h | h
  · exact Or.inl (inBox_set b x hb d _ ⟨(hb d hd).1,h⟩)
  · exact Or.inr (inBox_set b x hb d _ ⟨h,(hb d hd).2⟩)

theorem visit_covers (nodes : Array Node) (fuel i : Nat) (box : Box)
    (seen done : List Nat) (h : visit nodes fuel i box seen = some done)
    (x : Nat → ℝ) (hx : InBox box x) :
    ∃ (j : Nat) (node : Node), nodes[j]? = some node ∧ node.kind = .leaf ∧ InBox node.box x := by
  induction fuel generalizing i box seen done with
  | zero => simp [visit] at h
  | succ fuel ih =>
    simp only [visit] at h
    split at h
    · simp at h
    · cases hn : nodes[i]? with
      | none => simp [hn] at h
      | some node =>
        simp only [hn] at h
        dsimp only [Bind.bind, Option.bind] at h
        split at h
        · simp at h
        · rename_i hb
          have hbox : node.box = box := by simpa using hb
          cases hk : node.kind with
          | leaf => exact ⟨i,node,hn,hk,hbox ▸ hx⟩
          | split d c left right =>
            simp only [hk] at h
            split at h
            · simp at h
            · rename_i hd
              have hdim : d < box.length := by
                have hh : (decide (d < box.length) && left != right) = true := by
                  simpa using hd
                have hh' := Bool.and_eq_true_iff.mp hh
                exact of_decide_eq_true hh'.1
              split at h
              · simp at h
              · simp only [getElem!_pos box d hdim] at h
                cases hl : visit nodes fuel left (box.set d (box[d].1,c)) (i::seen) with
                | none => simp [hl] at h
                | some mid =>
                  simp only [hl] at h
                  rcases split_covers box x hx d hdim c with hxl | hxr
                  · apply ih left _ (i::seen) mid hl
                    exact hxl
                  · apply ih right _ mid done h
                    exact hxr

theorem check_covers (root : Box) (nodes : Array Node) (h : check root nodes = true)
    (x : Nat → ℝ) (hx : InBox root x) :
    ∃ (j : Nat) (node : Node), nodes[j]? = some node ∧ node.kind = .leaf ∧ InBox node.box x := by
  unfold check at h
  have hh := Bool.and_eq_true_iff.mp h
  cases hv : visit nodes nodes.size 0 root [] with
  | none => simp [hv] at hh
  | some done => exact visit_covers nodes nodes.size 0 root [] done hv x hx

#print axioms check_covers
#print axioms split_covers
#print axioms visit_covers
end TreePilot
