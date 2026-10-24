"""Assemble the leaf safety adapters and universal theorem from terminal IDs."""
def render(ids):
 s='import FrozenAcceptance\nimport FrozenParameters\n'+''.join(f'import Instances.Leaf{i}\n' for i in ids)
 s+='noncomputable section\nopen Spec TorchLean TorchLean.Tensor CertSound ACASCoverage TreePilot\nnamespace ACASChecked\n'
 for i in ids:
  s+=f'''theorem leafSafe{i} (x : Tensor ℝ [5]) (hx : InBox (nodes[{i}]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance{i}.raw.boxl.zip Instance{i}.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf{i}.boxl.zip Leaf{i}.boxu) (scaledPoint x)
    rw [boxMatches{i}]
    exact hx
  exact frozen_leaf_safe Instance{i}.raw Instance{i}.valid rfl rfl x hb (FrozenLink.model_correspondence x)

'''
 s+='''end ACASChecked

namespace ACASChecked

theorem acas_1_1_property1 : Frozen.ACASXu_1_1_Property1 := by
  apply ACASCoverage.finish
  intro j hmem x hbox
  simp only [ACASCoverage.leafIds,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with '''+' | '.join('hj' for _ in ids)+'\n'
 s+=''.join(f'  · subst j\n    exact ACASChecked.leafSafe{i} x hbox\n' for i in ids)
 return s+'\n#print axioms acas_1_1_property1\n\nend ACASChecked\n'
