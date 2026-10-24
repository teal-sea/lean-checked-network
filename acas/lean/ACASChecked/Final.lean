import ACASChecked.FrozenAcceptance
import ACASChecked.FrozenParameters
import ACASChecked.Instances.Leaf8
import ACASChecked.Instances.Leaf13
import ACASChecked.Instances.Leaf17
import ACASChecked.Instances.Leaf24
import ACASChecked.Instances.Leaf27
import ACASChecked.Instances.Leaf29
import ACASChecked.Instances.Leaf30
import ACASChecked.Instances.Leaf31
import ACASChecked.Instances.Leaf32
import ACASChecked.Instances.Leaf33
import ACASChecked.Instances.Leaf34
import ACASChecked.Instances.Leaf36
import ACASChecked.Instances.Leaf37
import ACASChecked.Instances.Leaf38
import ACASChecked.Instances.Leaf39
import ACASChecked.Instances.Leaf40
import ACASChecked.Instances.Leaf41
import ACASChecked.Instances.Leaf42
import ACASChecked.Instances.Leaf46
import ACASChecked.Instances.Leaf49
import ACASChecked.Instances.Leaf50
import ACASChecked.Instances.Leaf51
import ACASChecked.Instances.Leaf52
import ACASChecked.Instances.Leaf53
import ACASChecked.Instances.Leaf54
import ACASChecked.Instances.Leaf55
import ACASChecked.Instances.Leaf56
import ACASChecked.Instances.Leaf57
import ACASChecked.Instances.Leaf58
import ACASChecked.Instances.Leaf59
import ACASChecked.Instances.Leaf63
import ACASChecked.Instances.Leaf64
import ACASChecked.Instances.Leaf65
import ACASChecked.Instances.Leaf66
noncomputable section
open Spec TorchLean TorchLean.Tensor CertSound ACASCoverage TreePilot
namespace ACASChecked
theorem leafSafe8 (x : Tensor ℝ [5]) (hx : InBox (nodes[8]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance8.raw.boxl.zip Instance8.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf8.boxl.zip Leaf8.boxu) (scaledPoint x)
    rw [boxMatches8]
    exact hx
  exact frozen_leaf_safe Instance8.raw Instance8.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe13 (x : Tensor ℝ [5]) (hx : InBox (nodes[13]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance13.raw.boxl.zip Instance13.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf13.boxl.zip Leaf13.boxu) (scaledPoint x)
    rw [boxMatches13]
    exact hx
  exact frozen_leaf_safe Instance13.raw Instance13.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe17 (x : Tensor ℝ [5]) (hx : InBox (nodes[17]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance17.raw.boxl.zip Instance17.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf17.boxl.zip Leaf17.boxu) (scaledPoint x)
    rw [boxMatches17]
    exact hx
  exact frozen_leaf_safe Instance17.raw Instance17.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe24 (x : Tensor ℝ [5]) (hx : InBox (nodes[24]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance24.raw.boxl.zip Instance24.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf24.boxl.zip Leaf24.boxu) (scaledPoint x)
    rw [boxMatches24]
    exact hx
  exact frozen_leaf_safe Instance24.raw Instance24.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe27 (x : Tensor ℝ [5]) (hx : InBox (nodes[27]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance27.raw.boxl.zip Instance27.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf27.boxl.zip Leaf27.boxu) (scaledPoint x)
    rw [boxMatches27]
    exact hx
  exact frozen_leaf_safe Instance27.raw Instance27.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe29 (x : Tensor ℝ [5]) (hx : InBox (nodes[29]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance29.raw.boxl.zip Instance29.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf29.boxl.zip Leaf29.boxu) (scaledPoint x)
    rw [boxMatches29]
    exact hx
  exact frozen_leaf_safe Instance29.raw Instance29.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe30 (x : Tensor ℝ [5]) (hx : InBox (nodes[30]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance30.raw.boxl.zip Instance30.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf30.boxl.zip Leaf30.boxu) (scaledPoint x)
    rw [boxMatches30]
    exact hx
  exact frozen_leaf_safe Instance30.raw Instance30.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe31 (x : Tensor ℝ [5]) (hx : InBox (nodes[31]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance31.raw.boxl.zip Instance31.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf31.boxl.zip Leaf31.boxu) (scaledPoint x)
    rw [boxMatches31]
    exact hx
  exact frozen_leaf_safe Instance31.raw Instance31.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe32 (x : Tensor ℝ [5]) (hx : InBox (nodes[32]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance32.raw.boxl.zip Instance32.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf32.boxl.zip Leaf32.boxu) (scaledPoint x)
    rw [boxMatches32]
    exact hx
  exact frozen_leaf_safe Instance32.raw Instance32.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe33 (x : Tensor ℝ [5]) (hx : InBox (nodes[33]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance33.raw.boxl.zip Instance33.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf33.boxl.zip Leaf33.boxu) (scaledPoint x)
    rw [boxMatches33]
    exact hx
  exact frozen_leaf_safe Instance33.raw Instance33.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe34 (x : Tensor ℝ [5]) (hx : InBox (nodes[34]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance34.raw.boxl.zip Instance34.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf34.boxl.zip Leaf34.boxu) (scaledPoint x)
    rw [boxMatches34]
    exact hx
  exact frozen_leaf_safe Instance34.raw Instance34.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe36 (x : Tensor ℝ [5]) (hx : InBox (nodes[36]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance36.raw.boxl.zip Instance36.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf36.boxl.zip Leaf36.boxu) (scaledPoint x)
    rw [boxMatches36]
    exact hx
  exact frozen_leaf_safe Instance36.raw Instance36.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe37 (x : Tensor ℝ [5]) (hx : InBox (nodes[37]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance37.raw.boxl.zip Instance37.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf37.boxl.zip Leaf37.boxu) (scaledPoint x)
    rw [boxMatches37]
    exact hx
  exact frozen_leaf_safe Instance37.raw Instance37.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe38 (x : Tensor ℝ [5]) (hx : InBox (nodes[38]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance38.raw.boxl.zip Instance38.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf38.boxl.zip Leaf38.boxu) (scaledPoint x)
    rw [boxMatches38]
    exact hx
  exact frozen_leaf_safe Instance38.raw Instance38.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe39 (x : Tensor ℝ [5]) (hx : InBox (nodes[39]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance39.raw.boxl.zip Instance39.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf39.boxl.zip Leaf39.boxu) (scaledPoint x)
    rw [boxMatches39]
    exact hx
  exact frozen_leaf_safe Instance39.raw Instance39.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe40 (x : Tensor ℝ [5]) (hx : InBox (nodes[40]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance40.raw.boxl.zip Instance40.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf40.boxl.zip Leaf40.boxu) (scaledPoint x)
    rw [boxMatches40]
    exact hx
  exact frozen_leaf_safe Instance40.raw Instance40.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe41 (x : Tensor ℝ [5]) (hx : InBox (nodes[41]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance41.raw.boxl.zip Instance41.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf41.boxl.zip Leaf41.boxu) (scaledPoint x)
    rw [boxMatches41]
    exact hx
  exact frozen_leaf_safe Instance41.raw Instance41.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe42 (x : Tensor ℝ [5]) (hx : InBox (nodes[42]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance42.raw.boxl.zip Instance42.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf42.boxl.zip Leaf42.boxu) (scaledPoint x)
    rw [boxMatches42]
    exact hx
  exact frozen_leaf_safe Instance42.raw Instance42.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe46 (x : Tensor ℝ [5]) (hx : InBox (nodes[46]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance46.raw.boxl.zip Instance46.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf46.boxl.zip Leaf46.boxu) (scaledPoint x)
    rw [boxMatches46]
    exact hx
  exact frozen_leaf_safe Instance46.raw Instance46.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe49 (x : Tensor ℝ [5]) (hx : InBox (nodes[49]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance49.raw.boxl.zip Instance49.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf49.boxl.zip Leaf49.boxu) (scaledPoint x)
    rw [boxMatches49]
    exact hx
  exact frozen_leaf_safe Instance49.raw Instance49.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe50 (x : Tensor ℝ [5]) (hx : InBox (nodes[50]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance50.raw.boxl.zip Instance50.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf50.boxl.zip Leaf50.boxu) (scaledPoint x)
    rw [boxMatches50]
    exact hx
  exact frozen_leaf_safe Instance50.raw Instance50.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe51 (x : Tensor ℝ [5]) (hx : InBox (nodes[51]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance51.raw.boxl.zip Instance51.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf51.boxl.zip Leaf51.boxu) (scaledPoint x)
    rw [boxMatches51]
    exact hx
  exact frozen_leaf_safe Instance51.raw Instance51.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe52 (x : Tensor ℝ [5]) (hx : InBox (nodes[52]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance52.raw.boxl.zip Instance52.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf52.boxl.zip Leaf52.boxu) (scaledPoint x)
    rw [boxMatches52]
    exact hx
  exact frozen_leaf_safe Instance52.raw Instance52.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe53 (x : Tensor ℝ [5]) (hx : InBox (nodes[53]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance53.raw.boxl.zip Instance53.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf53.boxl.zip Leaf53.boxu) (scaledPoint x)
    rw [boxMatches53]
    exact hx
  exact frozen_leaf_safe Instance53.raw Instance53.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe54 (x : Tensor ℝ [5]) (hx : InBox (nodes[54]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance54.raw.boxl.zip Instance54.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf54.boxl.zip Leaf54.boxu) (scaledPoint x)
    rw [boxMatches54]
    exact hx
  exact frozen_leaf_safe Instance54.raw Instance54.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe55 (x : Tensor ℝ [5]) (hx : InBox (nodes[55]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance55.raw.boxl.zip Instance55.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf55.boxl.zip Leaf55.boxu) (scaledPoint x)
    rw [boxMatches55]
    exact hx
  exact frozen_leaf_safe Instance55.raw Instance55.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe56 (x : Tensor ℝ [5]) (hx : InBox (nodes[56]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance56.raw.boxl.zip Instance56.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf56.boxl.zip Leaf56.boxu) (scaledPoint x)
    rw [boxMatches56]
    exact hx
  exact frozen_leaf_safe Instance56.raw Instance56.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe57 (x : Tensor ℝ [5]) (hx : InBox (nodes[57]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance57.raw.boxl.zip Instance57.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf57.boxl.zip Leaf57.boxu) (scaledPoint x)
    rw [boxMatches57]
    exact hx
  exact frozen_leaf_safe Instance57.raw Instance57.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe58 (x : Tensor ℝ [5]) (hx : InBox (nodes[58]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance58.raw.boxl.zip Instance58.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf58.boxl.zip Leaf58.boxu) (scaledPoint x)
    rw [boxMatches58]
    exact hx
  exact frozen_leaf_safe Instance58.raw Instance58.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe59 (x : Tensor ℝ [5]) (hx : InBox (nodes[59]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance59.raw.boxl.zip Instance59.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf59.boxl.zip Leaf59.boxu) (scaledPoint x)
    rw [boxMatches59]
    exact hx
  exact frozen_leaf_safe Instance59.raw Instance59.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe63 (x : Tensor ℝ [5]) (hx : InBox (nodes[63]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance63.raw.boxl.zip Instance63.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf63.boxl.zip Leaf63.boxu) (scaledPoint x)
    rw [boxMatches63]
    exact hx
  exact frozen_leaf_safe Instance63.raw Instance63.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe64 (x : Tensor ℝ [5]) (hx : InBox (nodes[64]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance64.raw.boxl.zip Instance64.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf64.boxl.zip Leaf64.boxu) (scaledPoint x)
    rw [boxMatches64]
    exact hx
  exact frozen_leaf_safe Instance64.raw Instance64.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe65 (x : Tensor ℝ [5]) (hx : InBox (nodes[65]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance65.raw.boxl.zip Instance65.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf65.boxl.zip Leaf65.boxu) (scaledPoint x)
    rw [boxMatches65]
    exact hx
  exact frozen_leaf_safe Instance65.raw Instance65.valid rfl rfl x hb (FrozenLink.model_correspondence x)

theorem leafSafe66 (x : Tensor ℝ [5]) (hx : InBox (nodes[66]!).box (scaledPoint x)) :
    (Frozen.network.model.forward x).getScalar 0 < Frozen.threshold := by
  have hb : InBox (Instance66.raw.boxl.zip Instance66.raw.boxu) (scaledPoint x) := by
    change InBox (Leaf66.boxl.zip Leaf66.boxu) (scaledPoint x)
    rw [boxMatches66]
    exact hx
  exact frozen_leaf_safe Instance66.raw Instance66.valid rfl rfl x hb (FrozenLink.model_correspondence x)

end ACASChecked

namespace ACASChecked

theorem acas_1_1_property1 : Frozen.ACASXu_1_1_Property1 := by
  apply ACASCoverage.finish
  intro j hmem x hbox
  simp only [ACASCoverage.leafIds,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj | hj
  · subst j
    exact ACASChecked.leafSafe8 x hbox
  · subst j
    exact ACASChecked.leafSafe13 x hbox
  · subst j
    exact ACASChecked.leafSafe17 x hbox
  · subst j
    exact ACASChecked.leafSafe24 x hbox
  · subst j
    exact ACASChecked.leafSafe27 x hbox
  · subst j
    exact ACASChecked.leafSafe29 x hbox
  · subst j
    exact ACASChecked.leafSafe30 x hbox
  · subst j
    exact ACASChecked.leafSafe31 x hbox
  · subst j
    exact ACASChecked.leafSafe32 x hbox
  · subst j
    exact ACASChecked.leafSafe33 x hbox
  · subst j
    exact ACASChecked.leafSafe34 x hbox
  · subst j
    exact ACASChecked.leafSafe36 x hbox
  · subst j
    exact ACASChecked.leafSafe37 x hbox
  · subst j
    exact ACASChecked.leafSafe38 x hbox
  · subst j
    exact ACASChecked.leafSafe39 x hbox
  · subst j
    exact ACASChecked.leafSafe40 x hbox
  · subst j
    exact ACASChecked.leafSafe41 x hbox
  · subst j
    exact ACASChecked.leafSafe42 x hbox
  · subst j
    exact ACASChecked.leafSafe46 x hbox
  · subst j
    exact ACASChecked.leafSafe49 x hbox
  · subst j
    exact ACASChecked.leafSafe50 x hbox
  · subst j
    exact ACASChecked.leafSafe51 x hbox
  · subst j
    exact ACASChecked.leafSafe52 x hbox
  · subst j
    exact ACASChecked.leafSafe53 x hbox
  · subst j
    exact ACASChecked.leafSafe54 x hbox
  · subst j
    exact ACASChecked.leafSafe55 x hbox
  · subst j
    exact ACASChecked.leafSafe56 x hbox
  · subst j
    exact ACASChecked.leafSafe57 x hbox
  · subst j
    exact ACASChecked.leafSafe58 x hbox
  · subst j
    exact ACASChecked.leafSafe59 x hbox
  · subst j
    exact ACASChecked.leafSafe63 x hbox
  · subst j
    exact ACASChecked.leafSafe64 x hbox
  · subst j
    exact ACASChecked.leafSafe65 x hbox
  · subst j
    exact ACASChecked.leafSafe66 x hbox

#print axioms acas_1_1_property1

end ACASChecked
