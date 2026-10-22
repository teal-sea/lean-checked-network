import TransformerBridge.RawCorrespondence.SCFullAssembly
import TransformerBridge.RawCorrespondence.Generated.CI
import TransformerBridge.RawCorrespondence.CUFullGenerated.CU
import TransformerBridge.RawCorrespondence.GFullGenerated.Assembly
import TransformerBridge.Kronecker.Fields
import TransformerBridge.FrozenBounds
import TransformerBridge.InputAll

/-!
# The raw quantised model adds mod 113

`raw_model_adds_mod_113` states, with no hypotheses, that the real-softmax transformer built from
the raw integer weights `TransformerBridge.RawPackedPilot.weights` at scale `S = 256` puts its
strict maximum logit on `(a + b) % 113` for every input pair `(a, b)`, and that its first argmax
is that answer.

It is `Transformer.real_model_adds_mod_113_raw_chosen` applied to three facts about the frozen
tables `TransformerCore.Net.tab`:

* `tables_eq_raw` (`hT`): the frozen tables are exactly the tables computed from the raw weights.
  Its six fields come from separately checked certificates: `sc` (`SC_full`), `TI` and `TU`
  (`Kronecker.TI_eq`, `Kronecker.TU_eq`), `CI` (`CI_field`), `CU` (`CU_field`) and `G`
  (`G_field`).
* `frozen_tables_bounded` (`hB`): the frozen tables satisfy the entry bounds `chosenBounds`.
* `margin_all_pairs` (`hA`): on all 12,769 pairs the integer program's correct logit beats every
  other by more than twice the error bound `E` of the integer exponential.

The model is the quantised integer model with a real softmax. It is not the floating-point
checkpoint the integers were rounded from.
-/

set_option autoImplicit false

namespace TransformerBridge.FinalRaw

/-- **Full table identity** (`hT`). The frozen tables are exactly the tables built from the raw
integer weights at scale 256, in all six fields. -/
theorem tables_eq_raw :
    TransformerBridge.toTables TransformerCore.Net.tab =
      TransformerBridge.RawPackedPilot.weights.rawTables 256 :=
  TransformerBridge.RawCorrespondence.tables_eq _ _
    TransformerBridge.RawCorrespondence.SCFullAssembly.SC_full
    TransformerBridge.Kronecker.TI_eq
    TransformerBridge.Kronecker.TU_eq
    TransformerBridge.RawCorrespondence.Canonical.CI_field
    TransformerBridge.RawCorrespondence.CUFullCanonical.CU_field
    TransformerBridge.RawCorrespondence.GFullCanonical.G_field

/-- **All-pairs integer margin** (`hA`). The accepted `all_integer_margin`, with the error bound
`Ebound 256 32 2 chosenBounds` written as the literal that `real_model_adds_mod_113_raw_chosen`
expects. -/
theorem margin_all_pairs : ∀ a b : Fin 113, ∀ k, k ≠ Transformer.ans a b →
    Transformer.intLogits Transformer.chosen (TransformerBridge.toTables TransformerCore.Net.tab) 256 a b k
      + 2 * 416063585574805997938804232439435952711840399411200
      < Transformer.intLogits Transformer.chosen (TransformerBridge.toTables TransformerCore.Net.tab) 256 a b
          (Transformer.ans a b) := by
  intro a b k hk
  have hE : (Transformer.Ebound 256 Transformer.chosen.f 2 Transformer.chosenBounds : ℤ) =
      416063585574805997938804232439435952711840399411200 := by
    show (Transformer.Ebound 256 32 2 Transformer.chosenBounds : ℤ) = _
    rw [Transformer.Ebound_chosen]; rfl
  have h := TransformerBridge.all_integer_margin a b k hk
  rw [hE] at h
  exact h

/-- **The raw quantised model adds mod 113.** For every pair `(a, b)`, the real-softmax model
built from the raw integer weights at `S = 256` gives `(a + b) % 113` a strictly larger logit than
every other class, and its first argmax is `(a + b) % 113`. -/
theorem raw_model_adds_mod_113 :
    ∀ a b : Fin 113,
      (∀ k, k ≠ Transformer.ans a b →
        TransformerBridge.RawPackedPilot.weights.model 256 a b k <
          TransformerBridge.RawPackedPilot.weights.model 256 a b (Transformer.ans a b)) ∧
        Transformer.argmaxFirst (TransformerBridge.RawPackedPilot.weights.model 256 a b) =
          Transformer.ans a b :=
  Transformer.real_model_adds_mod_113_raw_chosen TransformerBridge.RawPackedPilot.weights
    (TransformerBridge.toTables TransformerCore.Net.tab) tables_eq_raw
    TransformerBridge.frozen_tables_bounded margin_all_pairs

end TransformerBridge.FinalRaw
