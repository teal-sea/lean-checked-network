import TransformerBridge.Row0
import TransformerBridge.Pointwise
import TransformerBridge.FrozenBounds

namespace TransformerBridge

/-- Strict mq maximum and first argmax for ROW0 only, using the concrete frozen hB proof.
This is the fused quantized real-softmax model, not an identity with the FP checkpoint. -/
theorem row0_mq_argmax (b : Fin 113) :
    (∀ k, k ≠ Transformer.ans 0 b →
      Transformer.mq (toTables TransformerCore.Net.tab) 256 32 0 b k <
        Transformer.mq (toTables TransformerCore.Net.tab) 256 32 0 b (Transformer.ans 0 b)) ∧
    Transformer.argmaxFirst (Transformer.mq (toTables TransformerCore.Net.tab) 256 32 0 b) =
      Transformer.ans 0 b := by
  exact Transformer.real_model_adds_mod_113_pointwise Transformer.chosen
    (by decide) (by decide) (by decide) Transformer.clamp_chosen 2 Transformer.deltaBound_chosen
    (toTables TransformerCore.Net.tab) Transformer.chosenBounds frozen_tables_bounded
    256 (by norm_num) 0 b (row0_integer_margin b)

end TransformerBridge
