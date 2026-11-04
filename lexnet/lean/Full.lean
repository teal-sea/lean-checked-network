/- Step 5: lexnet_correct.  The exact bidirectional semantics of the real weights equals the
   readable reference lexer on every byte list. -/
import lean.Fwd3
namespace Lexnet
open Hash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive FRel : List (List Int) → List Ref.Seen → Prop
  | nil : FRel [] []
  | cons {f c fs cs} : (∃ P : Pat, f = fvec P ∧ (P.w && P.n) = false ∧ Agree P c) →
      FRel fs cs → FRel (f :: fs) (c :: cs)

theorem fwd_all (bs : List Byte) : ∀ (h : FState) (s : Ref.Left), Rel h s →
    FRel (forwardFeatures h bs) (Ref.forwardPass s bs) := by
  induction bs with
  | nil => intro h s _; exact FRel.nil
  | cons b bs ih =>
    intro h s hr
    obtain ⟨hrel, P, hf, hx, hag⟩ := fwd_step h s b hr
    simp only [forwardFeatures, Ref.forwardPass]
    exact FRel.cons ⟨P, hf, hx, hag⟩ (ih _ _ hrel)

theorem bwd_all : ∀ (fs : List (List Int)) (cs : List Ref.Seen), FRel fs cs →
    (suffixPass fs).1 = encR (Ref.backwardPass cs).1 ∧ (suffixPass fs).2 = (Ref.backwardPass cs).2 := by
  intro fs cs h
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons f c fs cs hfc _ ih =>
    obtain ⟨P, hf, hx, hag⟩ := hfc
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨b1, b2⟩ := backward_ok P (Ref.backwardPass cs).1 hx
    rw [label_congr P c _ hag] at b1 b2
    simp only [suffixPass, Ref.backwardPass, hf, ih1, ih2]
    exact ⟨b1, by rw [b2]⟩

theorem rel_init : Rel initial {} := by
  refine ⟨by decide, by decide, rfl, rfl, ?_⟩
  refine ⟨by simp [valid], by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initial]
end Lexnet

open Lexnet in
theorem lexnet_correct (bs : List Byte) : exactClasses bs = Ref.referenceClasses bs := by
  have h := bwd_all _ _ (fwd_all bs initial {} rel_init)
  exact h.2

#print axioms lexnet_correct
