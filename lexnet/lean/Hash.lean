/- Base-64 word hashes over bytes.  Mentions no network quantity except the numeric code table,
   which is stated here independently (a-z 1..26, A-Z 27..52, 0-9 53..62, _ 63). -/
import lean.Reference
namespace Hash
open Ref

def code (c : Nat) : Int :=
  if 97 ≤ c ∧ c ≤ 122 then (c : Int) - 96
  else if 65 ≤ c ∧ c ≤ 90 then (c : Int) - 38
  else if 48 ≤ c ∧ c ≤ 57 then (c : Int) + 5
  else if c = 95 then 63 else 0

/-- Base-64 numeral of the codes of a byte list. -/
def H (w : List Nat) : Int := w.foldl (fun h c => 64 * h + code c) 0

/-- What the network keeps: first 8 bytes in one number, bytes 9.. in another. -/
def wordHash (w : List Nat) : Int × Int := (H (w.take 8), H (w.drop 8))

def valid (w : List Nat) : Prop := ∀ c ∈ w, isWordChar c = true

theorem code_range (c : Nat) (h : isWordChar c = true) : 1 ≤ code c ∧ code c ≤ 63 := by
  simp only [isWordChar, isLetter, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  unfold code; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem code_inj (c d : Nat) (hc : isWordChar c = true) (hd : isWordChar d = true) :
    code c = code d → c = d := by
  simp only [isWordChar, isLetter, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc hd
  unfold code; split <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> omega

theorem snoc_ind {P : List Nat → Prop} (h0 : P []) (h : ∀ w c, P w → P (w ++ [c])) : ∀ w, P w := by
  suffices ∀ n w, List.length w = n → P w from fun w => this _ w rfl
  intro n
  induction n with
  | zero => intro w hw; rw [List.length_eq_zero_iff.mp hw]; exact h0
  | succ n ih =>
    intro w hw
    rcases List.eq_nil_or_concat w with h1 | ⟨w', c, h1⟩
    · subst h1; exact h0
    · simp only [List.concat_eq_append] at h1; subst h1
      exact h w' c (ih w' (by simp at hw; omega))

theorem H_snoc (w : List Nat) (c : Nat) : H (w ++ [c]) = 64 * H w + code c := by
  simp [H, List.foldl_append]

theorem H_nonneg : ∀ w : List Nat, 0 ≤ H w := by
  intro w
  refine snoc_ind (P := fun w => 0 ≤ H w) (by simp [H]) ?_ w
  · intro w c ih
    rw [H_snoc]; unfold code; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem H_inj : ∀ (n : Nat) (a b : List Nat), a.length ≤ n → valid a → valid b → H a = H b → a = b := by
  intro n
  induction n with
  | zero =>
    intro a b ha va vb h
    have : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    rcases List.eq_nil_or_concat b with hb | ⟨b', e, hb⟩ <;> (try simp only [List.concat_eq_append] at hb)
    · exact hb.symm
    · exfalso; subst hb
      have := H_snoc b' e; have := H_nonneg b'
      have r := code_range e (vb e (by simp))
      simp [H] at h; simp [H] at *; omega
  | succ n ih =>
    intro a b ha va vb h
    rcases List.eq_nil_or_concat a with h1 | ⟨a', d, h1⟩ <;>
    rcases List.eq_nil_or_concat b with h2 | ⟨b', e, h2⟩ <;>
    (try simp only [List.concat_eq_append] at h1 h2)
    · rw [h1, h2]
    · exfalso; subst h1 h2
      have := H_snoc b' e; have := H_nonneg b'
      have r := code_range e (vb e (by simp))
      simp [H] at h; simp [H] at *; omega
    · exfalso; subst h1 h2
      have := H_snoc a' d; have := H_nonneg a'
      have r := code_range d (va d (by simp))
      simp [H] at h; simp [H] at *; omega
    · subst h1 h2
      have e1 := H_snoc a' d; have e2 := H_snoc b' e
      have rd := code_range d (va d (by simp)); have re := code_range e (vb e (by simp))
      have hh : 64 * H a' + code d = 64 * H b' + code e := by rw [← e1, ← e2]; exact h
      have : H a' = H b' := by omega
      have hde : code d = code e := by omega
      have := code_inj d e (va d (by simp)) (vb e (by simp)) hde
      have hl : a'.length ≤ n := by simp at ha; omega
      have := ih a' b' hl (fun c hc => va c (by simp [hc])) (fun c hc => vb c (by simp [hc])) ‹H a' = H b'›
      subst this; subst ‹d = e›; rfl

theorem wordHash_inj (a b : List Nat) (va : valid a) (vb : valid b) (h : wordHash a = wordHash b) : a = b := by
  simp only [wordHash, Prod.mk.injEq] at h
  have h1 := H_inj _ _ _ (List.length_take_le ..) (fun c hc => va c (List.mem_of_mem_take hc)) (fun c hc => vb c (List.mem_of_mem_take hc)) h.1
  have h2 := H_inj _ _ _ (Nat.le_refl _) (fun c hc => va c (List.mem_of_mem_drop hc)) (fun c hc => vb c (List.mem_of_mem_drop hc)) h.2
  calc a = a.take 8 ++ a.drop 8 := (List.take_append_drop 8 a).symm
    _ = b.take 8 ++ b.drop 8 := by rw [h1, h2]
    _ = b := List.take_append_drop 8 b

theorem H_lt : ∀ w : List Nat, valid w → H w < 64 ^ w.length := by
  intro w
  refine snoc_ind (P := fun w => valid w → H w < 64 ^ w.length) (by intro _; simp [H]) ?_ w
  · intro w c ih v
    have := ih (fun x hx => v x (by simp [hx]))
    have r := code_range c (v c (by simp))
    rw [H_snoc, List.length_append, List.length_singleton, Int.pow_succ]
    omega
end Hash
