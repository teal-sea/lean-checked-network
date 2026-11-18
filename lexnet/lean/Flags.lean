/- Step 3: the forward keyword/type/constant flags at a word end equal membership of the
   (14-byte truncated) word in the reference name lists. -/
import lean.NetExtra
import lean.Hash
namespace Lexnet
open Hash Units

instance : DecidablePred valid := fun w => by unfold valid; infer_instance

theorem flag_of (tabA : List Int) (P : List (Int × Int)) (names : List (List Nat))
    (hb : ∀ p ∈ names.map wordHash, (p.1 ∈ tabA ∧ p.2 = 0) ∨ p ∈ P)
    (ha : ∀ c ∈ tabA, (c, 0) ∈ names.map wordHash) (hP : ∀ p ∈ P, p ∈ names.map wordHash)
    (hv : ∀ k ∈ names, valid k) (w : List Nat) (vw : valid w) :
    (((wordHash w).1 ∈ tabA ∧ (wordHash w).2 = 0) ∨ wordHash w ∈ P) ↔ w ∈ names := by
  constructor
  · intro h
    have hm : wordHash w ∈ names.map wordHash := by
      rcases h with ⟨h1, h2⟩ | h
      · have := ha _ h1; rw [← h2] at this; simpa using this
      · exact hP _ h
    obtain ⟨k, hk, hkw⟩ := List.mem_map.mp hm
    have := wordHash_inj k w (hv k hk) vw hkw
    rw [← this]; exact hk
  · intro h
    exact hb _ (List.mem_map.mpr ⟨w, h, rfl⟩)

def kwNames := Ref.keywords
def tyNames := Ref.types
def coNames := Ref.constants

theorem kw_tab_b : ∀ p ∈ Ref.keywords.map wordHash, (p.1 ∈ tab0 ∧ p.2 = 0) ∨ p ∈ kwP := by decide +kernel
theorem kw_tab_a : ∀ c ∈ tab0, (c, 0) ∈ Ref.keywords.map wordHash := by decide +kernel
theorem kw_tab_p : ∀ p ∈ kwP, p ∈ Ref.keywords.map wordHash := by decide +kernel
theorem kw_valid : ∀ k ∈ Ref.keywords, valid k := by decide +kernel
theorem ty_tab_b : ∀ p ∈ Ref.types.map wordHash, (p.1 ∈ tab7 ∧ p.2 = 0) ∨ p ∈ tyP := by decide +kernel
theorem ty_tab_a : ∀ c ∈ tab7, (c, 0) ∈ Ref.types.map wordHash := by decide +kernel
theorem ty_tab_p : ∀ p ∈ tyP, p ∈ Ref.types.map wordHash := by decide +kernel
theorem ty_valid : ∀ k ∈ Ref.types, valid k := by decide +kernel
theorem co_tab_b : ∀ p ∈ Ref.constants.map wordHash, (p.1 ∈ tab10 ∧ p.2 = 0) ∨ p ∈ ([] : List (Int × Int)) := by decide +kernel
theorem co_tab_a : ∀ c ∈ tab10, (c, 0) ∈ Ref.constants.map wordHash := by decide +kernel
theorem co_valid : ∀ k ∈ Ref.constants, valid k := by decide +kernel

theorem kw_flag (w : List Nat) (vw : valid w) :
    (flagsOf (wordHash w).1 (wordHash w).2).1 = 1 ↔ w ∈ Ref.keywords := by
  rw [kw_char (wordHash w).1 (wordHash w).2 (show 0 ≤ (wordHash w).2 from H_nonneg _)]
  have := flag_of tab0 kwP _ kw_tab_b kw_tab_a kw_tab_p kw_valid w vw
  rw [← this]

theorem ty_flag (w : List Nat) (vw : valid w) :
    (flagsOf (wordHash w).1 (wordHash w).2).2.1 = 1 ↔ w ∈ Ref.types := by
  rw [ty_char (wordHash w).1 (wordHash w).2 (show 0 ≤ (wordHash w).2 from H_nonneg _)]
  have := flag_of tab7 tyP _ ty_tab_b ty_tab_a ty_tab_p ty_valid w vw
  rw [← this]

theorem co_flag (w : List Nat) (vw : valid w) :
    (flagsOf (wordHash w).1 (wordHash w).2).2.2 = 1 ↔ w ∈ Ref.constants := by
  rw [const_char (wordHash w).1 (wordHash w).2 (show 0 ≤ (wordHash w).2 from H_nonneg _)]
  have := flag_of tab10 [] _ co_tab_b co_tab_a (by simp) co_valid w vw
  rw [← this]; simp

theorem flags_01 (A B : Int) :
    ((flagsOf A B).1 = 0 ∨ (flagsOf A B).1 = 1) ∧ ((flagsOf A B).2.1 = 0 ∨ (flagsOf A B).2.1 = 1) ∧
    ((flagsOf A B).2.2 = 0 ∨ (flagsOf A B).2.2 = 1) := by
  rw [flags_link]; unfold flagsS clip1; simp only []; omega
end Lexnet
