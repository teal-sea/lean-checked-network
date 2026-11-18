import lean.Fwd1a
import lean.Fwd1b
import lean.Fwd1c
import lean.Fwd1d
namespace Lexnet
theorem core_all : ∀ i, i < 33 → coreOne i = true := by
  intro i hi
  match i, hi with
  | 0, _ => exact core_0
  | 1, _ => exact core_1
  | 2, _ => exact core_2
  | 3, _ => exact core_3
  | 4, _ => exact core_4
  | 5, _ => exact core_5
  | 6, _ => exact core_6
  | 7, _ => exact core_7
  | 8, _ => exact core_8
  | 9, _ => exact core_9
  | 10, _ => exact core_10
  | 11, _ => exact core_11
  | 12, _ => exact core_12
  | 13, _ => exact core_13
  | 14, _ => exact core_14
  | 15, _ => exact core_15
  | 16, _ => exact core_16
  | 17, _ => exact core_17
  | 18, _ => exact core_18
  | 19, _ => exact core_19
  | 20, _ => exact core_20
  | 21, _ => exact core_21
  | 22, _ => exact core_22
  | 23, _ => exact core_23
  | 24, _ => exact core_24
  | 25, _ => exact core_25
  | 26, _ => exact core_26
  | 27, _ => exact core_27
  | 28, _ => exact core_28
  | 29, _ => exact core_29
  | 30, _ => exact core_30
  | 31, _ => exact core_31
  | 32, _ => exact core_32
  | (n + 33), h => exact absurd h (by omega)
theorem reach_len : reach.length = 33 := by decide +kernel
theorem core_mem (a : AState) (ha : a ∈ reach) (ww wn : Bool) (c : Nat) (hc : c < 256) :
    coreCheck a ww wn c = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < 33 := by rw [reach_len] at hi; exact hi
  have h := core_all i hi'
  simp only [coreOne, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 ww (by cases ww <;> simp) wn (by cases wn <;> simp) c hc
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this
end Lexnet
