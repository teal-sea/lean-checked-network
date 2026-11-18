/- Optional float64-range certificate, part 3.  On every state satisfying the proven invariant `Rel`,
   every product and every ordered partial sum of the forward cell (in the evaluation order of the
   generated expressions) has absolute value at most 2^53, the largest range in which float64 holds
   every integer exactly; the same holds for the backward cell and the head, on all Boolean inputs.
   This is a statement about integer magnitudes only.  It does not model IEEE-754 rounding and says
   nothing about the compiled C code. -/
import lean.FloatBridge
import lean.FloatBox
namespace Lexnet
open Cell Hash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem within_nil : Within [] [] := by
  intro i; simp [List.getD_eq_getElem?_getD]

theorem within_cons (a : Int) (ia : Iv) (t : List Int) (it : List Iv) (ha : ia.1 ≤ a ∧ a ≤ ia.2)
    (ht : Within t it) : Within (a :: t) (ia :: it) := by
  intro i
  cases i with
  | zero => simpa using ha
  | succ i => simpa using ht i

theorem bits_within (l : List Int) (hl : ∀ i, i < 13 → 0 ≤ l.getD i 0 ∧ l.getD i 0 ≤ 1) :
    Within ((List.range 13).map fun i => l.getD i 0) bits13 :=
  within_map (List.range 13) (fun i => l.getD i 0) (fun _ => ((0 : Int), (1 : Int)))
    (fun i hi => hl i (List.mem_range.mp hi))

theorem input_within (x : Features) (h : FState) (t5 : List Iv)
    (hx : ∀ i, i < 13 → 0 ≤ x.flags.getD i 0 ∧ x.flags.getD i 0 ≤ 1)
    (hc : 0 ≤ x.code ∧ x.code ≤ 63)
    (ha : ∀ i, i < 13 → 0 ≤ h.auto.getD i 0 ∧ h.auto.getD i 0 ≤ 1)
    (ht : Within [h.W, h.N, h.d, h.h1, h.h2] t5) :
    Within (inputVec x h) (boxCommon ++ t5) := by
  unfold inputVec boxCommon
  apply within_append
  · simp [bits13]
  · apply within_append
    · simp [bits13]
    · apply within_append
      · simp [bits13]
      · exact bits_within _ hx
      · exact within_cons _ ((0 : Int), (63 : Int)) [] [] hc within_nil
    · exact bits_within _ ha
  · exact ht

theorem emb_bits : ∀ b : Byte, ∀ i, i < 13 → 0 ≤ (embedding b).flags.getD i 0 ∧ (embedding b).flags.getD i 0 ≤ 1 := by
  decide +kernel

theorem autoOf_bits (s : Ref.Left) : ∀ i, i < 13 → 0 ≤ (autoOf s).getD i 0 ∧ (autoOf s).getD i 0 ≤ 1 := by
  intro i hi
  have : ∀ b : Bool, 0 ≤ enc b ∧ enc b ≤ 1 := by intro b; cases b <;> simp [enc]
  have h0 : ∀ j, j < 13 → (autoOf s).getD j 0 = (autoOf s)[j]! := by intros; simp [List.getD_eq_getElem?_getD]
  unfold autoOf
  match i, hi with
  | 0, _ => exact this _ | 1, _ => exact this _ | 2, _ => exact this _ | 3, _ => exact this _
  | 4, _ => exact this _ | 5, _ => exact this _ | 6, _ => exact this _ | 7, _ => exact this _
  | 8, _ => exact this _ | 9, _ => exact this _ | 10, _ => exact this _ | 11, _ => exact this _
  | 12, _ => exact this _

theorem forward_range (b : Byte) (h : FState) (s : Ref.Left) (hr : Rel h s) :
    ∀ t ∈ traceCell fwdCell (inputVec (embedding b) h), -(2 ^ 53 : Int) ≤ t ∧ t ≤ 2 ^ 53 := by
  obtain ⟨hauto, hreach, hW, hN, hnum⟩ := hr
  obtain ⟨hv, hl, hd, hh1, hh2, hin, hout⟩ := hnum
  have hc : 0 ≤ (embedding b).code ∧ (embedding b).code ≤ 63 := by
    obtain ⟨_, Ec, _⟩ := emb_ok b; rw [Ec]; exact code_bd _
  have ha : ∀ i, i < 13 → 0 ≤ h.auto.getD i 0 ∧ h.auto.getD i 0 ≤ 1 := by
    rw [hauto]; exact autoOf_bits s
  have hN01 : 0 ≤ h.N ∧ h.N ≤ 1 := by rw [hN]; cases s.wasNumber <;> simp [enc]
  have cert := cert_fwd
  simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq,
    forall_eq_or_imp, forall_eq] at cert
  obtain ⟨cA, cB, cC⟩ := cert
  by_cases hww : s.wasWord = true
  · have hW1 : h.W = 1 := by rw [hW, hww]; rfl
    obtain ⟨l1, e1, e2, hdl⟩ := hin hww
    by_cases hd8 : 8 ≤ h.d
    · -- box A
      have hlt : h.h1 < 2 ^ 42 := by
        rcases hdl with ⟨l2, e3⟩ | ⟨l2, e3⟩
        · have hl7 : s.word.length ≤ 7 := by omega
          have tk : s.word.take 8 = s.word := List.take_of_length_le (by omega)
          rw [e1, tk]
          have := H_lt_len s.word hv 7 hl7
          have e : (64 : Int) ^ 7 = 2 ^ 42 := by decide
          omega
        · omega
      have hw := input_within (embedding b) h [(1, 1), (0, 1), (8, 14), (0, 2 ^ 42 - 1), (0, 2 ^ 36 - 1)]
        (emb_bits b) hc ha
        (within_cons _ _ _ _ (by simp [hW1]) (within_cons _ _ _ _ (by simpa using hN01)
          (within_cons _ _ _ _ (by simp; omega) (within_cons _ _ _ _ (by simp; omega)
            (within_cons _ _ _ _ (by simp; omega) within_nil)))))
      intro t ht
      have := (cell_sound fwdCell _ _ hw).2 t ht
      have hb : (cellIv fwdCell boxA).2 ≤ 2 ^ 53 := cA
      unfold boxA at hb
      omega
    · have hw := input_within (embedding b) h [(1, 1), (0, 1), (0, 7), (0, 2 ^ 48 - 1), (0, 2 ^ 36 - 1)]
        (emb_bits b) hc ha
        (within_cons _ _ _ _ (by simp [hW1]) (within_cons _ _ _ _ (by simpa using hN01)
          (within_cons _ _ _ _ (by simp; omega) (within_cons _ _ _ _ (by simp; omega)
            (within_cons _ _ _ _ (by simp; omega) within_nil)))))
      intro t ht
      have := (cell_sound fwdCell _ _ hw).2 t ht
      have hb : (cellIv fwdCell boxB).2 ≤ 2 ^ 53 := cB
      unfold boxB at hb
      omega
  · have hW0 : h.W = 0 := by rw [hW]; cases hq : s.wasWord <;> simp_all [enc]
    have hw := input_within (embedding b) h [(0, 0), (0, 1), (0, 14), (0, 2 ^ 48 - 1), (0, 2 ^ 36 - 1)]
      (emb_bits b) hc ha
      (within_cons _ _ _ _ (by simp [hW0]) (within_cons _ _ _ _ (by simpa using hN01)
        (within_cons _ _ _ _ (by simp; omega) (within_cons _ _ _ _ (by simp; omega)
          (within_cons _ _ _ _ (by simp; omega) within_nil)))))
    intro t ht
    have := (cell_sound fwdCell _ _ hw).2 t ht
    have hb : (cellIv fwdCell boxC).2 ≤ 2 ^ 53 := cC
    unfold boxC at hb
    omega

theorem enc_bits (b : Bool) : 0 ≤ enc b ∧ enc b ≤ 1 := by cases b <;> simp [enc]

theorem fvec_bits (P : Pat) : ∀ i, i < 15 → 0 ≤ (fvec P).getD i 0 ∧ (fvec P).getD i 0 ≤ 1 := by
  intro i hi
  unfold fvec
  match i, hi with
  | 0, _ => exact enc_bits _ | 1, _ => exact enc_bits _ | 2, _ => exact enc_bits _
  | 3, _ => exact enc_bits _ | 4, _ => exact enc_bits _ | 5, _ => exact enc_bits _
  | 6, _ => exact enc_bits _ | 7, _ => exact enc_bits _ | 8, _ => exact enc_bits _
  | 9, _ => exact enc_bits _ | 10, _ => exact enc_bits _ | 11, _ => exact enc_bits _
  | 12, _ => exact enc_bits _ | 13, _ => exact enc_bits _ | 14, _ => exact enc_bits _

theorem encR_bits (R : Ref.Right) : ∀ i, i < 7 → 0 ≤ (encR R).getD i 0 ∧ (encR R).getD i 0 ≤ 1 := by
  intro i hi
  unfold encR
  match i, hi with
  | 0, _ => exact enc_bits _ | 1, _ => exact enc_bits _ | 2, _ => exact enc_bits _
  | 3, _ => exact enc_bits _ | 4, _ => exact enc_bits _ | 5, _ => exact enc_bits _
  | 6, _ => exact enc_bits _

/-- Backward cell and head, on every Boolean forward-output pattern and backward state. -/
theorem backward_range (P : Pat) (R : Ref.Right) :
    ∀ t ∈ traceCell (bwdCell ++ [⟨headRows, []⟩]) (bwdIn (fvec P) (encR R)),
      -(2 ^ 53 : Int) ≤ t ∧ t ≤ 2 ^ 53 := by
  have hw : Within (bwdIn (fvec P) (encR R)) boxBwd := by
    unfold bwdIn boxBwd
    apply within_append
    · simp
    · exact within_map (List.range 15) (fun i => (fvec P).getD i 0) (fun _ => ((0 : Int), (1 : Int)))
        (fun i hi => fvec_bits P i (List.mem_range.mp hi))
    · exact within_map (List.range 7) (fun i => (encR R).getD i 0) (fun _ => ((0 : Int), (1 : Int)))
        (fun i hi => encR_bits R i (List.mem_range.mp hi))
  intro t ht
  have := (cell_sound _ _ _ hw).2 t ht
  have hb : bwdMax ≤ 2 ^ 53 := by simpa using cert_bwd
  unfold bwdMax at hb
  omega
end Lexnet
