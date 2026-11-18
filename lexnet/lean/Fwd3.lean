/- Step 2d: one forward step of the full exact cell, related to one step of the reference's
   left-to-right pass.  Gives the invariant `Rel` and the exact output vector. -/
import lean.Fwd1
import lean.Fwd3a
import lean.Flags
import lean.Bwd
namespace Lexnet
open Hash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem emb_ok : ∀ b : Byte,
    (embedding b).flags.getD 2 0 = enc (Ref.isWordChar b.val) ∧ (embedding b).code = code b.val ∧
    (embedding b).flags.getD 9 0 = enc (b.val == 47) ∧
    (embedding b).flags.getD 4 0 = enc (Ref.isBlank b.val) ∧
    (embedding b).flags.getD 5 0 = enc (b.val == 10) ∧
    (embedding b).flags.getD 12 0 = enc (b.val == 40) := by decide +kernel

def Rel (h : FState) (s : Ref.Left) : Prop :=
  h.auto = autoOf s ∧ autoOf s ∈ reach ∧ h.W = enc s.wasWord ∧ h.N = enc s.wasNumber ∧
  NumInv s.wasWord s.word h.d h.h1 h.h2

def Agree (P : Pat) (c : Ref.Seen) : Prop :=
  c.comment = (P.c0 || P.c1) ∧ c.string = P.s ∧ c.char = P.q ∧ c.pp = P.p ∧ c.word = P.w ∧
  c.number = P.n ∧ c.opener = P.o ∧ c.slash = P.sl ∧ c.blank = P.bl ∧ c.newline = P.nl ∧
  c.paren = P.lp ∧
  (c.word = true → c.isKeyword = P.k ∧ c.isType = P.t ∧ c.isConstant = P.v)

theorem label_congr (P : Pat) (c : Ref.Seen) (R : Ref.Right) (h : Agree P c) :
    Ref.label (seenOf P) R = Ref.label c R := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  rcases c with ⟨cm, st, ch, pp, wd, nu, ik, it, ic, op, sl, bl, nl, pa⟩
  simp only [] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  cases hw : wd
  · simp [Ref.label, seenOf, hw, ← h5, ← h1, ← h2, ← h3, ← h4, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11]
  · obtain ⟨k1, k2, k3⟩ := h12 hw
    simp [Ref.label, seenOf, hw, ← h5, ← h1, ← h2, ← h3, ← h4, ← h6, ← h7, ← h8, ← h9, ← h10, ← h11,
      k1, k2, k3]

theorem step_excl (s : Ref.Left) (c : Nat) :
    ((Ref.step s c).2.word && (Ref.step s c).2.number) = false := by
  have key : ∀ a b x y : Bool, ((a && !b) && ((x && y) && !(a || b))) = false := by decide
  exact key _ _ _ _

theorem step_wc (s : Ref.Left) (c : Nat) : (Ref.step s c).1.wasWord = true → Ref.isWordChar c = true := by
  intro h
  have hl : Ref.isLetter c = true → Ref.isWordChar c = true := fun h => by simp [Ref.isWordChar, h]
  simp only [Ref.step] at h
  cases hw : Ref.isWordChar c
  · cases hl' : Ref.isLetter c
    · simp [hw, hl'] at h
    · exact absurd (hl hl') (by simp [hw])
  · rfl

theorem bool_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem enc_of_01 (v : Int) (h : v = 0 ∨ v = 1) : v = enc (v == 1) := by
  rcases h with h | h <;> subst h <;> rfl

theorem fwd_out (x : Features) (h : FState) : (forward x h).2 =
    [(autoStep x.flags h.auto).getD 0 0, (autoStep x.flags h.auto).getD 1 0,
     (autoStep x.flags h.auto).getD 2 0, (autoStep x.flags h.auto).getD 3 0,
     (autoStep x.flags h.auto).getD 4 0,
     (wnStep x.flags h.auto h.W h.N).1, (wnStep x.flags h.auto h.W h.N).2,
     (flagsOf (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.1
              (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.2).1,
     (flagsOf (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.1
              (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.2).2.1,
     (flagsOf (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.1
              (hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2).2.2).2.2,
     openStep x.flags h.auto, x.flags.getD 9 0, x.flags.getD 4 0, x.flags.getD 5 0,
     x.flags.getD 12 0] := by rfl

theorem fin_ofNat (b : Byte) : Fin.ofNat 256 b.val = b := by
  apply Fin.ext; simp [Fin.ofNat, Nat.mod_eq_of_lt b.isLt]

theorem enc_ne (b : Bool) : (enc b != 0) = b := by cases b <;> rfl

theorem eta (s : Ref.Left) : mkL (autoOf s) s.wasWord s.wasNumber = { s with word := [] } := by
  cases s
  simp only [mkL, autoOf, bit, List.getD_cons_zero, List.getD_cons_succ, enc_ne]

theorem step_word_def (s : Ref.Left) (c : Nat) :
    (Ref.step s c).1.word = nextWord s.wasWord (Ref.step s c).1.wasWord s.word c := rfl

theorem fwd_step (h : FState) (s : Ref.Left) (b : Byte) (hr : Rel h s) :
    Rel (forward (embedding b) h).1 (Ref.step s b.val).1 ∧
    ∃ P : Pat, (forward (embedding b) h).2 = fvec P ∧ (P.w && P.n) = false ∧
      Agree P (Ref.step s b.val).2 := by
  obtain ⟨hauto, hreach, hW, hN, hnum⟩ := hr
  obtain ⟨Ew, Ec, E9, E4, E5, E12⟩ := emb_ok b
  have core := core_mem (autoOf s) hreach s.wasWord s.wasNumber b.val b.isLt
  simp only [coreCheck, fin_ofNat, eta, Bool.and_eq_true, beq_iff_eq] at core
  obtain ⟨⟨cA, cWN⟩, cO⟩ := core
  have cA' : autoStep (embedding b).flags (autoOf s) = autoOf (Ref.step s b.val).1 := cA
  have cWN' : wnStep (embedding b).flags (autoOf s) (enc s.wasWord) (enc s.wasNumber) =
      (enc (Ref.step s b.val).1.wasWord, enc (Ref.step s b.val).1.wasNumber) := cWN
  have cO' : openStep (embedding b).flags (autoOf s) = enc (Ref.step s b.val).2.opener := cO
  have hpro := projection (embedding b) h
  have hwn := wn_link (embedding b) h
  have hhash := hash_link (embedding b) h
  rw [hauto] at hpro hwn
  rw [hW, hN, cWN'] at hwn
  simp only [Prod.mk.injEq] at hwn hhash
  have hnum' := num_step s.wasWord (Ref.step s b.val).1.wasWord s.word b.val h.d h.h1 h.h2 hnum
    (step_wc s b.val)
  rw [← step_word_def] at hnum'
  rw [Ew, Ec, hW] at hhash
  have hd' := congrArg (fun p => p.1) hhash
  have hh1' := congrArg (fun p => p.2.1) hhash
  have hh2' := congrArg (fun p => p.2.2) hhash
  simp only [] at hd' hh1' hh2'
  rw [← hd', ← hh1', ← hh2'] at hnum'
  have sf := (step_facts (autoOf s) hreach b).1
  rw [cA'] at sf
  have hrel : Rel (forward (embedding b) h).1 (Ref.step s b.val).1 :=
    ⟨by rw [hpro, cA'], sf, hwn.1, hwn.2, hnum'⟩
  refine ⟨hrel, ?_⟩
  obtain ⟨hv', hl', hdd, hb1, hb2, hin', hout'⟩ := hnum'
  refine ⟨⟨(Ref.step s b.val).1.block, (Ref.step s b.val).1.line, (Ref.step s b.val).2.string,
    (Ref.step s b.val).2.char, (Ref.step s b.val).2.pp, (Ref.step s b.val).2.word,
    (Ref.step s b.val).2.number,
    ((flagsOf (forward (embedding b) h).1.h1 (forward (embedding b) h).1.h2).1 == 1),
    ((flagsOf (forward (embedding b) h).1.h1 (forward (embedding b) h).1.h2).2.1 == 1),
    ((flagsOf (forward (embedding b) h).1.h1 (forward (embedding b) h).1.h2).2.2 == 1),
    (Ref.step s b.val).2.opener, (Ref.step s b.val).2.slash, (Ref.step s b.val).2.blank,
    (Ref.step s b.val).2.newline, (Ref.step s b.val).2.paren⟩, ?_, ?_, ?_⟩
  · rw [fwd_out, hauto, hW, hN, cWN', cA', cO', Ew, Ec, E9, E4, E5, E12, ← hh1', ← hh2']
    have f01 := flags_01 (forward (embedding b) h).1.h1 (forward (embedding b) h).1.h2
    simp only [fvec, List.cons.injEq]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, enc_of_01 _ f01.1, enc_of_01 _ f01.2.1,
      enc_of_01 _ f01.2.2, trivial, rfl, rfl, rfl, rfl, trivial⟩
  · exact step_excl s b.val
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro hw
    have hw' : (Ref.step s b.val).1.wasWord = true := hw
    obtain ⟨_, e1, e2, _⟩ := hin' hw'
    rw [e1, e2]
    have hk := kw_flag _ hv'
    have ht := ty_flag _ hv'
    have hc := co_flag _ hv'
    refine ⟨?_, ?_, ?_⟩
    · apply bool_of_iff
      simp only [beq_iff_eq]
      have e : (Ref.step s b.val).2.isKeyword = true ↔ (Ref.step s b.val).1.word ∈ Ref.keywords := by
        show Ref.keywords.contains _ = true ↔ _; exact List.contains_iff_mem
      rw [e]; exact hk.symm
    · apply bool_of_iff
      simp only [beq_iff_eq]
      have e : (Ref.step s b.val).2.isType = true ↔ (Ref.step s b.val).1.word ∈ Ref.types := by
        show Ref.types.contains _ = true ↔ _; exact List.contains_iff_mem
      rw [e]; exact ht.symm
    · apply bool_of_iff
      simp only [beq_iff_eq]
      have e : (Ref.step s b.val).2.isConstant = true ↔ (Ref.step s b.val).1.word ∈ Ref.constants := by
        show Ref.constants.contains _ = true ↔ _; exact List.contains_iff_mem
      rw [e]; exact hc.symm
end Lexnet
