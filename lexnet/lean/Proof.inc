
-- Hand-written Boolean specification, independent of affine weight rows.
def bit (s : List Int) (i : Nat) : Bool := s.getD i 0 != 0
def enc (b : Bool) : Int := if b then 1 else 0
def referenceFlags (b : Byte) : List Int :=
  let c := b.val
  let letter : Bool := decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ c = 95)
  let digit : Bool := decide (48 ≤ c ∧ c ≤ 57)
  let word := letter || digit
  let space : Bool := decide (c = 32 ∨ c = 9 ∨ c = 13 ∨ c = 11 ∨ c = 12)
  [enc letter, enc digit, enc word, enc (word || c == 46), enc space,
   enc (c == 10), enc (c == 34), enc (c == 39), enc (c == 92),
   enc (c == 47), enc (c == 42), enc (c == 35), enc (c == 40)]
theorem features_exact : ∀ b : Byte, (embedding b).flags = referenceFlags b := by
  decide +kernel

def specInitial : AState := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
theorem initial_agrees : initialAuto = specInitial := by decide +kernel

def specStep (x : List Int) (h : AState) : AState :=
  let nl := bit x 5
  let inBlock := bit h 0 && !bit h 8
  let inLine := bit h 1 && !nl
  let inString := bit h 2 && !bit h 9 && !nl
  let inChar := bit h 3 && !bit h 10 && !nl
  let inPP := bit h 4 && (!nl || bit h 12)
  let openBlock := bit h 6 && bit x 10
  let openLine := bit h 6 && bit x 9
  [enc (inBlock || openBlock),
   enc (inLine || openLine),
   enc (inString || (bit x 6 && !(inBlock || inLine || inChar))),
   enc (inChar || (bit x 7 && !(inBlock || inLine || inString))),
   enc (inPP || (bit x 11 && bit h 11 && !(inBlock || inLine || inString || inChar))),
   enc ((inString || inChar) && bit x 8 && !bit h 5),
   enc (bit x 9 && !(inBlock || inLine || inString || inChar || openLine)),
   enc (inBlock && bit x 10),
   enc (bit h 7 && bit x 9),
   enc (inString && bit x 6 && !bit h 5),
   enc (inChar && bit x 7 && !bit h 5),
   enc (nl || (bit h 11 && bit x 4)),
   enc (inPP && bit x 8)]

def transOk : Bool :=
  decide (initialAuto ∈ reach) &&
  reach.all fun h => inputs.all fun x =>
    decide (autoStep x h ∈ reach) && (autoStep x h == specStep x h)

theorem input_covered : ∀ b : Byte, (embedding b).flags ∈ inputs := by decide +kernel
theorem trans_ok : transOk = true := by decide +kernel

theorem step_facts (h : AState) (hr : h ∈ reach) (b : Byte) :
    autoStep (embedding b).flags h ∈ reach ∧
    autoStep (embedding b).flags h = specStep (embedding b).flags h := by
  have ht := trans_ok
  simp only [transOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true] at ht
  exact ht.2 h hr (embedding b).flags (input_covered b)

-- Complete exact bidirectional semantics. The head's integer logits are doubled.
-- Strict improvement implements the C head's earliest-class tie breaking.
def argmax : List Int → Nat
  | [] => 0
  | z :: zs =>
    (zs.zipIdx.foldl (fun (best : Nat × Int) (p : Int × Nat) =>
      if best.2 < p.1 then (p.2 + 1, p.1) else best) (0, z)).1

def forwardFeatures : FState → List Byte → List (List Int)
  | _, [] => []
  | h, b :: bs =>
      let (next, f) := forward (embedding b) h
      f :: forwardFeatures next bs

def suffixPass : List (List Int) → List Int × List Nat
  | [] => ([0, 0, 0, 0, 0, 0, 0], [])
  | f :: fs =>
      let (right, rest) := suffixPass fs
      let (next, logits) := backward f right
      (next, argmax logits :: rest)

def exactClasses (bs : List Byte) : List Nat :=
  (suffixPass (forwardFeatures initial bs)).2

def fullTrace : FState → List Byte → List AState
  | _, [] => []
  | h, b :: bs =>
      let next := (forward (embedding b) h).1
      next.auto :: fullTrace next bs

def specTrace : AState → List Byte → List AState
  | _, [] => []
  | h, b :: bs =>
      let next := specStep (referenceFlags b) h
      next :: specTrace next bs

theorem trace_from_reach (bs : List Byte) (h : FState) (hr : h.auto ∈ reach) :
    fullTrace h bs = specTrace h.auto bs := by
  induction bs generalizing h with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨hc, he⟩ := step_facts h.auto hr b
    have hn : (forward (embedding b) h).1.auto ∈ reach := by
      rw [projection]; exact hc
    simp only [fullTrace, specTrace]
    rw [ih _ hn, projection, he, features_exact]

/-- Every byte list, of every length: the full exact cell's automaton agrees
    with the Boolean lexer, including all thirteen flags at every position. -/
theorem automaton_correct (bs : List Byte) :
    fullTrace initial bs = specTrace specInitial bs := by
  rw [← initial_agrees]
  apply trace_from_reach
  have ht := trans_ok
  simp only [transOk, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ht.1

#print axioms projection
#print axioms trans_ok
#print axioms features_exact
#print axioms automaton_correct
end Lexnet
