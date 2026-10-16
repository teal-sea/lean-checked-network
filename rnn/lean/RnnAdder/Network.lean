/-!
# A recurrent network with a binary state, and the proof scheme for all input lengths

The network reads one pair of bits `(a, b)` per step, least significant bit first, keeps a
hidden state of `H` bits, and emits one sum bit per step. After the last step a carry bit is
read off the state. Every weight is an integer and every activation is a threshold at zero,
so one step is pure integer arithmetic:

    step h (a, b)  = [ Wh h + Wxa a + Wxb b + bh > 0 ]     (entry by entry)
    out  h (a, b)  = [ Wo (step h (a, b)) + Woa a + Wob b + bo > 0 ]
    carry h        = [ Wc h + bc > 0 ]

The specification is the ripple-carry adder `addBits`. The proof for every input length is:
a finite check `transOk` (every state reachable from `h0` under the four input pairs stays in
the explicit list `reach`, and the carry read off each state behaves like the ripple carry)
followed by induction on the input list. Nothing here depends on the particular weights.
-/

namespace RnnAdder

/-- The hidden state: one `Bool` per unit. -/
abbrev State := List Bool

/-- One input: the bit of the first number and the bit of the second number at this position. -/
abbrev Input := Bool × Bool

/-- Sum of the weights at the positions where the state is `true`. -/
def dotB : List Int → State → Int
  | w :: ws, h :: hs => Int.add (if h then w else 0) (dotB ws hs)
  | _, _ => 0

/-- The threshold activation. -/
def thr (z : Int) : Bool := decide (0 < z)

/-- One unit of the recurrent layer. -/
def unit (wh : List Int) (wa wb b : Int) (h : State) (x : Input) : Bool :=
  thr (Int.add (Int.add (Int.add (dotB wh h) (if x.1 then wa else 0)) (if x.2 then wb else 0)) b)

/-- The recurrent layer: one unit per row of `Wh`. -/
def layer : List (List Int) → List Int → List Int → List Int → State → Input → State
  | wh :: whs, wa :: was, wb :: wbs, b :: bs, h, x => unit wh wa wb b h x :: layer whs was wbs bs h x
  | _, _, _, _, _, _ => []

/-- The integer weights of a network, its initial state and the list of states it claims to reach. -/
structure Net where
  Wh : List (List Int)   -- recurrent weights, one row per unit
  Wxa : List Int         -- input weights for the bit `a`, one per unit
  Wxb : List Int         -- input weights for the bit `b`, one per unit
  bh : List Int          -- recurrent biases
  Wo : List Int          -- sum-bit read-out weights (applied to the new state)
  Woa : Int              -- sum-bit weight for the bit `a`
  Wob : Int              -- sum-bit weight for the bit `b`
  bo : Int               -- sum-bit bias
  Wc : List Int          -- carry read-out weights
  bc : Int               -- carry read-out bias
  h0 : State             -- initial state
  reach : List State     -- the states claimed reachable from `h0`

variable (N : Net)

/-- One step of the state. -/
def step (h : State) (x : Input) : State := layer N.Wh N.Wxa N.Wxb N.bh h x

/-- The sum bit emitted at a step. -/
def out (h : State) (x : Input) : Bool :=
  thr (Int.add (Int.add (Int.add (dotB N.Wo (step N h x)) (if x.1 then N.Woa else 0))
    (if x.2 then N.Wob else 0)) N.bo)

/-- The carry read off a state. -/
def carry (h : State) : Bool := thr (Int.add (dotB N.Wc h) N.bc)

/-- The sum bits the network emits on an input list, starting from state `h`. -/
def run : State → List Input → List Bool
  | _, [] => []
  | h, x :: xs => out N h x :: run (step N h x) xs

/-- The state after reading an input list. -/
def runState : State → List Input → State
  | h, [] => h
  | h, x :: xs => runState (step N h x) xs

/-- The carry the network reports after reading an input list. -/
def finalCarry (h : State) (xs : List Input) : Bool := carry N (runState N h xs)

/-! ## The specification: a ripple-carry adder -/

/-- The carry out of a full adder. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The sum bits of the ripple-carry adder with carry-in `c`. -/
def addBits : Bool → List Input → List Bool
  | _, [] => []
  | c, (a, b) :: xs => (a ^^ b ^^ c) :: addBits (maj a b c) xs

/-- The final carry of the ripple-carry adder with carry-in `c`. -/
def carryOut : Bool → List Input → Bool
  | c, [] => c
  | c, (a, b) :: xs => carryOut (maj a b c) xs

/-! ## The finite check -/

/-- The four possible inputs. -/
def inputs : List Input := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_inputs (x : Input) : x ∈ inputs := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> decide

/-- The certificate, as one `Bool`: the initial state is in `reach` and reads carry `false`;
every state in `reach` steps, under every input, to a state in `reach`; the carry read off the
new state is the full-adder carry; and the emitted bit is the full-adder sum. -/
def transOk : Bool :=
  decide (N.h0 ∈ N.reach) && (carry N N.h0 == false) &&
  N.reach.all fun h => inputs.all fun x =>
    decide (step N h x ∈ N.reach) &&
    (carry N (step N h x) == maj x.1 x.2 (carry N h)) &&
    (out N h x == (x.1 ^^ x.2 ^^ carry N h))

theorem transOk_facts (ht : transOk N = true) :
    N.h0 ∈ N.reach ∧ carry N N.h0 = false ∧
    ∀ h ∈ N.reach, ∀ x : Input, step N h x ∈ N.reach ∧
      carry N (step N h x) = maj x.1 x.2 (carry N h) ∧ out N h x = (x.1 ^^ x.2 ^^ carry N h) := by
  simp only [transOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ht
  obtain ⟨⟨h0r, h0c⟩, hall⟩ := ht
  refine ⟨h0r, h0c, fun h hr x => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hall h hr x (mem_inputs x)
  exact ⟨h1, h2, h3⟩

/-! ## From the finite check to every input length -/

/-- Induction on the input list, with the invariant "the state is in `reach`". -/
theorem run_eq_addBits_of_reach (ht : transOk N = true) :
    ∀ (xs : List Input) (h : State), h ∈ N.reach →
      run N h xs = addBits (carry N h) xs ∧ finalCarry N h xs = carryOut (carry N h) xs
  | [], _, _ => ⟨rfl, rfl⟩
  | (a, b) :: xs, h, hr => by
    obtain ⟨_, _, hstep⟩ := transOk_facts N ht
    obtain ⟨hr', hc', ho'⟩ := hstep h hr (a, b)
    obtain ⟨ih1, ih2⟩ := run_eq_addBits_of_reach ht xs (step N h (a, b)) hr'
    simp only [run, finalCarry, runState, addBits, carryOut] at ih1 ih2 ⊢
    rw [ho', ih1, hc']
    exact ⟨rfl, by rw [← hc']; exact ih2⟩

/-- The network's sum bits equal the ripple-carry adder's, for every input list. -/
theorem run_eq_addBits (ht : transOk N = true) (xs : List Input) :
    run N N.h0 xs = addBits false xs := by
  obtain ⟨h0r, h0c, _⟩ := transOk_facts N ht
  have := (run_eq_addBits_of_reach N ht xs N.h0 h0r).1
  rwa [h0c] at this

/-- The network's final carry equals the ripple-carry adder's, for every input list. -/
theorem finalCarry_eq_carryOut (ht : transOk N = true) (xs : List Input) :
    finalCarry N N.h0 xs = carryOut false xs := by
  obtain ⟨h0r, h0c, _⟩ := transOk_facts N ht
  have := (run_eq_addBits_of_reach N ht xs N.h0 h0r).2
  rwa [h0c] at this

/-! ## The arithmetic reading -/

/-- The number whose bits are the list, least significant first. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- The ripple-carry adder adds: its sum bits plus its carry at position `n` equal the two
inputs plus the carry-in. -/
theorem addBits_adds (c : Bool) (xs : List Input) :
    bitsToNat (addBits c xs) + 2 ^ xs.length * (if carryOut c xs then 1 else 0)
      = bitsToNat (xs.map Prod.fst) + bitsToNat (xs.map Prod.snd) + (if c then 1 else 0) := by
  induction xs generalizing c with
  | nil => cases c <;> simp [addBits, carryOut, bitsToNat]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    have := ih (maj a b c)
    simp only [addBits, carryOut, bitsToNat, List.map_cons, List.length_cons, Nat.pow_succ] at this ⊢
    -- `omega` treats `2 ^ n * carry` as one unknown; put the factor 2 outside it
    rw [Nat.mul_right_comm]
    cases a <;> cases b <;> cases c <;> simp [maj] at this ⊢ <;> omega

/-- The network adds, for every input length: the number its sum bits spell, plus its final
carry at position `n`, is the sum of the two input numbers. -/
theorem network_adds (ht : transOk N = true) (xs : List Input) :
    bitsToNat (run N N.h0 xs) + 2 ^ xs.length * (if finalCarry N N.h0 xs then 1 else 0)
      = bitsToNat (xs.map Prod.fst) + bitsToNat (xs.map Prod.snd) := by
  rw [run_eq_addBits N ht, finalCarry_eq_carryOut N ht]
  have := addBits_adds false xs
  simpa using this

end RnnAdder
