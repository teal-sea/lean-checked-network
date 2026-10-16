import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=8 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.negSucc 110), (.negSucc 126), (.negSucc 98), (.negSucc 42), (.negSucc 100), (.ofNat 60), (.ofNat 103), (.ofNat 70)],
  [(.negSucc 77), (.negSucc 93), (.ofNat 91), (.negSucc 73), (.ofNat 106), (.negSucc 111), (.negSucc 89), (.ofNat 104)],
  [(.ofNat 80), (.ofNat 99), (.negSucc 5), (.ofNat 77), (.ofNat 103), (.negSucc 103), (.ofNat 103), (.negSucc 100)],
  [(.ofNat 97), (.ofNat 100), (.negSucc 79), (.negSucc 101), (.negSucc 86), (.ofNat 76), (.negSucc 69), (.ofNat 102)],
  [(.negSucc 28), (.ofNat 104), (.ofNat 98), (.ofNat 103), (.negSucc 100), (.ofNat 116), (.negSucc 110), (.negSucc 105)]]

def E2 : List (List Int) := [
  [(.ofNat 111), (.ofNat 90), (.ofNat 99), (.negSucc 111), (.negSucc 107), (.negSucc 124), (.negSucc 101), (.negSucc 120)],
  [(.ofNat 109), (.negSucc 112), (.negSucc 105), (.ofNat 110), (.negSucc 109), (.ofNat 42), (.negSucc 41), (.ofNat 95)],
  [(.negSucc 90), (.negSucc 103), (.ofNat 106), (.negSucc 110), (.ofNat 27), (.ofNat 109), (.ofNat 115), (.ofNat 69)],
  [(.negSucc 122), (.ofNat 87), (.negSucc 118), (.ofNat 120), (.ofNat 106), (.ofNat 78), (.negSucc 109), (.negSucc 105)],
  [(.ofNat 32), (.ofNat 116), (.negSucc 46), (.ofNat 110), (.ofNat 127), (.negSucc 110), (.ofNat 111), (.ofNat 112)]]

def W2 : List (List Int) := [
  [(.negSucc 119), (.negSucc 121), (.negSucc 101), (.ofNat 110), (.ofNat 117), (.ofNat 7), (.negSucc 117), (.ofNat 116)],
  [(.negSucc 109), (.ofNat 117), (.ofNat 110), (.negSucc 102), (.ofNat 15), (.ofNat 127), (.negSucc 30), (.negSucc 110)],
  [(.ofNat 72), (.ofNat 121), (.negSucc 109), (.negSucc 116), (.negSucc 124), (.ofNat 47), (.negSucc 13), (.ofNat 118)],
  [(.ofNat 114), (.ofNat 81), (.ofNat 110), (.ofNat 125), (.negSucc 100), (.negSucc 121), (.negSucc 112), (.negSucc 121)],
  [(.ofNat 9), (.negSucc 114), (.ofNat 77), (.negSucc 120), (.ofNat 54), (.negSucc 117), (.ofNat 116), (.ofNat 97)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
