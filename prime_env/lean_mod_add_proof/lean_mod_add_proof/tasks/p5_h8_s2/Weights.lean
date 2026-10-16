import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=8 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.ofNat 115), (.ofNat 70), (.negSucc 113), (.negSucc 86), (.negSucc 113), (.ofNat 115), (.negSucc 109), (.negSucc 21)],
  [(.negSucc 106), (.ofNat 65), (.negSucc 83), (.negSucc 116), (.ofNat 102), (.negSucc 110), (.negSucc 59), (.ofNat 100)],
  [(.negSucc 125), (.negSucc 100), (.ofNat 105), (.negSucc 95), (.negSucc 90), (.ofNat 108), (.ofNat 115), (.negSucc 118)],
  [(.ofNat 70), (.ofNat 118), (.ofNat 127), (.ofNat 112), (.negSucc 82), (.ofNat 109), (.ofNat 105), (.ofNat 115)],
  [(.ofNat 117), (.negSucc 116), (.negSucc 97), (.ofNat 119), (.ofNat 120), (.negSucc 105), (.negSucc 123), (.negSucc 102)]]

def E2 : List (List Int) := [
  [(.negSucc 93), (.ofNat 110), (.ofNat 96), (.ofNat 109), (.ofNat 75), (.ofNat 105), (.ofNat 103), (.ofNat 93)],
  [(.ofNat 114), (.negSucc 94), (.negSucc 100), (.ofNat 100), (.ofNat 81), (.negSucc 102), (.ofNat 100), (.ofNat 84)],
  [(.ofNat 99), (.ofNat 89), (.negSucc 100), (.negSucc 71), (.negSucc 94), (.ofNat 105), (.negSucc 85), (.negSucc 108)],
  [(.negSucc 54), (.ofNat 94), (.negSucc 72), (.negSucc 100), (.ofNat 98), (.ofNat 4), (.negSucc 89), (.ofNat 108)],
  [(.negSucc 99), (.negSucc 104), (.ofNat 104), (.negSucc 97), (.negSucc 106), (.negSucc 75), (.negSucc 126), (.negSucc 71)]]

def W2 : List (List Int) := [
  [(.ofNat 91), (.ofNat 102), (.negSucc 126), (.ofNat 86), (.negSucc 99), (.ofNat 102), (.negSucc 103), (.negSucc 103)],
  [(.ofNat 105), (.ofNat 104), (.ofNat 73), (.negSucc 119), (.negSucc 96), (.negSucc 99), (.negSucc 93), (.ofNat 101)],
  [(.negSucc 56), (.negSucc 108), (.ofNat 107), (.negSucc 92), (.ofNat 94), (.ofNat 82), (.ofNat 67), (.negSucc 96)],
  [(.negSucc 103), (.ofNat 100), (.ofNat 72), (.ofNat 34), (.negSucc 92), (.negSucc 65), (.ofNat 104), (.negSucc 75)],
  [(.negSucc 103), (.negSucc 92), (.negSucc 86), (.ofNat 109), (.ofNat 98), (.negSucc 96), (.ofNat 51), (.ofNat 104)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
