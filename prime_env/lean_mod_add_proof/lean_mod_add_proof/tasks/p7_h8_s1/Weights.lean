import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=8 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.negSucc 112), (.ofNat 116), (.negSucc 111), (.negSucc 121), (.negSucc 93), (.negSucc 84), (.negSucc 103), (.negSucc 104)],
  [(.ofNat 94), (.negSucc 108), (.negSucc 101), (.negSucc 111), (.ofNat 127), (.ofNat 111), (.ofNat 94), (.negSucc 41)],
  [(.ofNat 104), (.ofNat 103), (.negSucc 59), (.ofNat 114), (.negSucc 113), (.negSucc 62), (.ofNat 109), (.ofNat 110)],
  [(.negSucc 97), (.negSucc 83), (.ofNat 85), (.ofNat 74), (.ofNat 110), (.negSucc 111), (.negSucc 84), (.ofNat 110)],
  [(.negSucc 73), (.negSucc 37), (.ofNat 111), (.negSucc 111), (.negSucc 112), (.ofNat 96), (.ofNat 120), (.ofNat 92)],
  [(.ofNat 110), (.negSucc 26), (.ofNat 120), (.ofNat 79), (.ofNat 92), (.ofNat 107), (.negSucc 111), (.negSucc 84)],
  [(.negSucc 49), (.negSucc 119), (.negSucc 91), (.ofNat 108), (.negSucc 52), (.negSucc 106), (.ofNat 111), (.negSucc 117)]]

def E2 : List (List Int) := [
  [(.ofNat 104), (.ofNat 103), (.negSucc 59), (.ofNat 114), (.negSucc 113), (.negSucc 62), (.ofNat 109), (.ofNat 110)],
  [(.negSucc 97), (.negSucc 83), (.ofNat 85), (.ofNat 74), (.ofNat 110), (.negSucc 111), (.negSucc 84), (.ofNat 110)],
  [(.negSucc 73), (.negSucc 37), (.ofNat 111), (.negSucc 111), (.negSucc 112), (.ofNat 96), (.ofNat 120), (.ofNat 92)],
  [(.ofNat 110), (.negSucc 26), (.ofNat 120), (.ofNat 79), (.ofNat 92), (.ofNat 107), (.negSucc 111), (.negSucc 84)],
  [(.negSucc 49), (.negSucc 119), (.negSucc 91), (.ofNat 108), (.negSucc 52), (.negSucc 106), (.ofNat 111), (.negSucc 117)],
  [(.negSucc 112), (.ofNat 116), (.negSucc 111), (.negSucc 121), (.negSucc 93), (.negSucc 84), (.negSucc 103), (.negSucc 104)],
  [(.ofNat 94), (.negSucc 108), (.negSucc 101), (.negSucc 111), (.ofNat 127), (.ofNat 111), (.ofNat 94), (.negSucc 41)]]

def W2 : List (List Int) := [
  [(.negSucc 70), (.ofNat 102), (.ofNat 87), (.ofNat 18), (.negSucc 0), (.ofNat 109), (.negSucc 118), (.negSucc 115)],
  [(.ofNat 110), (.negSucc 75), (.ofNat 26), (.negSucc 109), (.negSucc 14), (.ofNat 33), (.ofNat 121), (.negSucc 101)],
  [(.negSucc 81), (.ofNat 93), (.negSucc 116), (.ofNat 107), (.ofNat 105), (.negSucc 108), (.negSucc 107), (.ofNat 82)],
  [(.negSucc 107), (.negSucc 63), (.negSucc 100), (.ofNat 36), (.negSucc 118), (.ofNat 116), (.ofNat 88), (.ofNat 112)],
  [(.negSucc 0), (.negSucc 112), (.negSucc 86), (.negSucc 112), (.ofNat 114), (.ofNat 99), (.negSucc 20), (.ofNat 110)],
  [(.ofNat 107), (.ofNat 127), (.ofNat 96), (.ofNat 8), (.negSucc 97), (.negSucc 109), (.negSucc 63), (.negSucc 22)],
  [(.negSucc 108), (.negSucc 111), (.ofNat 112), (.ofNat 115), (.ofNat 9), (.negSucc 74), (.ofNat 67), (.negSucc 57)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
