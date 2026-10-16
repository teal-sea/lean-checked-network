import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=8 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.ofNat 59), (.negSucc 61), (.negSucc 97), (.ofNat 54), (.negSucc 112), (.negSucc 126), (.negSucc 100), (.negSucc 97)],
  [(.ofNat 76), (.negSucc 101), (.negSucc 105), (.ofNat 107), (.ofNat 104), (.ofNat 97), (.ofNat 98), (.negSucc 87)],
  [(.negSucc 81), (.negSucc 94), (.negSucc 23), (.negSucc 55), (.negSucc 86), (.ofNat 101), (.negSucc 117), (.ofNat 94)],
  [(.ofNat 106), (.negSucc 51), (.ofNat 94), (.negSucc 97), (.negSucc 99), (.negSucc 93), (.ofNat 96), (.negSucc 59)],
  [(.negSucc 111), (.ofNat 53), (.ofNat 88), (.ofNat 94), (.ofNat 66), (.negSucc 71), (.negSucc 85), (.negSucc 119)],
  [(.ofNat 120), (.ofNat 99), (.ofNat 87), (.ofNat 87), (.negSucc 101), (.ofNat 105), (.negSucc 23), (.ofNat 90)],
  [(.negSucc 95), (.ofNat 104), (.negSucc 82), (.negSucc 100), (.ofNat 105), (.negSucc 64), (.ofNat 56), (.ofNat 113)]]

def E2 : List (List Int) := [
  [(.negSucc 111), (.ofNat 53), (.ofNat 88), (.ofNat 94), (.ofNat 66), (.negSucc 71), (.negSucc 85), (.negSucc 119)],
  [(.ofNat 120), (.ofNat 99), (.ofNat 87), (.ofNat 87), (.negSucc 101), (.ofNat 105), (.negSucc 23), (.ofNat 90)],
  [(.negSucc 95), (.ofNat 104), (.negSucc 82), (.negSucc 100), (.ofNat 105), (.negSucc 64), (.ofNat 56), (.ofNat 113)],
  [(.ofNat 59), (.negSucc 61), (.negSucc 97), (.ofNat 54), (.negSucc 112), (.negSucc 126), (.negSucc 100), (.negSucc 97)],
  [(.ofNat 76), (.negSucc 101), (.negSucc 105), (.ofNat 107), (.ofNat 104), (.ofNat 97), (.ofNat 98), (.negSucc 87)],
  [(.negSucc 81), (.negSucc 94), (.negSucc 23), (.negSucc 55), (.negSucc 86), (.ofNat 101), (.negSucc 117), (.ofNat 94)],
  [(.ofNat 106), (.negSucc 51), (.ofNat 94), (.negSucc 97), (.negSucc 99), (.negSucc 93), (.ofNat 96), (.negSucc 59)]]

def W2 : List (List Int) := [
  [(.negSucc 43), (.ofNat 95), (.negSucc 101), (.negSucc 73), (.negSucc 111), (.ofNat 15), (.ofNat 87), (.ofNat 109)],
  [(.negSucc 11), (.ofNat 58), (.negSucc 117), (.ofNat 103), (.ofNat 119), (.negSucc 112), (.negSucc 82), (.ofNat 14)],
  [(.ofNat 98), (.negSucc 93), (.ofNat 103), (.negSucc 35), (.negSucc 122), (.ofNat 104), (.ofNat 70), (.negSucc 126)],
  [(.negSucc 105), (.negSucc 112), (.ofNat 94), (.negSucc 105), (.ofNat 100), (.ofNat 19), (.negSucc 45), (.ofNat 100)],
  [(.ofNat 126), (.negSucc 111), (.ofNat 109), (.negSucc 4), (.negSucc 37), (.negSucc 105), (.negSucc 93), (.ofNat 60)],
  [(.negSucc 123), (.ofNat 72), (.ofNat 8), (.ofNat 120), (.negSucc 38), (.negSucc 23), (.ofNat 111), (.negSucc 90)],
  [(.ofNat 46), (.ofNat 118), (.negSucc 70), (.negSucc 100), (.ofNat 45), (.ofNat 119), (.negSucc 113), (.negSucc 73)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
