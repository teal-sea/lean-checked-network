import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.negSucc 85), (.negSucc 120), (.negSucc 97), (.ofNat 93), (.ofNat 123), (.negSucc 123), (.ofNat 124), (.ofNat 78), (.negSucc 117), (.ofNat 124), (.negSucc 126), (.ofNat 119), (.ofNat 62), (.negSucc 7), (.ofNat 125), (.negSucc 117)],
  [(.ofNat 122), (.negSucc 80), (.negSucc 10), (.negSucc 124), (.negSucc 109), (.negSucc 118), (.negSucc 126), (.ofNat 121), (.ofNat 121), (.negSucc 83), (.negSucc 46), (.negSucc 118), (.ofNat 125), (.negSucc 90), (.ofNat 102), (.ofNat 124)],
  [(.negSucc 121), (.ofNat 118), (.ofNat 101), (.negSucc 118), (.negSucc 121), (.ofNat 117), (.ofNat 101), (.ofNat 101), (.negSucc 122), (.negSucc 111), (.ofNat 122), (.ofNat 116), (.ofNat 108), (.ofNat 117), (.negSucc 123), (.negSucc 115)],
  [(.ofNat 120), (.negSucc 120), (.negSucc 118), (.ofNat 115), (.negSucc 121), (.ofNat 121), (.ofNat 98), (.negSucc 123), (.ofNat 97), (.ofNat 118), (.ofNat 118), (.ofNat 97), (.negSucc 117), (.negSucc 119), (.negSucc 121), (.ofNat 110)],
  [(.negSucc 103), (.ofNat 122), (.ofNat 126), (.ofNat 123), (.ofNat 122), (.ofNat 106), (.negSucc 109), (.negSucc 122), (.ofNat 68), (.negSucc 121), (.negSucc 113), (.negSucc 122), (.negSucc 125), (.ofNat 123), (.ofNat 93), (.ofNat 88)]]

def E2 : List (List Int) := [
  [(.negSucc 89), (.negSucc 92), (.ofNat 120), (.ofNat 101), (.negSucc 116), (.negSucc 120), (.negSucc 101), (.ofNat 121), (.ofNat 116), (.ofNat 112), (.negSucc 123), (.negSucc 118), (.negSucc 120), (.negSucc 114), (.ofNat 116), (.negSucc 106)],
  [(.negSucc 100), (.ofNat 116), (.negSucc 111), (.negSucc 116), (.negSucc 119), (.ofNat 100), (.ofNat 127), (.ofNat 104), (.negSucc 110), (.negSucc 5), (.ofNat 114), (.ofNat 53), (.negSucc 118), (.ofNat 114), (.ofNat 121), (.ofNat 114)],
  [(.ofNat 122), (.negSucc 121), (.ofNat 109), (.negSucc 121), (.ofNat 116), (.ofNat 121), (.negSucc 118), (.negSucc 118), (.ofNat 64), (.negSucc 115), (.ofNat 123), (.ofNat 95), (.negSucc 32), (.negSucc 61), (.ofNat 27), (.negSucc 116)],
  [(.negSucc 119), (.ofNat 119), (.negSucc 41), (.ofNat 92), (.ofNat 121), (.ofNat 76), (.ofNat 104), (.negSucc 120), (.ofNat 101), (.ofNat 123), (.negSucc 54), (.negSucc 118), (.ofNat 126), (.negSucc 84), (.negSucc 120), (.ofNat 123)],
  [(.ofNat 113), (.negSucc 105), (.negSucc 112), (.ofNat 122), (.negSucc 3), (.negSucc 115), (.ofNat 26), (.ofNat 99), (.negSucc 123), (.negSucc 118), (.negSucc 119), (.ofNat 120), (.ofNat 104), (.ofNat 119), (.negSucc 117), (.negSucc 34)]]

def W2 : List (List Int) := [
  [(.ofNat 124), (.ofNat 127), (.negSucc 117), (.negSucc 116), (.negSucc 123), (.ofNat 126), (.negSucc 121), (.ofNat 105), (.negSucc 120), (.ofNat 26), (.ofNat 123), (.negSucc 117), (.ofNat 119), (.negSucc 27), (.ofNat 120), (.negSucc 54)],
  [(.negSucc 125), (.negSucc 124), (.ofNat 100), (.negSucc 124), (.negSucc 66), (.ofNat 97), (.ofNat 122), (.ofNat 125), (.ofNat 118), (.ofNat 124), (.negSucc 124), (.ofNat 67), (.negSucc 123), (.ofNat 99), (.ofNat 126), (.negSucc 118)],
  [(.ofNat 92), (.ofNat 112), (.ofNat 86), (.ofNat 117), (.ofNat 126), (.negSucc 123), (.negSucc 121), (.ofNat 117), (.negSucc 118), (.negSucc 124), (.negSucc 122), (.ofNat 117), (.negSucc 123), (.negSucc 118), (.ofNat 24), (.ofNat 120)],
  [(.ofNat 101), (.ofNat 34), (.negSucc 119), (.ofNat 124), (.ofNat 115), (.negSucc 120), (.ofNat 116), (.negSucc 121), (.ofNat 99), (.ofNat 124), (.ofNat 108), (.negSucc 124), (.negSucc 95), (.ofNat 123), (.negSucc 123), (.negSucc 120)],
  [(.negSucc 114), (.negSucc 118), (.ofNat 120), (.ofNat 108), (.negSucc 121), (.ofNat 114), (.ofNat 19), (.negSucc 123), (.ofNat 121), (.negSucc 116), (.ofNat 124), (.ofNat 125), (.ofNat 127), (.negSucc 118), (.negSucc 121), (.ofNat 122)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
