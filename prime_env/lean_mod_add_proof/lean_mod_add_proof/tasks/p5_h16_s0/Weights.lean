import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.ofNat 55), (.negSucc 116), (.negSucc 109), (.ofNat 122), (.negSucc 126), (.ofNat 115), (.ofNat 126), (.negSucc 85), (.ofNat 116), (.negSucc 121), (.negSucc 119), (.ofNat 122), (.negSucc 123), (.negSucc 124), (.negSucc 125), (.ofNat 103)],
  [(.negSucc 117), (.negSucc 105), (.negSucc 126), (.negSucc 123), (.ofNat 121), (.negSucc 105), (.negSucc 124), (.negSucc 59), (.ofNat 126), (.ofNat 97), (.ofNat 122), (.negSucc 122), (.negSucc 122), (.negSucc 97), (.ofNat 118), (.negSucc 125)],
  [(.ofNat 122), (.ofNat 120), (.negSucc 116), (.ofNat 126), (.ofNat 126), (.negSucc 104), (.ofNat 117), (.ofNat 121), (.ofNat 121), (.ofNat 102), (.negSucc 113), (.ofNat 64), (.ofNat 99), (.ofNat 124), (.ofNat 127), (.ofNat 126)],
  [(.negSucc 118), (.negSucc 125), (.ofNat 126), (.negSucc 114), (.ofNat 116), (.ofNat 123), (.ofNat 118), (.negSucc 120), (.negSucc 125), (.negSucc 116), (.ofNat 35), (.ofNat 76), (.ofNat 125), (.ofNat 125), (.ofNat 113), (.negSucc 121)],
  [(.ofNat 117), (.ofNat 121), (.ofNat 125), (.negSucc 95), (.negSucc 123), (.negSucc 124), (.negSucc 124), (.ofNat 123), (.negSucc 123), (.ofNat 125), (.ofNat 118), (.negSucc 120), (.ofNat 120), (.negSucc 120), (.negSucc 123), (.ofNat 105)]]

def E2 : List (List Int) := [
  [(.negSucc 120), (.negSucc 117), (.negSucc 125), (.negSucc 105), (.ofNat 127), (.ofNat 119), (.negSucc 125), (.negSucc 121), (.negSucc 115), (.ofNat 43), (.negSucc 113), (.ofNat 81), (.negSucc 123), (.negSucc 123), (.negSucc 111), (.negSucc 118)],
  [(.ofNat 124), (.ofNat 121), (.negSucc 123), (.negSucc 99), (.ofNat 124), (.negSucc 116), (.ofNat 126), (.ofNat 124), (.ofNat 123), (.ofNat 119), (.ofNat 124), (.negSucc 121), (.negSucc 121), (.ofNat 122), (.ofNat 124), (.ofNat 95)],
  [(.negSucc 113), (.negSucc 124), (.ofNat 115), (.ofNat 123), (.negSucc 116), (.negSucc 36), (.negSucc 114), (.negSucc 88), (.ofNat 127), (.negSucc 120), (.negSucc 118), (.ofNat 122), (.ofNat 123), (.ofNat 125), (.ofNat 127), (.ofNat 120)],
  [(.ofNat 95), (.ofNat 121), (.ofNat 127), (.negSucc 123), (.negSucc 126), (.ofNat 122), (.negSucc 115), (.negSucc 26), (.negSucc 117), (.ofNat 124), (.ofNat 94), (.negSucc 120), (.ofNat 125), (.ofNat 95), (.negSucc 116), (.negSucc 126)],
  [(.ofNat 101), (.negSucc 107), (.ofNat 119), (.ofNat 126), (.negSucc 120), (.negSucc 125), (.ofNat 125), (.ofNat 120), (.negSucc 126), (.negSucc 118), (.ofNat 107), (.ofNat 53), (.negSucc 92), (.negSucc 123), (.negSucc 126), (.ofNat 124)]]

def W2 : List (List Int) := [
  [(.ofNat 100), (.ofNat 122), (.negSucc 124), (.negSucc 123), (.negSucc 126), (.ofNat 106), (.negSucc 124), (.ofNat 117), (.negSucc 126), (.ofNat 108), (.ofNat 111), (.ofNat 103), (.ofNat 102), (.ofNat 100), (.negSucc 123), (.negSucc 123)],
  [(.ofNat 92), (.negSucc 123), (.ofNat 126), (.ofNat 122), (.negSucc 117), (.ofNat 101), (.ofNat 125), (.ofNat 84), (.negSucc 117), (.negSucc 122), (.negSucc 121), (.negSucc 117), (.ofNat 126), (.negSucc 110), (.negSucc 125), (.ofNat 125)],
  [(.negSucc 120), (.ofNat 120), (.ofNat 125), (.ofNat 31), (.ofNat 126), (.negSucc 120), (.negSucc 119), (.negSucc 112), (.ofNat 126), (.ofNat 124), (.ofNat 122), (.ofNat 123), (.negSucc 110), (.negSucc 125), (.negSucc 102), (.negSucc 123)],
  [(.ofNat 123), (.ofNat 118), (.negSucc 102), (.negSucc 122), (.ofNat 126), (.ofNat 125), (.negSucc 121), (.ofNat 122), (.ofNat 126), (.negSucc 118), (.negSucc 116), (.negSucc 122), (.negSucc 125), (.negSucc 112), (.ofNat 125), (.ofNat 30)],
  [(.negSucc 118), (.negSucc 122), (.negSucc 125), (.ofNat 125), (.negSucc 116), (.negSucc 122), (.ofNat 125), (.negSucc 124), (.negSucc 113), (.ofNat 86), (.ofNat 86), (.ofNat 104), (.negSucc 111), (.ofNat 127), (.ofNat 126), (.ofNat 122)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
