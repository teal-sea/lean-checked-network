import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.ofNat 121), (.ofNat 80), (.negSucc 122), (.ofNat 123), (.negSucc 44), (.ofNat 82), (.ofNat 123), (.ofNat 127), (.ofNat 100), (.negSucc 80), (.negSucc 112), (.ofNat 104), (.negSucc 118), (.ofNat 127), (.negSucc 121), (.negSucc 124)],
  [(.negSucc 121), (.negSucc 123), (.ofNat 124), (.negSucc 113), (.ofNat 119), (.ofNat 109), (.negSucc 118), (.ofNat 108), (.ofNat 117), (.ofNat 119), (.negSucc 78), (.negSucc 123), (.ofNat 119), (.ofNat 63), (.negSucc 117), (.negSucc 108)],
  [(.ofNat 120), (.negSucc 114), (.negSucc 96), (.negSucc 67), (.ofNat 115), (.negSucc 125), (.ofNat 122), (.negSucc 121), (.ofNat 109), (.ofNat 107), (.ofNat 125), (.ofNat 125), (.ofNat 123), (.negSucc 121), (.ofNat 108), (.ofNat 111)],
  [(.negSucc 113), (.ofNat 84), (.negSucc 109), (.ofNat 124), (.negSucc 87), (.ofNat 123), (.ofNat 72), (.negSucc 121), (.negSucc 119), (.negSucc 121), (.negSucc 124), (.negSucc 122), (.ofNat 99), (.negSucc 121), (.ofNat 123), (.ofNat 121)],
  [(.negSucc 42), (.ofNat 120), (.ofNat 124), (.negSucc 121), (.negSucc 125), (.negSucc 120), (.negSucc 122), (.ofNat 83), (.negSucc 123), (.negSucc 122), (.ofNat 116), (.ofNat 84), (.negSucc 124), (.ofNat 100), (.ofNat 76), (.ofNat 88)]]

def E2 : List (List Int) := [
  [(.ofNat 118), (.negSucc 117), (.ofNat 125), (.negSucc 115), (.negSucc 99), (.ofNat 122), (.ofNat 123), (.ofNat 111), (.negSucc 116), (.negSucc 116), (.negSucc 100), (.negSucc 122), (.ofNat 126), (.negSucc 109), (.ofNat 122), (.negSucc 119)],
  [(.negSucc 123), (.ofNat 90), (.negSucc 126), (.negSucc 72), (.ofNat 118), (.negSucc 126), (.negSucc 87), (.ofNat 127), (.negSucc 125), (.negSucc 124), (.ofNat 124), (.ofNat 95), (.ofNat 107), (.ofNat 116), (.ofNat 117), (.ofNat 71)],
  [(.ofNat 122), (.ofNat 116), (.ofNat 124), (.ofNat 123), (.ofNat 115), (.ofNat 117), (.negSucc 101), (.ofNat 60), (.ofNat 102), (.negSucc 84), (.negSucc 125), (.ofNat 100), (.negSucc 122), (.ofNat 126), (.negSucc 121), (.ofNat 121)],
  [(.negSucc 112), (.ofNat 116), (.negSucc 99), (.negSucc 122), (.negSucc 106), (.ofNat 110), (.ofNat 123), (.negSucc 121), (.ofNat 120), (.ofNat 118), (.ofNat 120), (.negSucc 125), (.negSucc 123), (.negSucc 109), (.negSucc 120), (.ofNat 89)],
  [(.ofNat 70), (.negSucc 121), (.negSucc 104), (.ofNat 126), (.negSucc 123), (.negSucc 120), (.negSucc 123), (.negSucc 123), (.ofNat 100), (.ofNat 114), (.negSucc 96), (.ofNat 126), (.ofNat 47), (.negSucc 125), (.ofNat 73), (.negSucc 118)]]

def W2 : List (List Int) := [
  [(.negSucc 74), (.ofNat 75), (.negSucc 125), (.ofNat 47), (.negSucc 124), (.ofNat 96), (.ofNat 119), (.ofNat 108), (.ofNat 98), (.ofNat 122), (.ofNat 123), (.negSucc 126), (.negSucc 124), (.negSucc 97), (.negSucc 119), (.ofNat 120)],
  [(.negSucc 89), (.ofNat 125), (.ofNat 125), (.negSucc 117), (.negSucc 109), (.ofNat 113), (.negSucc 112), (.ofNat 126), (.negSucc 119), (.negSucc 31), (.negSucc 123), (.ofNat 126), (.ofNat 90), (.ofNat 124), (.negSucc 121), (.ofNat 88)],
  [(.ofNat 118), (.ofNat 95), (.negSucc 118), (.ofNat 123), (.ofNat 119), (.negSucc 124), (.negSucc 104), (.ofNat 79), (.negSucc 118), (.negSucc 122), (.ofNat 113), (.negSucc 116), (.ofNat 125), (.ofNat 119), (.ofNat 104), (.negSucc 119)],
  [(.negSucc 122), (.negSucc 121), (.ofNat 94), (.negSucc 124), (.ofNat 119), (.ofNat 126), (.ofNat 125), (.negSucc 119), (.ofNat 32), (.negSucc 113), (.ofNat 117), (.ofNat 88), (.ofNat 112), (.negSucc 108), (.ofNat 125), (.negSucc 117)],
  [(.ofNat 121), (.negSucc 114), (.ofNat 115), (.ofNat 121), (.ofNat 89), (.negSucc 120), (.negSucc 123), (.negSucc 124), (.ofNat 123), (.ofNat 108), (.negSucc 120), (.ofNat 107), (.negSucc 117), (.negSucc 123), (.ofNat 98), (.ofNat 116)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
