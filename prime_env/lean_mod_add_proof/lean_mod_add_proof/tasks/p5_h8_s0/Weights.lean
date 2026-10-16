import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=8 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.negSucc 106), (.ofNat 101), (.negSucc 97), (.ofNat 105), (.ofNat 117), (.ofNat 97), (.negSucc 111), (.ofNat 125)],
  [(.ofNat 81), (.negSucc 66), (.negSucc 112), (.negSucc 96), (.negSucc 100), (.negSucc 102), (.negSucc 109), (.negSucc 96)],
  [(.ofNat 96), (.negSucc 29), (.ofNat 81), (.ofNat 108), (.negSucc 97), (.ofNat 102), (.ofNat 99), (.negSucc 109)],
  [(.negSucc 100), (.ofNat 113), (.ofNat 109), (.negSucc 123), (.ofNat 88), (.negSucc 105), (.ofNat 104), (.ofNat 92)],
  [(.ofNat 105), (.negSucc 107), (.ofNat 19), (.negSucc 126), (.ofNat 106), (.ofNat 107), (.ofNat 24), (.ofNat 105)]]

def E2 : List (List Int) := [
  [(.negSucc 101), (.negSucc 106), (.negSucc 126), (.ofNat 101), (.ofNat 92), (.ofNat 48), (.negSucc 104), (.negSucc 98)],
  [(.negSucc 101), (.ofNat 110), (.ofNat 75), (.negSucc 107), (.negSucc 89), (.ofNat 105), (.negSucc 110), (.negSucc 104)],
  [(.ofNat 102), (.negSucc 107), (.ofNat 108), (.ofNat 90), (.negSucc 102), (.negSucc 105), (.negSucc 18), (.ofNat 65)],
  [(.negSucc 103), (.negSucc 92), (.ofNat 85), (.negSucc 22), (.negSucc 81), (.ofNat 99), (.ofNat 99), (.ofNat 104)],
  [(.ofNat 108), (.ofNat 99), (.negSucc 93), (.negSucc 58), (.ofNat 107), (.negSucc 87), (.ofNat 121), (.ofNat 89)]]

def W2 : List (List Int) := [
  [(.negSucc 79), (.negSucc 101), (.ofNat 116), (.ofNat 105), (.negSucc 56), (.ofNat 102), (.ofNat 59), (.negSucc 114)],
  [(.ofNat 93), (.ofNat 68), (.ofNat 39), (.negSucc 114), (.negSucc 108), (.negSucc 99), (.ofNat 110), (.ofNat 53)],
  [(.negSucc 106), (.ofNat 56), (.negSucc 98), (.ofNat 101), (.negSucc 88), (.negSucc 21), (.ofNat 75), (.ofNat 105)],
  [(.ofNat 116), (.negSucc 108), (.negSucc 120), (.negSucc 77), (.ofNat 98), (.ofNat 77), (.negSucc 80), (.ofNat 99)],
  [(.negSucc 92), (.ofNat 106), (.ofNat 82), (.ofNat 110), (.ofNat 110), (.negSucc 101), (.negSucc 126), (.negSucc 81)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
