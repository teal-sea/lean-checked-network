import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=8 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.ofNat 89), (.negSucc 125), (.negSucc 57), (.ofNat 69), (.negSucc 78), (.negSucc 72), (.negSucc 99), (.ofNat 121)],
  [(.ofNat 66), (.ofNat 95), (.negSucc 96), (.negSucc 62), (.negSucc 50), (.ofNat 108), (.ofNat 91), (.negSucc 114)],
  [(.negSucc 96), (.negSucc 50), (.ofNat 107), (.negSucc 107), (.ofNat 96), (.negSucc 66), (.ofNat 94), (.ofNat 111)],
  [(.ofNat 95), (.negSucc 32), (.ofNat 101), (.negSucc 92), (.negSucc 112), (.negSucc 100), (.negSucc 115), (.negSucc 91)],
  [(.ofNat 112), (.ofNat 82), (.negSucc 95), (.ofNat 29), (.ofNat 113), (.ofNat 108), (.negSucc 89), (.ofNat 91)],
  [(.negSucc 96), (.negSucc 98), (.negSucc 29), (.ofNat 94), (.negSucc 107), (.ofNat 78), (.ofNat 114), (.ofNat 16)],
  [(.negSucc 103), (.ofNat 127), (.ofNat 70), (.ofNat 106), (.ofNat 72), (.negSucc 120), (.ofNat 12), (.negSucc 72)]]

def E2 : List (List Int) := [
  [(.ofNat 71), (.ofNat 112), (.ofNat 101), (.negSucc 88), (.negSucc 63), (.ofNat 116), (.negSucc 107), (.negSucc 105)],
  [(.negSucc 103), (.negSucc 36), (.negSucc 115), (.negSucc 118), (.ofNat 92), (.negSucc 53), (.negSucc 90), (.ofNat 102)],
  [(.ofNat 88), (.negSucc 61), (.negSucc 94), (.negSucc 103), (.negSucc 108), (.negSucc 101), (.ofNat 108), (.negSucc 102)],
  [(.ofNat 120), (.ofNat 123), (.ofNat 85), (.ofNat 1), (.ofNat 99), (.ofNat 124), (.ofNat 36), (.ofNat 115)],
  [(.negSucc 92), (.negSucc 117), (.negSucc 29), (.ofNat 92), (.negSucc 102), (.ofNat 89), (.negSucc 111), (.ofNat 57)],
  [(.negSucc 100), (.ofNat 97), (.negSucc 91), (.ofNat 116), (.ofNat 38), (.negSucc 126), (.ofNat 28), (.negSucc 77)],
  [(.ofNat 102), (.negSucc 112), (.ofNat 114), (.ofNat 90), (.negSucc 76), (.negSucc 86), (.ofNat 105), (.ofNat 109)]]

def W2 : List (List Int) := [
  [(.ofNat 89), (.negSucc 45), (.negSucc 116), (.negSucc 108), (.ofNat 104), (.negSucc 4), (.ofNat 110), (.negSucc 18)],
  [(.negSucc 108), (.negSucc 10), (.negSucc 69), (.negSucc 71), (.negSucc 94), (.ofNat 127), (.ofNat 77), (.ofNat 121)],
  [(.negSucc 25), (.ofNat 85), (.ofNat 125), (.ofNat 64), (.ofNat 85), (.negSucc 46), (.negSucc 115), (.negSucc 103)],
  [(.ofNat 113), (.negSucc 113), (.negSucc 65), (.ofNat 107), (.negSucc 69), (.negSucc 91), (.ofNat 44), (.ofNat 100)],
  [(.negSucc 8), (.ofNat 114), (.negSucc 92), (.ofNat 68), (.negSucc 99), (.ofNat 25), (.ofNat 123), (.negSucc 85)],
  [(.negSucc 99), (.negSucc 101), (.ofNat 47), (.ofNat 61), (.ofNat 118), (.ofNat 91), (.negSucc 55), (.ofNat 21)],
  [(.ofNat 111), (.ofNat 100), (.ofNat 88), (.negSucc 35), (.negSucc 95), (.negSucc 110), (.negSucc 84), (.ofNat 45)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
