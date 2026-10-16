import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=8 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.negSucc 106), (.ofNat 50), (.negSucc 103), (.ofNat 96), (.negSucc 93), (.ofNat 87), (.ofNat 97), (.ofNat 101)],
  [(.negSucc 78), (.negSucc 95), (.ofNat 93), (.ofNat 15), (.ofNat 91), (.negSucc 95), (.negSucc 95), (.negSucc 97)],
  [(.negSucc 0), (.ofNat 51), (.negSucc 89), (.negSucc 111), (.ofNat 78), (.ofNat 100), (.ofNat 97), (.ofNat 103)],
  [(.ofNat 68), (.ofNat 113), (.ofNat 33), (.ofNat 82), (.negSucc 99), (.negSucc 100), (.negSucc 104), (.negSucc 66)],
  [(.ofNat 99), (.negSucc 101), (.ofNat 16), (.ofNat 127), (.ofNat 105), (.ofNat 96), (.ofNat 88), (.negSucc 95)],
  [(.ofNat 120), (.negSucc 108), (.negSucc 68), (.negSucc 74), (.negSucc 34), (.negSucc 100), (.negSucc 74), (.ofNat 96)],
  [(.ofNat 105), (.ofNat 103), (.ofNat 92), (.negSucc 107), (.negSucc 82), (.ofNat 111), (.ofNat 24), (.negSucc 91)],
  [(.ofNat 43), (.ofNat 85), (.negSucc 107), (.ofNat 93), (.ofNat 107), (.negSucc 112), (.ofNat 34), (.negSucc 87)],
  [(.negSucc 18), (.negSucc 104), (.ofNat 112), (.ofNat 107), (.negSucc 101), (.ofNat 84), (.negSucc 64), (.ofNat 93)],
  [(.negSucc 67), (.negSucc 84), (.negSucc 118), (.negSucc 101), (.negSucc 10), (.negSucc 49), (.ofNat 81), (.negSucc 92)],
  [(.negSucc 107), (.ofNat 102), (.ofNat 103), (.negSucc 77), (.ofNat 86), (.negSucc 58), (.negSucc 105), (.ofNat 93)]]

def E2 : List (List Int) := [
  [(.ofNat 104), (.negSucc 100), (.ofNat 16), (.ofNat 127), (.negSucc 106), (.ofNat 94), (.negSucc 85), (.ofNat 89)],
  [(.ofNat 123), (.negSucc 112), (.negSucc 64), (.negSucc 73), (.ofNat 68), (.negSucc 100), (.ofNat 73), (.negSucc 93)],
  [(.ofNat 107), (.ofNat 104), (.ofNat 92), (.negSucc 116), (.ofNat 89), (.ofNat 111), (.negSucc 25), (.ofNat 88)],
  [(.ofNat 34), (.ofNat 95), (.negSucc 107), (.ofNat 91), (.negSucc 99), (.negSucc 114), (.negSucc 46), (.ofNat 12)],
  [(.negSucc 15), (.negSucc 105), (.ofNat 112), (.ofNat 108), (.ofNat 110), (.ofNat 86), (.ofNat 67), (.negSucc 90)],
  [(.negSucc 73), (.negSucc 100), (.negSucc 116), (.negSucc 100), (.negSucc 19), (.negSucc 49), (.negSucc 94), (.ofNat 97)],
  [(.negSucc 107), (.ofNat 102), (.ofNat 105), (.negSucc 86), (.negSucc 86), (.negSucc 52), (.ofNat 107), (.negSucc 84)],
  [(.negSucc 103), (.ofNat 39), (.negSucc 106), (.ofNat 97), (.ofNat 97), (.ofNat 85), (.negSucc 99), (.negSucc 86)],
  [(.negSucc 73), (.negSucc 92), (.ofNat 97), (.ofNat 16), (.negSucc 107), (.negSucc 95), (.ofNat 98), (.ofNat 99)],
  [(.ofNat 0), (.ofNat 41), (.negSucc 100), (.negSucc 107), (.negSucc 83), (.ofNat 101), (.negSucc 101), (.negSucc 95)],
  [(.ofNat 69), (.ofNat 110), (.ofNat 37), (.ofNat 83), (.ofNat 105), (.negSucc 98), (.ofNat 110), (.ofNat 62)]]

def W2 : List (List Int) := [
  [(.negSucc 112), (.negSucc 107), (.negSucc 40), (.ofNat 123), (.ofNat 110), (.ofNat 69), (.negSucc 104), (.negSucc 107)],
  [(.negSucc 94), (.ofNat 59), (.ofNat 111), (.negSucc 51), (.ofNat 28), (.negSucc 40), (.ofNat 95), (.negSucc 41)],
  [(.negSucc 67), (.ofNat 111), (.negSucc 102), (.negSucc 97), (.negSucc 86), (.ofNat 115), (.negSucc 31), (.ofNat 116)],
  [(.ofNat 47), (.negSucc 64), (.ofNat 111), (.ofNat 57), (.ofNat 91), (.negSucc 115), (.ofNat 15), (.negSucc 110)],
  [(.ofNat 49), (.negSucc 125), (.negSucc 114), (.ofNat 83), (.negSucc 94), (.ofNat 118), (.ofNat 38), (.ofNat 51)],
  [(.ofNat 84), (.ofNat 69), (.ofNat 104), (.negSucc 97), (.negSucc 20), (.negSucc 122), (.negSucc 75), (.ofNat 72)],
  [(.ofNat 73), (.ofNat 36), (.negSucc 114), (.negSucc 80), (.ofNat 74), (.ofNat 94), (.ofNat 43), (.negSucc 97)],
  [(.ofNat 99), (.negSucc 110), (.ofNat 58), (.ofNat 91), (.negSucc 112), (.negSucc 69), (.negSucc 92), (.ofNat 96)],
  [(.ofNat 37), (.negSucc 42), (.ofNat 6), (.ofNat 24), (.ofNat 8), (.ofNat 61), (.ofNat 100), (.negSucc 10)],
  [(.negSucc 20), (.ofNat 127), (.ofNat 30), (.negSucc 120), (.ofNat 107), (.ofNat 20), (.negSucc 122), (.negSucc 93)],
  [(.negSucc 90), (.negSucc 18), (.ofNat 42), (.ofNat 7), (.negSucc 108), (.ofNat 46), (.ofNat 83), (.ofNat 107)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
