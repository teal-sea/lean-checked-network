import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=8 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.ofNat 121), (.negSucc 99), (.ofNat 102), (.ofNat 90), (.negSucc 65), (.ofNat 125), (.ofNat 54), (.negSucc 102)],
  [(.negSucc 108), (.ofNat 8), (.negSucc 106), (.negSucc 109), (.negSucc 55), (.negSucc 115), (.ofNat 19), (.ofNat 104)],
  [(.ofNat 118), (.ofNat 98), (.ofNat 96), (.ofNat 123), (.ofNat 118), (.negSucc 15), (.negSucc 61), (.negSucc 97)],
  [(.negSucc 55), (.ofNat 91), (.negSucc 100), (.negSucc 9), (.negSucc 110), (.ofNat 110), (.ofNat 99), (.ofNat 114)],
  [(.negSucc 14), (.negSucc 52), (.ofNat 104), (.negSucc 88), (.ofNat 43), (.negSucc 124), (.negSucc 112), (.negSucc 114)],
  [(.ofNat 75), (.negSucc 112), (.negSucc 96), (.ofNat 123), (.ofNat 101), (.ofNat 45), (.ofNat 114), (.ofNat 103)],
  [(.negSucc 100), (.negSucc 79), (.ofNat 107), (.negSucc 90), (.negSucc 121), (.ofNat 79), (.negSucc 110), (.ofNat 11)],
  [(.ofNat 108), (.ofNat 111), (.negSucc 120), (.negSucc 43), (.ofNat 100), (.negSucc 109), (.ofNat 120), (.negSucc 47)],
  [(.negSucc 107), (.ofNat 121), (.ofNat 42), (.ofNat 94), (.ofNat 37), (.ofNat 97), (.negSucc 126), (.ofNat 88)],
  [(.ofNat 107), (.ofNat 53), (.negSucc 2), (.negSucc 125), (.negSucc 109), (.ofNat 0), (.ofNat 119), (.negSucc 98)],
  [(.negSucc 109), (.negSucc 114), (.negSucc 51), (.ofNat 58), (.ofNat 114), (.negSucc 84), (.negSucc 85), (.ofNat 99)]]

def E2 : List (List Int) := [
  [(.ofNat 99), (.negSucc 75), (.negSucc 102), (.negSucc 95), (.negSucc 116), (.negSucc 73), (.negSucc 106), (.ofNat 7)],
  [(.negSucc 103), (.ofNat 112), (.ofNat 110), (.negSucc 39), (.ofNat 98), (.ofNat 102), (.ofNat 114), (.negSucc 48)],
  [(.ofNat 104), (.ofNat 117), (.negSucc 39), (.ofNat 89), (.ofNat 27), (.negSucc 99), (.negSucc 123), (.ofNat 89)],
  [(.negSucc 101), (.ofNat 43), (.ofNat 2), (.negSucc 126), (.negSucc 104), (.ofNat 9), (.ofNat 105), (.negSucc 96)],
  [(.ofNat 110), (.negSucc 109), (.ofNat 67), (.ofNat 75), (.ofNat 114), (.ofNat 77), (.negSucc 73), (.ofNat 96)],
  [(.negSucc 116), (.negSucc 94), (.negSucc 98), (.ofNat 89), (.negSucc 67), (.negSucc 119), (.ofNat 33), (.negSucc 97)],
  [(.ofNat 107), (.ofNat 13), (.ofNat 106), (.negSucc 104), (.negSucc 41), (.ofNat 119), (.ofNat 16), (.ofNat 99)],
  [(.negSucc 109), (.ofNat 99), (.negSucc 94), (.ofNat 125), (.ofNat 111), (.ofNat 15), (.negSucc 59), (.negSucc 95)],
  [(.negSucc 40), (.ofNat 85), (.ofNat 100), (.negSucc 26), (.negSucc 115), (.negSucc 104), (.ofNat 104), (.ofNat 110)],
  [(.ofNat 26), (.negSucc 55), (.negSucc 99), (.negSucc 85), (.ofNat 48), (.ofNat 121), (.negSucc 107), (.negSucc 109)],
  [(.negSucc 73), (.negSucc 111), (.ofNat 94), (.ofNat 120), (.ofNat 95), (.negSucc 53), (.ofNat 106), (.ofNat 96)]]

def W2 : List (List Int) := [
  [(.ofNat 93), (.ofNat 58), (.negSucc 112), (.negSucc 106), (.ofNat 70), (.negSucc 36), (.negSucc 21), (.ofNat 64)],
  [(.negSucc 112), (.negSucc 103), (.ofNat 48), (.ofNat 80), (.ofNat 28), (.ofNat 89), (.ofNat 15), (.negSucc 29)],
  [(.ofNat 127), (.negSucc 59), (.negSucc 110), (.ofNat 25), (.negSucc 101), (.negSucc 97), (.ofNat 86), (.ofNat 14)],
  [(.negSucc 113), (.ofNat 88), (.ofNat 60), (.negSucc 93), (.ofNat 114), (.ofNat 38), (.negSucc 86), (.ofNat 53)],
  [(.ofNat 2), (.ofNat 85), (.negSucc 98), (.ofNat 113), (.negSucc 50), (.ofNat 91), (.ofNat 13), (.negSucc 87)],
  [(.negSucc 41), (.ofNat 110), (.ofNat 91), (.negSucc 27), (.negSucc 40), (.negSucc 110), (.negSucc 101), (.ofNat 127)],
  [(.ofNat 7), (.negSucc 40), (.negSucc 29), (.negSucc 35), (.ofNat 97), (.ofNat 90), (.ofNat 65), (.negSucc 114)],
  [(.ofNat 20), (.negSucc 110), (.ofNat 13), (.ofNat 91), (.negSucc 98), (.ofNat 42), (.negSucc 113), (.ofNat 96)],
  [(.ofNat 20), (.ofNat 37), (.ofNat 91), (.negSucc 115), (.ofNat 14), (.negSucc 99), (.ofNat 119), (.negSucc 85)],
  [(.negSucc 13), (.ofNat 79), (.negSucc 101), (.ofNat 27), (.ofNat 100), (.ofNat 109), (.negSucc 115), (.negSucc 2)],
  [(.negSucc 90), (.ofNat 123), (.ofNat 110), (.ofNat 63), (.negSucc 110), (.negSucc 42), (.ofNat 50), (.negSucc 88)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
