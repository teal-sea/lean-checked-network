import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.negSucc 108), (.negSucc 99), (.ofNat 90), (.ofNat 91), (.negSucc 113), (.ofNat 111), (.ofNat 123), (.negSucc 96), (.negSucc 84), (.ofNat 115), (.ofNat 100), (.ofNat 67), (.ofNat 105), (.ofNat 109), (.ofNat 111), (.negSucc 118)],
  [(.ofNat 111), (.negSucc 99), (.ofNat 43), (.negSucc 103), (.negSucc 42), (.negSucc 109), (.ofNat 107), (.negSucc 104), (.ofNat 105), (.negSucc 107), (.negSucc 79), (.ofNat 109), (.negSucc 75), (.ofNat 31), (.ofNat 68), (.negSucc 113)],
  [(.negSucc 107), (.ofNat 113), (.negSucc 126), (.ofNat 33), (.ofNat 106), (.negSucc 90), (.ofNat 50), (.negSucc 99), (.ofNat 127), (.ofNat 101), (.negSucc 106), (.negSucc 77), (.negSucc 108), (.negSucc 96), (.negSucc 95), (.negSucc 89)],
  [(.ofNat 107), (.ofNat 68), (.ofNat 115), (.ofNat 105), (.negSucc 104), (.ofNat 101), (.negSucc 102), (.ofNat 23), (.ofNat 106), (.negSucc 90), (.negSucc 107), (.negSucc 103), (.ofNat 111), (.ofNat 100), (.negSucc 109), (.ofNat 104)],
  [(.negSucc 92), (.negSucc 111), (.negSucc 109), (.negSucc 100), (.negSucc 109), (.negSucc 76), (.negSucc 118), (.ofNat 106), (.ofNat 29), (.ofNat 91), (.negSucc 31), (.ofNat 114), (.ofNat 109), (.negSucc 105), (.negSucc 109), (.ofNat 112)],
  [(.negSucc 100), (.ofNat 85), (.ofNat 108), (.negSucc 109), (.ofNat 113), (.negSucc 113), (.negSucc 88), (.ofNat 116), (.negSucc 113), (.ofNat 116), (.ofNat 119), (.ofNat 94), (.negSucc 113), (.ofNat 117), (.ofNat 76), (.ofNat 105)],
  [(.ofNat 112), (.ofNat 104), (.negSucc 89), (.ofNat 106), (.ofNat 70), (.ofNat 100), (.ofNat 57), (.ofNat 49), (.negSucc 111), (.negSucc 117), (.ofNat 112), (.negSucc 119), (.negSucc 100), (.negSucc 114), (.ofNat 111), (.negSucc 88)]]

def E2 : List (List Int) := [
  [(.negSucc 111), (.ofNat 121), (.negSucc 113), (.ofNat 97), (.negSucc 116), (.negSucc 107), (.negSucc 123), (.negSucc 105), (.negSucc 115), (.ofNat 114), (.ofNat 54), (.negSucc 49), (.negSucc 102), (.ofNat 105), (.ofNat 111), (.ofNat 68)],
  [(.negSucc 101), (.ofNat 98), (.ofNat 111), (.negSucc 118), (.ofNat 28), (.negSucc 45), (.negSucc 109), (.ofNat 28), (.negSucc 36), (.negSucc 112), (.ofNat 126), (.negSucc 122), (.ofNat 116), (.ofNat 74), (.ofNat 109), (.negSucc 120)],
  [(.ofNat 106), (.negSucc 119), (.negSucc 107), (.negSucc 81), (.ofNat 117), (.ofNat 107), (.negSucc 108), (.ofNat 127), (.ofNat 120), (.ofNat 109), (.ofNat 106), (.ofNat 84), (.ofNat 22), (.negSucc 96), (.negSucc 17), (.negSucc 111)],
  [(.negSucc 113), (.ofNat 45), (.ofNat 117), (.ofNat 115), (.negSucc 47), (.negSucc 90), (.ofNat 47), (.ofNat 113), (.ofNat 115), (.negSucc 101), (.ofNat 69), (.ofNat 117), (.negSucc 112), (.ofNat 117), (.negSucc 114), (.negSucc 98)],
  [(.ofNat 118), (.ofNat 110), (.negSucc 69), (.negSucc 83), (.negSucc 126), (.negSucc 115), (.ofNat 115), (.ofNat 66), (.ofNat 122), (.ofNat 68), (.negSucc 115), (.negSucc 103), (.ofNat 93), (.negSucc 106), (.negSucc 108), (.negSucc 5)],
  [(.negSucc 106), (.negSucc 91), (.negSucc 117), (.negSucc 103), (.ofNat 105), (.ofNat 109), (.ofNat 118), (.negSucc 96), (.negSucc 48), (.ofNat 100), (.negSucc 115), (.negSucc 117), (.ofNat 113), (.ofNat 112), (.negSucc 81), (.ofNat 119)],
  [(.ofNat 102), (.negSucc 87), (.ofNat 94), (.ofNat 112), (.ofNat 102), (.ofNat 74), (.ofNat 39), (.negSucc 111), (.negSucc 109), (.negSucc 109), (.negSucc 86), (.ofNat 111), (.negSucc 118), (.negSucc 112), (.ofNat 100), (.ofNat 107)]]

def W2 : List (List Int) := [
  [(.ofNat 98), (.negSucc 63), (.negSucc 105), (.negSucc 99), (.ofNat 103), (.negSucc 114), (.negSucc 78), (.ofNat 113), (.ofNat 7), (.ofNat 120), (.ofNat 119), (.ofNat 109), (.negSucc 105), (.negSucc 106), (.ofNat 112), (.negSucc 97)],
  [(.negSucc 83), (.negSucc 106), (.ofNat 51), (.negSucc 102), (.ofNat 83), (.ofNat 102), (.negSucc 114), (.ofNat 105), (.negSucc 120), (.negSucc 112), (.ofNat 110), (.negSucc 110), (.ofNat 109), (.ofNat 103), (.ofNat 80), (.ofNat 25)],
  [(.negSucc 97), (.ofNat 91), (.ofNat 98), (.ofNat 112), (.negSucc 102), (.ofNat 115), (.negSucc 113), (.ofNat 3), (.negSucc 112), (.ofNat 106), (.ofNat 8), (.negSucc 111), (.ofNat 37), (.negSucc 107), (.negSucc 103), (.ofNat 124)],
  [(.ofNat 112), (.ofNat 118), (.negSucc 104), (.ofNat 98), (.ofNat 101), (.negSucc 98), (.negSucc 29), (.negSucc 102), (.negSucc 75), (.negSucc 87), (.negSucc 116), (.ofNat 115), (.negSucc 106), (.ofNat 116), (.negSucc 102), (.ofNat 112)],
  [(.negSucc 104), (.negSucc 111), (.ofNat 112), (.negSucc 108), (.ofNat 115), (.negSucc 38), (.ofNat 114), (.negSucc 110), (.ofNat 96), (.ofNat 72), (.negSucc 114), (.ofNat 94), (.ofNat 93), (.negSucc 105), (.negSucc 107), (.ofNat 71)],
  [(.ofNat 109), (.negSucc 86), (.negSucc 109), (.ofNat 80), (.negSucc 101), (.ofNat 106), (.ofNat 118), (.negSucc 96), (.ofNat 118), (.negSucc 52), (.negSucc 76), (.negSucc 105), (.ofNat 111), (.ofNat 33), (.negSucc 8), (.negSucc 94)],
  [(.negSucc 112), (.ofNat 103), (.ofNat 104), (.ofNat 96), (.negSucc 126), (.negSucc 100), (.ofNat 81), (.ofNat 78), (.ofNat 106), (.negSucc 115), (.ofNat 88), (.negSucc 85), (.negSucc 111), (.ofNat 44), (.ofNat 104), (.negSucc 118)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
