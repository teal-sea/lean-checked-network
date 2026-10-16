import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.ofNat 116), (.ofNat 64), (.negSucc 110), (.ofNat 112), (.negSucc 109), (.ofNat 85), (.negSucc 120), (.ofNat 96), (.negSucc 112), (.ofNat 105), (.negSucc 86), (.ofNat 113), (.ofNat 120), (.ofNat 84), (.ofNat 121), (.ofNat 72)],
  [(.ofNat 105), (.ofNat 120), (.negSucc 114), (.negSucc 100), (.ofNat 110), (.negSucc 100), (.ofNat 94), (.ofNat 106), (.ofNat 110), (.negSucc 92), (.negSucc 119), (.ofNat 115), (.negSucc 82), (.negSucc 98), (.negSucc 100), (.ofNat 96)],
  [(.negSucc 27), (.negSucc 104), (.negSucc 74), (.ofNat 102), (.negSucc 120), (.ofNat 110), (.ofNat 99), (.negSucc 112), (.ofNat 113), (.negSucc 108), (.ofNat 97), (.ofNat 101), (.negSucc 106), (.ofNat 112), (.negSucc 89), (.ofNat 116)],
  [(.negSucc 114), (.negSucc 80), (.ofNat 109), (.ofNat 1), (.ofNat 73), (.negSucc 115), (.negSucc 104), (.ofNat 91), (.ofNat 104), (.negSucc 118), (.ofNat 115), (.ofNat 67), (.ofNat 111), (.negSucc 110), (.ofNat 114), (.ofNat 78)],
  [(.negSucc 112), (.ofNat 117), (.ofNat 109), (.negSucc 99), (.ofNat 101), (.ofNat 107), (.negSucc 13), (.ofNat 115), (.ofNat 75), (.negSucc 91), (.negSucc 113), (.negSucc 113), (.ofNat 52), (.ofNat 112), (.negSucc 50), (.negSucc 108)],
  [(.negSucc 98), (.negSucc 41), (.ofNat 112), (.ofNat 112), (.negSucc 109), (.negSucc 111), (.ofNat 119), (.negSucc 30), (.negSucc 110), (.ofNat 109), (.negSucc 13), (.negSucc 111), (.negSucc 116), (.negSucc 110), (.negSucc 113), (.negSucc 106)],
  [(.ofNat 104), (.negSucc 126), (.negSucc 40), (.negSucc 116), (.ofNat 111), (.ofNat 85), (.negSucc 39), (.negSucc 115), (.negSucc 107), (.ofNat 108), (.ofNat 117), (.negSucc 102), (.ofNat 68), (.ofNat 106), (.ofNat 91), (.negSucc 112)]]

def E2 : List (List Int) := [
  [(.negSucc 113), (.ofNat 108), (.ofNat 73), (.negSucc 108), (.negSucc 108), (.ofNat 106), (.negSucc 50), (.negSucc 106), (.ofNat 64), (.ofNat 108), (.ofNat 107), (.ofNat 99), (.ofNat 98), (.ofNat 111), (.negSucc 100), (.ofNat 120)],
  [(.negSucc 109), (.negSucc 102), (.negSucc 85), (.ofNat 110), (.ofNat 84), (.negSucc 118), (.negSucc 107), (.ofNat 108), (.ofNat 114), (.ofNat 84), (.ofNat 99), (.ofNat 29), (.negSucc 121), (.negSucc 99), (.negSucc 100), (.ofNat 101)],
  [(.negSucc 93), (.negSucc 102), (.negSucc 126), (.negSucc 112), (.negSucc 69), (.ofNat 110), (.ofNat 111), (.ofNat 74), (.ofNat 112), (.negSucc 95), (.negSucc 121), (.negSucc 122), (.negSucc 83), (.ofNat 85), (.ofNat 112), (.ofNat 82)],
  [(.ofNat 107), (.ofNat 118), (.negSucc 100), (.ofNat 112), (.negSucc 100), (.negSucc 107), (.ofNat 85), (.negSucc 107), (.ofNat 49), (.negSucc 115), (.negSucc 86), (.negSucc 101), (.ofNat 113), (.ofNat 89), (.negSucc 1), (.negSucc 101)],
  [(.ofNat 113), (.ofNat 83), (.negSucc 1), (.negSucc 97), (.ofNat 115), (.ofNat 100), (.negSucc 113), (.ofNat 46), (.negSucc 91), (.negSucc 94), (.ofNat 108), (.negSucc 89), (.negSucc 33), (.negSucc 111), (.negSucc 105), (.negSucc 114)],
  [(.ofNat 107), (.negSucc 115), (.ofNat 108), (.ofNat 99), (.negSucc 111), (.negSucc 91), (.negSucc 80), (.ofNat 111), (.negSucc 105), (.negSucc 64), (.negSucc 73), (.ofNat 87), (.negSucc 96), (.ofNat 112), (.ofNat 101), (.negSucc 97)],
  [(.negSucc 18), (.negSucc 33), (.ofNat 122), (.negSucc 93), (.ofNat 111), (.ofNat 73), (.ofNat 113), (.negSucc 111), (.negSucc 108), (.ofNat 105), (.negSucc 98), (.ofNat 110), (.ofNat 93), (.negSucc 107), (.ofNat 113), (.ofNat 5)]]

def W2 : List (List Int) := [
  [(.negSucc 112), (.ofNat 111), (.negSucc 112), (.negSucc 117), (.ofNat 105), (.negSucc 109), (.ofNat 113), (.negSucc 111), (.negSucc 121), (.ofNat 63), (.ofNat 119), (.ofNat 124), (.ofNat 77), (.ofNat 84), (.negSucc 111), (.negSucc 58)],
  [(.negSucc 123), (.ofNat 118), (.ofNat 14), (.ofNat 119), (.negSucc 114), (.ofNat 91), (.ofNat 111), (.ofNat 97), (.negSucc 112), (.negSucc 66), (.negSucc 118), (.ofNat 116), (.negSucc 115), (.negSucc 121), (.ofNat 75), (.ofNat 71)],
  [(.negSucc 90), (.negSucc 113), (.ofNat 126), (.negSucc 118), (.ofNat 17), (.negSucc 56), (.negSucc 114), (.ofNat 110), (.negSucc 85), (.negSucc 124), (.negSucc 14), (.ofNat 70), (.ofNat 55), (.ofNat 116), (.ofNat 107), (.ofNat 127)],
  [(.ofNat 87), (.negSucc 92), (.ofNat 109), (.ofNat 114), (.ofNat 84), (.negSucc 95), (.negSucc 104), (.negSucc 112), (.ofNat 112), (.negSucc 100), (.ofNat 115), (.negSucc 108), (.ofNat 112), (.negSucc 111), (.negSucc 115), (.ofNat 101)],
  [(.ofNat 123), (.ofNat 112), (.ofNat 96), (.negSucc 99), (.negSucc 101), (.ofNat 124), (.ofNat 112), (.negSucc 117), (.ofNat 118), (.negSucc 61), (.negSucc 99), (.negSucc 115), (.negSucc 96), (.ofNat 112), (.negSucc 108), (.negSucc 7)],
  [(.ofNat 119), (.negSucc 48), (.negSucc 74), (.ofNat 86), (.ofNat 126), (.negSucc 118), (.negSucc 81), (.ofNat 119), (.ofNat 108), (.ofNat 107), (.negSucc 107), (.negSucc 104), (.negSucc 113), (.negSucc 90), (.ofNat 127), (.negSucc 122)],
  [(.ofNat 19), (.negSucc 115), (.negSucc 121), (.ofNat 65), (.negSucc 116), (.ofNat 114), (.negSucc 108), (.ofNat 20), (.negSucc 62), (.ofNat 121), (.ofNat 105), (.ofNat 70), (.ofNat 114), (.negSucc 58), (.ofNat 61), (.negSucc 115)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
