import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 32 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=32 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.ofNat 112), (.ofNat 125), (.ofNat 115), (.ofNat 110), (.negSucc 105), (.negSucc 110), (.negSucc 92), (.ofNat 124), (.negSucc 83), (.ofNat 76), (.ofNat 119), (.ofNat 120), (.negSucc 115), (.negSucc 111), (.ofNat 112), (.negSucc 119), (.ofNat 114), (.ofNat 0), (.ofNat 75), (.negSucc 118), (.ofNat 100), (.negSucc 122), (.negSucc 84), (.negSucc 118), (.ofNat 45), (.ofNat 126), (.ofNat 56), (.ofNat 68), (.ofNat 70), (.negSucc 92), (.negSucc 121), (.negSucc 63)],
  [(.negSucc 73), (.negSucc 117), (.negSucc 78), (.negSucc 88), (.negSucc 113), (.ofNat 85), (.negSucc 67), (.negSucc 118), (.negSucc 67), (.ofNat 75), (.ofNat 56), (.ofNat 60), (.ofNat 123), (.negSucc 110), (.ofNat 116), (.negSucc 48), (.ofNat 117), (.ofNat 0), (.negSucc 116), (.negSucc 66), (.negSucc 120), (.ofNat 109), (.ofNat 115), (.ofNat 125), (.ofNat 83), (.negSucc 119), (.ofNat 118), (.ofNat 121), (.negSucc 115), (.ofNat 119), (.ofNat 127), (.negSucc 119)],
  [(.negSucc 119), (.ofNat 73), (.negSucc 93), (.negSucc 120), (.ofNat 41), (.ofNat 121), (.ofNat 119), (.ofNat 78), (.ofNat 117), (.negSucc 118), (.negSucc 116), (.negSucc 113), (.negSucc 116), (.ofNat 70), (.negSucc 74), (.ofNat 117), (.negSucc 68), (.ofNat 0), (.negSucc 115), (.ofNat 115), (.ofNat 123), (.ofNat 63), (.ofNat 114), (.negSucc 119), (.negSucc 123), (.ofNat 86), (.ofNat 95), (.ofNat 79), (.negSucc 112), (.negSucc 125), (.negSucc 116), (.negSucc 79)],
  [(.negSucc 81), (.ofNat 90), (.ofNat 119), (.negSucc 60), (.ofNat 120), (.ofNat 62), (.negSucc 125), (.ofNat 77), (.negSucc 123), (.ofNat 125), (.negSucc 107), (.negSucc 113), (.ofNat 93), (.ofNat 118), (.negSucc 120), (.ofNat 110), (.negSucc 121), (.ofNat 0), (.ofNat 76), (.ofNat 108), (.negSucc 115), (.negSucc 116), (.negSucc 68), (.ofNat 84), (.ofNat 124), (.ofNat 90), (.negSucc 109), (.negSucc 111), (.ofNat 90), (.ofNat 119), (.ofNat 79), (.ofNat 109)],
  [(.ofNat 112), (.negSucc 119), (.negSucc 124), (.ofNat 114), (.ofNat 97), (.negSucc 115), (.ofNat 119), (.negSucc 116), (.ofNat 120), (.negSucc 117), (.ofNat 83), (.ofNat 75), (.ofNat 72), (.ofNat 79), (.negSucc 83), (.negSucc 88), (.negSucc 78), (.ofNat 0), (.ofNat 119), (.negSucc 82), (.ofNat 79), (.ofNat 125), (.negSucc 119), (.ofNat 79), (.negSucc 116), (.negSucc 117), (.negSucc 116), (.negSucc 113), (.ofNat 120), (.negSucc 82), (.ofNat 88), (.ofNat 116)]]

def E2 : List (List Int) := [
  [(.negSucc 77), (.ofNat 116), (.negSucc 93), (.ofNat 110), (.ofNat 115), (.ofNat 117), (.negSucc 122), (.negSucc 74), (.ofNat 94), (.negSucc 117), (.negSucc 57), (.negSucc 60), (.negSucc 87), (.ofNat 108), (.ofNat 81), (.negSucc 114), (.ofNat 120), (.ofNat 0), (.negSucc 87), (.ofNat 111), (.negSucc 119), (.ofNat 127), (.negSucc 90), (.negSucc 123), (.ofNat 48), (.ofNat 118), (.negSucc 113), (.ofNat 114), (.ofNat 121), (.ofNat 116), (.ofNat 109), (.negSucc 81)],
  [(.negSucc 120), (.negSucc 122), (.negSucc 79), (.negSucc 87), (.ofNat 111), (.ofNat 97), (.ofNat 117), (.ofNat 115), (.negSucc 117), (.ofNat 81), (.ofNat 112), (.negSucc 118), (.ofNat 119), (.negSucc 80), (.negSucc 110), (.negSucc 106), (.ofNat 62), (.ofNat 0), (.ofNat 108), (.negSucc 60), (.ofNat 68), (.negSucc 119), (.negSucc 118), (.ofNat 116), (.negSucc 117), (.negSucc 80), (.ofNat 79), (.ofNat 109), (.ofNat 88), (.negSucc 123), (.ofNat 70), (.negSucc 118)],
  [(.negSucc 57), (.ofNat 119), (.ofNat 117), (.negSucc 119), (.negSucc 84), (.negSucc 107), (.negSucc 85), (.negSucc 123), (.ofNat 123), (.ofNat 82), (.ofNat 109), (.negSucc 90), (.negSucc 122), (.negSucc 116), (.negSucc 114), (.ofNat 92), (.negSucc 113), (.ofNat 0), (.ofNat 113), (.negSucc 117), (.ofNat 85), (.ofNat 99), (.negSucc 48), (.negSucc 81), (.ofNat 123), (.negSucc 85), (.ofNat 118), (.negSucc 77), (.negSucc 113), (.ofNat 120), (.negSucc 113), (.negSucc 59)],
  [(.ofNat 112), (.negSucc 89), (.negSucc 122), (.negSucc 53), (.negSucc 117), (.negSucc 114), (.negSucc 90), (.ofNat 116), (.negSucc 111), (.negSucc 116), (.negSucc 92), (.ofNat 108), (.ofNat 113), (.negSucc 67), (.ofNat 78), (.ofNat 119), (.negSucc 112), (.ofNat 0), (.negSucc 68), (.negSucc 79), (.negSucc 114), (.ofNat 52), (.ofNat 114), (.negSucc 92), (.negSucc 121), (.ofNat 121), (.ofNat 79), (.negSucc 119), (.negSucc 113), (.negSucc 91), (.ofNat 122), (.ofNat 113)],
  [(.ofNat 109), (.negSucc 86), (.ofNat 115), (.ofNat 112), (.negSucc 44), (.ofNat 39), (.ofNat 119), (.negSucc 84), (.ofNat 77), (.ofNat 122), (.negSucc 118), (.ofNat 112), (.negSucc 64), (.ofNat 112), (.ofNat 119), (.ofNat 64), (.ofNat 97), (.ofNat 0), (.negSucc 122), (.ofNat 110), (.ofNat 126), (.negSucc 118), (.ofNat 113), (.ofNat 118), (.ofNat 85), (.negSucc 123), (.negSucc 111), (.negSucc 71), (.ofNat 62), (.negSucc 89), (.negSucc 121), (.ofNat 111)]]

def W2 : List (List Int) := [
  [(.negSucc 114), (.ofNat 122), (.ofNat 82), (.ofNat 30), (.negSucc 66), (.negSucc 114), (.ofNat 95), (.negSucc 75), (.negSucc 123), (.ofNat 84), (.negSucc 26), (.negSucc 63), (.negSucc 77), (.negSucc 119), (.ofNat 115), (.ofNat 118), (.ofNat 117), (.ofNat 0), (.ofNat 114), (.negSucc 110), (.negSucc 121), (.negSucc 125), (.ofNat 122), (.ofNat 121), (.ofNat 125), (.ofNat 121), (.negSucc 110), (.negSucc 75), (.ofNat 74), (.ofNat 83), (.negSucc 122), (.negSucc 112)],
  [(.negSucc 110), (.negSucc 125), (.negSucc 118), (.negSucc 114), (.negSucc 119), (.ofNat 55), (.ofNat 79), (.ofNat 118), (.ofNat 118), (.negSucc 117), (.ofNat 117), (.negSucc 119), (.negSucc 82), (.negSucc 68), (.negSucc 64), (.ofNat 108), (.ofNat 116), (.ofNat 0), (.ofNat 116), (.ofNat 75), (.ofNat 127), (.ofNat 111), (.ofNat 65), (.negSucc 125), (.negSucc 118), (.negSucc 80), (.negSucc 115), (.ofNat 113), (.negSucc 112), (.ofNat 90), (.ofNat 102), (.ofNat 80)],
  [(.ofNat 77), (.ofNat 118), (.ofNat 126), (.negSucc 110), (.negSucc 86), (.ofNat 122), (.negSucc 118), (.negSucc 124), (.negSucc 83), (.ofNat 125), (.ofNat 108), (.negSucc 87), (.ofNat 118), (.ofNat 112), (.negSucc 122), (.negSucc 97), (.negSucc 89), (.ofNat 0), (.negSucc 61), (.ofNat 120), (.negSucc 117), (.ofNat 15), (.negSucc 115), (.ofNat 118), (.ofNat 84), (.negSucc 93), (.ofNat 41), (.ofNat 115), (.negSucc 116), (.negSucc 120), (.ofNat 69), (.ofNat 120)],
  [(.ofNat 122), (.negSucc 77), (.negSucc 118), (.ofNat 97), (.ofNat 112), (.ofNat 90), (.ofNat 126), (.ofNat 118), (.negSucc 87), (.negSucc 118), (.negSucc 96), (.ofNat 114), (.negSucc 124), (.ofNat 112), (.negSucc 83), (.negSucc 120), (.negSucc 122), (.ofNat 0), (.negSucc 122), (.ofNat 76), (.ofNat 62), (.negSucc 114), (.negSucc 113), (.negSucc 82), (.ofNat 90), (.ofNat 120), (.ofNat 122), (.negSucc 77), (.ofNat 76), (.ofNat 127), (.negSucc 118), (.ofNat 78)],
  [(.ofNat 65), (.negSucc 90), (.ofNat 82), (.ofNat 121), (.ofNat 115), (.negSucc 112), (.negSucc 120), (.negSucc 86), (.ofNat 119), (.ofNat 83), (.negSucc 119), (.ofNat 113), (.ofNat 117), (.negSucc 75), (.ofNat 114), (.negSucc 15), (.negSucc 67), (.ofNat 0), (.negSucc 85), (.negSucc 113), (.ofNat 97), (.ofNat 127), (.ofNat 87), (.negSucc 87), (.negSucc 119), (.negSucc 125), (.ofNat 93), (.negSucc 120), (.ofNat 124), (.negSucc 119), (.ofNat 126), (.negSucc 114)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
