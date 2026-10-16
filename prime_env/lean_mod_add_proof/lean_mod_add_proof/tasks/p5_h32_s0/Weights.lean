import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 32 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=32 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.negSucc 120), (.ofNat 122), (.ofNat 78), (.ofNat 120), (.negSucc 75), (.ofNat 121), (.negSucc 91), (.negSucc 111), (.ofNat 120), (.negSucc 111), (.ofNat 120), (.negSucc 117), (.negSucc 75), (.negSucc 105), (.negSucc 87), (.ofNat 120), (.ofNat 113), (.negSucc 86), (.negSucc 122), (.ofNat 59), (.ofNat 57), (.negSucc 107), (.ofNat 123), (.ofNat 100), (.negSucc 117), (.ofNat 79), (.negSucc 121), (.negSucc 104), (.ofNat 90), (.negSucc 92), (.ofNat 86), (.negSucc 113)],
  [(.negSucc 67), (.negSucc 105), (.negSucc 114), (.negSucc 93), (.negSucc 96), (.ofNat 76), (.negSucc 120), (.negSucc 109), (.negSucc 121), (.ofNat 76), (.ofNat 73), (.ofNat 123), (.ofNat 113), (.ofNat 105), (.negSucc 74), (.negSucc 114), (.negSucc 121), (.negSucc 120), (.negSucc 83), (.negSucc 110), (.ofNat 85), (.negSucc 117), (.ofNat 70), (.negSucc 121), (.ofNat 85), (.ofNat 120), (.ofNat 127), (.ofNat 105), (.negSucc 112), (.negSucc 120), (.negSucc 114), (.ofNat 82)],
  [(.ofNat 110), (.negSucc 10), (.ofNat 126), (.negSucc 69), (.ofNat 116), (.negSucc 110), (.negSucc 60), (.ofNat 81), (.ofNat 119), (.ofNat 120), (.negSucc 112), (.negSucc 113), (.ofNat 115), (.ofNat 116), (.ofNat 117), (.ofNat 85), (.ofNat 117), (.negSucc 60), (.ofNat 109), (.ofNat 124), (.negSucc 112), (.ofNat 47), (.negSucc 115), (.ofNat 123), (.ofNat 81), (.ofNat 85), (.negSucc 112), (.ofNat 119), (.negSucc 117), (.negSucc 39), (.negSucc 111), (.ofNat 83)],
  [(.ofNat 109), (.ofNat 114), (.negSucc 115), (.ofNat 115), (.negSucc 123), (.negSucc 111), (.ofNat 114), (.ofNat 121), (.negSucc 36), (.ofNat 86), (.negSucc 112), (.ofNat 60), (.negSucc 76), (.negSucc 2), (.negSucc 121), (.ofNat 99), (.negSucc 65), (.ofNat 116), (.ofNat 112), (.negSucc 118), (.ofNat 124), (.ofNat 120), (.negSucc 114), (.negSucc 109), (.negSucc 115), (.negSucc 111), (.ofNat 59), (.ofNat 36), (.ofNat 62), (.ofNat 114), (.ofNat 57), (.negSucc 117)],
  [(.negSucc 78), (.negSucc 121), (.ofNat 92), (.negSucc 123), (.ofNat 115), (.ofNat 70), (.ofNat 110), (.ofNat 80), (.negSucc 97), (.negSucc 113), (.ofNat 63), (.ofNat 94), (.negSucc 121), (.negSucc 116), (.ofNat 117), (.negSucc 118), (.negSucc 90), (.ofNat 112), (.negSucc 66), (.ofNat 93), (.negSucc 114), (.ofNat 97), (.ofNat 59), (.ofNat 56), (.ofNat 126), (.negSucc 113), (.ofNat 94), (.negSucc 117), (.ofNat 121), (.ofNat 112), (.ofNat 121), (.ofNat 125)]]

def E2 : List (List Int) := [
  [(.negSucc 117), (.ofNat 108), (.negSucc 122), (.ofNat 117), (.ofNat 95), (.negSucc 77), (.ofNat 85), (.negSucc 82), (.negSucc 106), (.ofNat 113), (.negSucc 120), (.negSucc 67), (.ofNat 113), (.negSucc 120), (.negSucc 118), (.negSucc 116), (.negSucc 116), (.negSucc 122), (.negSucc 76), (.ofNat 83), (.negSucc 123), (.ofNat 114), (.ofNat 116), (.ofNat 89), (.negSucc 71), (.ofNat 85), (.negSucc 126), (.ofNat 94), (.negSucc 67), (.ofNat 121), (.ofNat 111), (.ofNat 116)],
  [(.ofNat 52), (.negSucc 122), (.ofNat 121), (.negSucc 78), (.ofNat 59), (.negSucc 120), (.ofNat 121), (.negSucc 119), (.ofNat 127), (.negSucc 73), (.negSucc 83), (.ofNat 119), (.ofNat 118), (.negSucc 102), (.ofNat 126), (.ofNat 66), (.ofNat 92), (.negSucc 75), (.ofNat 114), (.negSucc 117), (.ofNat 118), (.negSucc 90), (.ofNat 113), (.ofNat 84), (.negSucc 88), (.negSucc 112), (.ofNat 120), (.ofNat 123), (.ofNat 117), (.ofNat 90), (.negSucc 89), (.negSucc 124)],
  [(.ofNat 120), (.ofNat 125), (.negSucc 64), (.negSucc 85), (.negSucc 116), (.negSucc 68), (.ofNat 65), (.negSucc 56), (.negSucc 122), (.negSucc 122), (.ofNat 114), (.negSucc 123), (.negSucc 78), (.ofNat 103), (.negSucc 115), (.ofNat 89), (.ofNat 56), (.ofNat 116), (.ofNat 111), (.ofNat 125), (.negSucc 78), (.negSucc 122), (.negSucc 82), (.negSucc 114), (.ofNat 122), (.negSucc 115), (.negSucc 83), (.ofNat 57), (.ofNat 114), (.negSucc 113), (.negSucc 121), (.ofNat 123)],
  [(.ofNat 83), (.negSucc 108), (.negSucc 90), (.ofNat 121), (.ofNat 124), (.ofNat 114), (.negSucc 116), (.ofNat 117), (.ofNat 106), (.negSucc 70), (.ofNat 112), (.ofNat 118), (.negSucc 121), (.ofNat 120), (.ofNat 82), (.negSucc 119), (.negSucc 115), (.ofNat 116), (.negSucc 85), (.negSucc 115), (.negSucc 65), (.negSucc 59), (.negSucc 123), (.ofNat 124), (.negSucc 125), (.ofNat 85), (.negSucc 86), (.negSucc 116), (.negSucc 94), (.negSucc 115), (.negSucc 62), (.negSucc 80)],
  [(.negSucc 110), (.ofNat 47), (.ofNat 121), (.negSucc 126), (.negSucc 123), (.ofNat 115), (.negSucc 112), (.ofNat 115), (.ofNat 50), (.ofNat 118), (.negSucc 73), (.negSucc 92), (.negSucc 83), (.negSucc 1), (.ofNat 84), (.ofNat 127), (.ofNat 125), (.negSucc 77), (.negSucc 122), (.ofNat 78), (.ofNat 116), (.ofNat 117), (.negSucc 77), (.negSucc 121), (.ofNat 120), (.ofNat 121), (.ofNat 123), (.negSucc 111), (.negSucc 122), (.ofNat 63), (.ofNat 117), (.negSucc 80)]]

def W2 : List (List Int) := [
  [(.ofNat 117), (.ofNat 116), (.negSucc 87), (.ofNat 92), (.ofNat 119), (.negSucc 71), (.ofNat 112), (.negSucc 60), (.negSucc 77), (.negSucc 76), (.negSucc 121), (.negSucc 80), (.negSucc 115), (.ofNat 116), (.ofNat 118), (.negSucc 115), (.negSucc 123), (.ofNat 92), (.ofNat 87), (.negSucc 120), (.negSucc 70), (.negSucc 121), (.ofNat 116), (.ofNat 127), (.negSucc 83), (.ofNat 124), (.ofNat 124), (.negSucc 119), (.ofNat 116), (.negSucc 85), (.negSucc 77), (.negSucc 124)],
  [(.negSucc 69), (.negSucc 125), (.ofNat 119), (.ofNat 72), (.negSucc 124), (.negSucc 121), (.negSucc 94), (.ofNat 116), (.ofNat 120), (.ofNat 115), (.negSucc 79), (.negSucc 90), (.ofNat 73), (.negSucc 78), (.negSucc 84), (.ofNat 66), (.ofNat 118), (.ofNat 122), (.negSucc 114), (.ofNat 93), (.negSucc 83), (.negSucc 93), (.ofNat 117), (.negSucc 114), (.ofNat 121), (.ofNat 81), (.negSucc 126), (.negSucc 105), (.ofNat 118), (.negSucc 122), (.negSucc 122), (.ofNat 119)],
  [(.negSucc 120), (.ofNat 122), (.negSucc 124), (.negSucc 117), (.ofNat 120), (.negSucc 77), (.negSucc 121), (.ofNat 112), (.negSucc 126), (.ofNat 115), (.ofNat 113), (.ofNat 119), (.ofNat 123), (.negSucc 122), (.negSucc 76), (.ofNat 97), (.negSucc 86), (.ofNat 64), (.negSucc 114), (.ofNat 70), (.ofNat 118), (.ofNat 115), (.negSucc 79), (.ofNat 54), (.negSucc 126), (.negSucc 115), (.ofNat 117), (.ofNat 104), (.negSucc 83), (.negSucc 63), (.negSucc 74), (.negSucc 87)],
  [(.negSucc 80), (.negSucc 91), (.ofNat 120), (.ofNat 127), (.negSucc 89), (.ofNat 116), (.negSucc 43), (.negSucc 85), (.ofNat 119), (.negSucc 78), (.ofNat 115), (.negSucc 123), (.ofNat 86), (.negSucc 73), (.ofNat 119), (.negSucc 121), (.negSucc 71), (.negSucc 116), (.ofNat 79), (.negSucc 114), (.negSucc 123), (.ofNat 117), (.negSucc 121), (.ofNat 93), (.ofNat 119), (.negSucc 114), (.negSucc 52), (.ofNat 122), (.negSucc 121), (.ofNat 117), (.ofNat 116), (.negSucc 85)],
  [(.ofNat 109), (.negSucc 74), (.negSucc 81), (.negSucc 120), (.negSucc 80), (.ofNat 112), (.ofNat 117), (.negSucc 122), (.negSucc 86), (.negSucc 122), (.negSucc 66), (.ofNat 117), (.negSucc 115), (.ofNat 114), (.negSucc 125), (.ofNat 126), (.ofNat 116), (.negSucc 114), (.ofNat 120), (.ofNat 124), (.ofNat 115), (.negSucc 66), (.negSucc 84), (.negSucc 121), (.negSucc 84), (.ofNat 68), (.negSucc 103), (.negSucc 20), (.negSucc 86), (.ofNat 113), (.ofNat 114), (.ofNat 119)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
