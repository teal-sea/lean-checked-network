import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 5

5 possible inputs per side, 32 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=5 H=32 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 5

def E1 : List (List Int) := [
  [(.ofNat 112), (.ofNat 106), (.ofNat 92), (.negSucc 114), (.ofNat 79), (.negSucc 66), (.ofNat 0), (.negSucc 114), (.ofNat 119), (.negSucc 72), (.negSucc 110), (.ofNat 76), (.ofNat 125), (.ofNat 64), (.ofNat 75), (.negSucc 115), (.ofNat 109), (.ofNat 103), (.negSucc 120), (.ofNat 0), (.ofNat 115), (.ofNat 55), (.negSucc 115), (.negSucc 89), (.ofNat 119), (.negSucc 115), (.negSucc 93), (.ofNat 110), (.negSucc 69), (.ofNat 110), (.ofNat 107), (.ofNat 78)],
  [(.negSucc 106), (.negSucc 111), (.negSucc 112), (.negSucc 119), (.negSucc 106), (.negSucc 66), (.ofNat 0), (.ofNat 105), (.ofNat 49), (.negSucc 70), (.ofNat 115), (.ofNat 70), (.ofNat 82), (.ofNat 57), (.ofNat 123), (.negSucc 116), (.ofNat 120), (.negSucc 69), (.ofNat 92), (.ofNat 0), (.negSucc 104), (.negSucc 118), (.negSucc 118), (.ofNat 108), (.negSucc 64), (.ofNat 108), (.ofNat 116), (.negSucc 80), (.ofNat 104), (.negSucc 115), (.negSucc 51), (.negSucc 109)],
  [(.ofNat 75), (.ofNat 104), (.negSucc 119), (.ofNat 70), (.ofNat 116), (.ofNat 106), (.ofNat 0), (.negSucc 71), (.negSucc 120), (.ofNat 107), (.negSucc 99), (.negSucc 104), (.negSucc 120), (.negSucc 108), (.ofNat 100), (.ofNat 97), (.negSucc 59), (.negSucc 86), (.ofNat 126), (.ofNat 0), (.ofNat 68), (.negSucc 117), (.negSucc 3), (.negSucc 115), (.negSucc 126), (.negSucc 85), (.ofNat 124), (.negSucc 63), (.negSucc 115), (.ofNat 101), (.negSucc 87), (.ofNat 113)],
  [(.ofNat 65), (.negSucc 62), (.ofNat 78), (.ofNat 124), (.negSucc 107), (.negSucc 113), (.ofNat 0), (.negSucc 73), (.negSucc 110), (.negSucc 115), (.ofNat 52), (.ofNat 115), (.negSucc 120), (.ofNat 114), (.negSucc 120), (.ofNat 125), (.negSucc 121), (.ofNat 108), (.ofNat 83), (.ofNat 0), (.ofNat 82), (.ofNat 101), (.ofNat 122), (.ofNat 107), (.negSucc 102), (.negSucc 46), (.negSucc 58), (.ofNat 106), (.ofNat 106), (.negSucc 49), (.ofNat 112), (.negSucc 104)],
  [(.negSucc 104), (.negSucc 80), (.ofNat 122), (.ofNat 97), (.ofNat 63), (.ofNat 109), (.ofNat 0), (.ofNat 108), (.ofNat 111), (.ofNat 111), (.ofNat 89), (.negSucc 108), (.ofNat 98), (.negSucc 102), (.negSucc 115), (.ofNat 72), (.negSucc 101), (.negSucc 113), (.negSucc 116), (.ofNat 0), (.negSucc 103), (.ofNat 124), (.ofNat 100), (.negSucc 59), (.ofNat 120), (.ofNat 102), (.negSucc 125), (.negSucc 114), (.negSucc 60), (.negSucc 86), (.negSucc 114), (.ofNat 64)]]

def E2 : List (List Int) := [
  [(.negSucc 101), (.negSucc 101), (.ofNat 121), (.negSucc 94), (.ofNat 74), (.negSucc 103), (.ofNat 0), (.negSucc 107), (.ofNat 110), (.ofNat 71), (.ofNat 108), (.ofNat 107), (.ofNat 91), (.negSucc 111), (.negSucc 84), (.negSucc 107), (.ofNat 118), (.negSucc 114), (.ofNat 93), (.ofNat 0), (.negSucc 64), (.ofNat 108), (.ofNat 117), (.negSucc 104), (.negSucc 126), (.negSucc 114), (.ofNat 117), (.ofNat 59), (.negSucc 102), (.negSucc 56), (.ofNat 57), (.negSucc 113)],
  [(.ofNat 51), (.ofNat 58), (.ofNat 43), (.negSucc 121), (.ofNat 67), (.ofNat 113), (.ofNat 0), (.ofNat 113), (.ofNat 121), (.negSucc 109), (.negSucc 114), (.negSucc 66), (.negSucc 118), (.ofNat 104), (.ofNat 118), (.ofNat 104), (.ofNat 56), (.ofNat 107), (.ofNat 123), (.ofNat 0), (.negSucc 64), (.ofNat 122), (.ofNat 110), (.ofNat 112), (.negSucc 83), (.ofNat 101), (.negSucc 107), (.ofNat 87), (.ofNat 49), (.ofNat 103), (.negSucc 103), (.ofNat 109)],
  [(.ofNat 85), (.ofNat 81), (.negSucc 119), (.negSucc 85), (.negSucc 101), (.negSucc 105), (.ofNat 0), (.negSucc 105), (.negSucc 74), (.ofNat 115), (.ofNat 107), (.negSucc 75), (.negSucc 120), (.negSucc 77), (.ofNat 116), (.ofNat 123), (.negSucc 118), (.negSucc 81), (.ofNat 93), (.ofNat 0), (.ofNat 110), (.negSucc 35), (.negSucc 102), (.negSucc 111), (.ofNat 118), (.negSucc 52), (.negSucc 121), (.negSucc 110), (.ofNat 72), (.negSucc 112), (.ofNat 114), (.negSucc 75)],
  [(.negSucc 107), (.negSucc 106), (.negSucc 108), (.ofNat 118), (.ofNat 116), (.ofNat 77), (.ofNat 0), (.ofNat 69), (.negSucc 120), (.negSucc 104), (.negSucc 57), (.ofNat 107), (.ofNat 87), (.negSucc 59), (.negSucc 95), (.ofNat 69), (.negSucc 112), (.negSucc 61), (.negSucc 119), (.ofNat 0), (.negSucc 111), (.negSucc 120), (.negSucc 120), (.ofNat 92), (.ofNat 120), (.negSucc 84), (.negSucc 31), (.ofNat 113), (.negSucc 108), (.ofNat 107), (.negSucc 109), (.negSucc 67)],
  [(.ofNat 111), (.ofNat 109), (.ofNat 104), (.ofNat 116), (.negSucc 109), (.ofNat 71), (.ofNat 0), (.ofNat 68), (.negSucc 92), (.ofNat 75), (.negSucc 63), (.negSucc 112), (.ofNat 124), (.ofNat 103), (.negSucc 121), (.negSucc 120), (.ofNat 105), (.ofNat 102), (.negSucc 115), (.ofNat 0), (.ofNat 106), (.negSucc 109), (.negSucc 60), (.ofNat 27), (.negSucc 86), (.ofNat 108), (.ofNat 121), (.negSucc 102), (.ofNat 114), (.negSucc 89), (.ofNat 89), (.ofNat 103)]]

def W2 : List (List Int) := [
  [(.negSucc 105), (.negSucc 114), (.ofNat 47), (.negSucc 98), (.ofNat 115), (.ofNat 108), (.ofNat 0), (.ofNat 107), (.ofNat 120), (.negSucc 115), (.negSucc 89), (.negSucc 77), (.ofNat 84), (.negSucc 80), (.negSucc 125), (.ofNat 124), (.ofNat 118), (.negSucc 110), (.negSucc 121), (.ofNat 0), (.negSucc 61), (.ofNat 122), (.negSucc 56), (.negSucc 92), (.negSucc 121), (.ofNat 115), (.ofNat 107), (.negSucc 75), (.ofNat 108), (.ofNat 72), (.ofNat 109), (.negSucc 75)],
  [(.ofNat 53), (.ofNat 102), (.negSucc 119), (.ofNat 118), (.negSucc 109), (.negSucc 75), (.ofNat 0), (.negSucc 113), (.ofNat 116), (.ofNat 111), (.ofNat 110), (.ofNat 108), (.negSucc 121), (.negSucc 58), (.negSucc 89), (.ofNat 39), (.ofNat 118), (.ofNat 77), (.negSucc 118), (.ofNat 0), (.negSucc 78), (.negSucc 64), (.negSucc 122), (.negSucc 49), (.ofNat 74), (.negSucc 108), (.ofNat 125), (.ofNat 109), (.negSucc 114), (.ofNat 66), (.negSucc 116), (.ofNat 109)],
  [(.ofNat 83), (.negSucc 27), (.negSucc 113), (.ofNat 120), (.ofNat 77), (.negSucc 62), (.ofNat 0), (.ofNat 110), (.negSucc 96), (.negSucc 78), (.negSucc 114), (.negSucc 113), (.negSucc 120), (.ofNat 106), (.ofNat 118), (.negSucc 121), (.negSucc 90), (.ofNat 78), (.ofNat 91), (.ofNat 0), (.ofNat 110), (.negSucc 123), (.negSucc 100), (.ofNat 109), (.ofNat 126), (.ofNat 78), (.ofNat 79), (.negSucc 117), (.ofNat 106), (.negSucc 110), (.ofNat 111), (.negSucc 113)],
  [(.negSucc 106), (.negSucc 77), (.ofNat 98), (.negSucc 72), (.ofNat 81), (.ofNat 106), (.ofNat 0), (.negSucc 70), (.negSucc 123), (.negSucc 72), (.ofNat 106), (.ofNat 109), (.ofNat 97), (.negSucc 112), (.ofNat 121), (.negSucc 114), (.negSucc 122), (.negSucc 105), (.ofNat 126), (.ofNat 0), (.negSucc 114), (.negSucc 104), (.ofNat 114), (.negSucc 114), (.ofNat 107), (.ofNat 70), (.negSucc 121), (.ofNat 109), (.negSucc 47), (.ofNat 116), (.negSucc 69), (.ofNat 107)],
  [(.ofNat 114), (.ofNat 108), (.ofNat 124), (.negSucc 124), (.negSucc 108), (.negSucc 114), (.ofNat 0), (.negSucc 80), (.negSucc 56), (.ofNat 108), (.negSucc 42), (.negSucc 77), (.ofNat 127), (.ofNat 107), (.negSucc 80), (.ofNat 108), (.negSucc 81), (.ofNat 114), (.ofNat 86), (.ofNat 0), (.ofNat 105), (.ofNat 117), (.ofNat 120), (.ofNat 110), (.negSucc 121), (.negSucc 107), (.negSucc 120), (.negSucc 56), (.negSucc 83), (.negSucc 104), (.negSucc 76), (.negSucc 75)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 5 → ∀ b, b < 5 → answer a b = (a + b) % 5

end LeanCheckedNetwork.Net
