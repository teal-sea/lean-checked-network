import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=7 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.ofNat 120), (.ofNat 113), (.ofNat 79), (.ofNat 111), (.ofNat 57), (.ofNat 123), (.negSucc 26), (.negSucc 93), (.ofNat 110), (.negSucc 89), (.ofNat 112), (.negSucc 79), (.ofNat 118), (.negSucc 108), (.negSucc 103), (.ofNat 114)],
  [(.ofNat 101), (.negSucc 123), (.negSucc 82), (.ofNat 114), (.ofNat 117), (.negSucc 119), (.ofNat 113), (.ofNat 9), (.ofNat 114), (.negSucc 25), (.ofNat 116), (.ofNat 113), (.negSucc 115), (.negSucc 6), (.negSucc 86), (.negSucc 115)],
  [(.negSucc 115), (.ofNat 119), (.negSucc 70), (.ofNat 117), (.negSucc 103), (.ofNat 107), (.ofNat 117), (.ofNat 86), (.ofNat 82), (.ofNat 65), (.negSucc 105), (.ofNat 62), (.ofNat 108), (.ofNat 111), (.ofNat 125), (.negSucc 118)],
  [(.negSucc 74), (.negSucc 104), (.ofNat 113), (.ofNat 82), (.negSucc 115), (.negSucc 78), (.ofNat 109), (.negSucc 117), (.negSucc 107), (.negSucc 107), (.negSucc 103), (.negSucc 106), (.negSucc 91), (.negSucc 115), (.ofNat 119), (.ofNat 114)],
  [(.ofNat 104), (.ofNat 76), (.negSucc 123), (.negSucc 111), (.ofNat 103), (.ofNat 39), (.negSucc 76), (.ofNat 122), (.negSucc 120), (.ofNat 120), (.negSucc 113), (.ofNat 83), (.ofNat 79), (.negSucc 118), (.ofNat 101), (.ofNat 66)],
  [(.negSucc 94), (.negSucc 28), (.ofNat 117), (.negSucc 112), (.ofNat 93), (.ofNat 63), (.negSucc 112), (.negSucc 120), (.negSucc 94), (.negSucc 121), (.negSucc 13), (.ofNat 102), (.negSucc 7), (.ofNat 127), (.negSucc 47), (.negSucc 105)],
  [(.negSucc 111), (.negSucc 85), (.negSucc 109), (.negSucc 98), (.negSucc 110), (.negSucc 110), (.negSucc 109), (.ofNat 107), (.negSucc 45), (.ofNat 104), (.ofNat 114), (.negSucc 125), (.negSucc 97), (.ofNat 103), (.negSucc 123), (.ofNat 83)]]

def E2 : List (List Int) := [
  [(.negSucc 124), (.ofNat 117), (.ofNat 124), (.ofNat 119), (.ofNat 44), (.negSucc 104), (.ofNat 79), (.ofNat 92), (.ofNat 3), (.negSucc 81), (.ofNat 121), (.ofNat 107), (.negSucc 93), (.negSucc 43), (.ofNat 107), (.ofNat 115)],
  [(.ofNat 74), (.negSucc 113), (.negSucc 102), (.ofNat 112), (.ofNat 118), (.ofNat 106), (.negSucc 114), (.negSucc 112), (.ofNat 96), (.ofNat 106), (.negSucc 55), (.negSucc 109), (.ofNat 102), (.ofNat 120), (.ofNat 114), (.ofNat 54)],
  [(.ofNat 117), (.ofNat 107), (.negSucc 18), (.ofNat 29), (.negSucc 88), (.ofNat 51), (.negSucc 114), (.ofNat 118), (.ofNat 112), (.negSucc 103), (.negSucc 106), (.negSucc 89), (.negSucc 105), (.negSucc 80), (.ofNat 125), (.negSucc 119)],
  [(.negSucc 71), (.negSucc 78), (.ofNat 100), (.negSucc 114), (.negSucc 121), (.negSucc 97), (.negSucc 106), (.negSucc 107), (.ofNat 82), (.ofNat 108), (.negSucc 108), (.ofNat 112), (.ofNat 114), (.negSucc 115), (.negSucc 96), (.ofNat 45)],
  [(.negSucc 84), (.negSucc 110), (.negSucc 108), (.negSucc 115), (.ofNat 110), (.ofNat 116), (.negSucc 47), (.ofNat 75), (.negSucc 74), (.negSucc 115), (.negSucc 110), (.ofNat 70), (.negSucc 108), (.ofNat 103), (.negSucc 114), (.ofNat 117)],
  [(.ofNat 109), (.ofNat 109), (.ofNat 106), (.negSucc 73), (.ofNat 76), (.negSucc 107), (.ofNat 127), (.ofNat 95), (.negSucc 110), (.ofNat 110), (.ofNat 87), (.negSucc 102), (.ofNat 86), (.ofNat 91), (.negSucc 105), (.negSucc 99)],
  [(.ofNat 73), (.negSucc 100), (.negSucc 122), (.ofNat 89), (.negSucc 116), (.ofNat 106), (.ofNat 104), (.negSucc 98), (.negSucc 113), (.negSucc 78), (.ofNat 115), (.ofNat 46), (.ofNat 0), (.negSucc 115), (.negSucc 35), (.negSucc 99)]]

def W2 : List (List Int) := [
  [(.negSucc 108), (.ofNat 125), (.negSucc 11), (.negSucc 42), (.negSucc 118), (.negSucc 105), (.ofNat 113), (.negSucc 103), (.negSucc 89), (.ofNat 118), (.ofNat 120), (.negSucc 27), (.ofNat 61), (.ofNat 69), (.negSucc 110), (.ofNat 117)],
  [(.negSucc 102), (.negSucc 120), (.ofNat 93), (.ofNat 118), (.ofNat 55), (.ofNat 91), (.ofNat 109), (.ofNat 71), (.ofNat 11), (.negSucc 108), (.negSucc 81), (.ofNat 106), (.ofNat 81), (.negSucc 121), (.negSucc 113), (.negSucc 55)],
  [(.ofNat 107), (.ofNat 106), (.negSucc 120), (.ofNat 110), (.ofNat 108), (.negSucc 84), (.ofNat 85), (.negSucc 74), (.ofNat 110), (.ofNat 92), (.negSucc 109), (.negSucc 80), (.negSucc 123), (.ofNat 2), (.negSucc 5), (.negSucc 108)],
  [(.ofNat 58), (.negSucc 109), (.ofNat 111), (.ofNat 49), (.negSucc 105), (.negSucc 77), (.negSucc 94), (.negSucc 103), (.ofNat 117), (.negSucc 89), (.negSucc 108), (.negSucc 94), (.ofNat 118), (.ofNat 112), (.ofNat 109), (.ofNat 92)],
  [(.negSucc 108), (.ofNat 54), (.negSucc 99), (.negSucc 111), (.negSucc 40), (.ofNat 112), (.negSucc 110), (.ofNat 120), (.ofNat 40), (.ofNat 53), (.negSucc 60), (.ofNat 111), (.negSucc 106), (.negSucc 71), (.ofNat 113), (.ofNat 95)],
  [(.ofNat 74), (.negSucc 23), (.ofNat 111), (.negSucc 112), (.ofNat 118), (.negSucc 114), (.negSucc 113), (.negSucc 114), (.negSucc 86), (.ofNat 78), (.ofNat 88), (.ofNat 88), (.ofNat 96), (.negSucc 101), (.ofNat 102), (.negSucc 126)],
  [(.ofNat 110), (.negSucc 51), (.negSucc 85), (.negSucc 109), (.ofNat 35), (.ofNat 110), (.ofNat 101), (.ofNat 115), (.negSucc 115), (.negSucc 115), (.ofNat 110), (.negSucc 119), (.negSucc 58), (.ofNat 123), (.negSucc 67), (.negSucc 34)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
