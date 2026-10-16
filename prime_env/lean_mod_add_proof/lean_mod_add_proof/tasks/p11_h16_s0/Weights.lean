import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.ofNat 41), (.negSucc 102), (.negSucc 98), (.ofNat 88), (.negSucc 63), (.negSucc 114), (.negSucc 114), (.ofNat 41), (.ofNat 122), (.negSucc 87), (.negSucc 97), (.ofNat 88), (.negSucc 35), (.ofNat 101), (.negSucc 120), (.ofNat 108)],
  [(.negSucc 83), (.ofNat 67), (.negSucc 99), (.negSucc 44), (.ofNat 84), (.negSucc 97), (.ofNat 124), (.ofNat 116), (.ofNat 110), (.ofNat 99), (.negSucc 109), (.negSucc 93), (.negSucc 108), (.negSucc 67), (.ofNat 102), (.ofNat 98)],
  [(.ofNat 107), (.ofNat 118), (.negSucc 112), (.negSucc 111), (.ofNat 85), (.ofNat 78), (.negSucc 103), (.ofNat 90), (.ofNat 114), (.ofNat 4), (.ofNat 103), (.ofNat 50), (.ofNat 108), (.negSucc 105), (.negSucc 71), (.ofNat 56)],
  [(.negSucc 107), (.ofNat 91), (.ofNat 88), (.negSucc 114), (.ofNat 103), (.ofNat 119), (.ofNat 97), (.negSucc 90), (.ofNat 109), (.negSucc 97), (.ofNat 69), (.negSucc 36), (.negSucc 97), (.ofNat 106), (.negSucc 95), (.negSucc 82)],
  [(.ofNat 114), (.negSucc 88), (.ofNat 111), (.negSucc 92), (.ofNat 113), (.ofNat 70), (.negSucc 92), (.negSucc 107), (.ofNat 49), (.ofNat 100), (.negSucc 115), (.negSucc 107), (.negSucc 74), (.negSucc 103), (.ofNat 117), (.negSucc 93)],
  [(.negSucc 109), (.negSucc 121), (.ofNat 111), (.negSucc 70), (.ofNat 106), (.negSucc 102), (.ofNat 90), (.negSucc 97), (.negSucc 62), (.ofNat 108), (.negSucc 48), (.ofNat 93), (.ofNat 106), (.ofNat 20), (.negSucc 103), (.negSucc 117)],
  [(.ofNat 102), (.negSucc 79), (.ofNat 99), (.ofNat 17), (.negSucc 88), (.negSucc 106), (.negSucc 59), (.ofNat 109), (.negSucc 96), (.negSucc 106), (.ofNat 113), (.negSucc 110), (.negSucc 100), (.ofNat 120), (.ofNat 17), (.negSucc 96)],
  [(.negSucc 103), (.ofNat 120), (.ofNat 112), (.ofNat 114), (.negSucc 103), (.negSucc 45), (.ofNat 25), (.ofNat 105), (.negSucc 112), (.negSucc 90), (.ofNat 15), (.ofNat 116), (.ofNat 108), (.negSucc 109), (.ofNat 115), (.negSucc 98)],
  [(.ofNat 80), (.ofNat 106), (.ofNat 22), (.ofNat 104), (.negSucc 89), (.ofNat 121), (.ofNat 54), (.ofNat 61), (.negSucc 104), (.ofNat 127), (.negSucc 102), (.negSucc 104), (.ofNat 109), (.ofNat 67), (.negSucc 102), (.negSucc 50)],
  [(.negSucc 75), (.ofNat 63), (.negSucc 118), (.ofNat 112), (.negSucc 101), (.ofNat 109), (.negSucc 110), (.negSucc 121), (.negSucc 87), (.ofNat 75), (.ofNat 82), (.ofNat 113), (.negSucc 117), (.ofNat 68), (.ofNat 100), (.ofNat 99)],
  [(.ofNat 58), (.negSucc 105), (.negSucc 109), (.ofNat 95), (.negSucc 105), (.ofNat 27), (.ofNat 120), (.negSucc 106), (.ofNat 97), (.negSucc 123), (.ofNat 107), (.negSucc 103), (.ofNat 94), (.negSucc 111), (.ofNat 31), (.ofNat 98)]]

def E2 : List (List Int) := [
  [(.negSucc 112), (.ofNat 111), (.negSucc 82), (.negSucc 96), (.ofNat 112), (.negSucc 28), (.ofNat 115), (.ofNat 96), (.ofNat 119), (.negSucc 101), (.ofNat 99), (.negSucc 56), (.ofNat 103), (.negSucc 110), (.negSucc 23), (.negSucc 112)],
  [(.ofNat 127), (.ofNat 96), (.negSucc 23), (.negSucc 100), (.ofNat 90), (.ofNat 114), (.negSucc 107), (.ofNat 18), (.ofNat 111), (.ofNat 79), (.negSucc 123), (.negSucc 14), (.ofNat 52), (.ofNat 89), (.negSucc 120), (.negSucc 123)],
  [(.negSucc 117), (.negSucc 58), (.ofNat 111), (.negSucc 107), (.ofNat 95), (.ofNat 101), (.ofNat 104), (.negSucc 123), (.ofNat 78), (.ofNat 110), (.negSucc 77), (.ofNat 51), (.negSucc 113), (.negSucc 41), (.ofNat 112), (.negSucc 100)],
  [(.ofNat 113), (.negSucc 114), (.ofNat 125), (.negSucc 100), (.ofNat 62), (.negSucc 41), (.negSucc 95), (.negSucc 93), (.negSucc 105), (.negSucc 72), (.ofNat 111), (.negSucc 86), (.ofNat 110), (.negSucc 112), (.negSucc 71), (.negSucc 87)],
  [(.negSucc 104), (.negSucc 86), (.ofNat 111), (.negSucc 94), (.negSucc 113), (.negSucc 120), (.ofNat 57), (.ofNat 85), (.negSucc 109), (.negSucc 96), (.ofNat 19), (.ofNat 106), (.negSucc 97), (.ofNat 116), (.negSucc 101), (.negSucc 103)],
  [(.ofNat 96), (.ofNat 69), (.ofNat 94), (.ofNat 24), (.negSucc 109), (.negSucc 86), (.ofNat 50), (.ofNat 107), (.negSucc 97), (.ofNat 105), (.negSucc 112), (.negSucc 110), (.negSucc 62), (.negSucc 97), (.ofNat 113), (.ofNat 5)],
  [(.negSucc 93), (.ofNat 119), (.ofNat 66), (.ofNat 111), (.negSucc 107), (.ofNat 98), (.negSucc 88), (.ofNat 90), (.negSucc 100), (.ofNat 89), (.ofNat 20), (.ofNat 119), (.ofNat 121), (.ofNat 10), (.negSucc 99), (.ofNat 122)],
  [(.ofNat 90), (.ofNat 83), (.ofNat 1), (.ofNat 108), (.negSucc 64), (.ofNat 107), (.ofNat 119), (.negSucc 111), (.negSucc 98), (.negSucc 125), (.ofNat 98), (.negSucc 102), (.negSucc 103), (.ofNat 111), (.negSucc 11), (.ofNat 106)],
  [(.negSucc 97), (.negSucc 125), (.negSucc 108), (.ofNat 105), (.negSucc 77), (.ofNat 92), (.negSucc 118), (.negSucc 111), (.ofNat 78), (.negSucc 52), (.negSucc 100), (.ofNat 109), (.ofNat 59), (.negSucc 115), (.ofNat 122), (.ofNat 104)],
  [(.negSucc 27), (.negSucc 101), (.negSucc 118), (.ofNat 112), (.ofNat 51), (.negSucc 119), (.ofNat 104), (.negSucc 51), (.ofNat 118), (.ofNat 107), (.negSucc 99), (.negSucc 97), (.ofNat 91), (.ofNat 82), (.negSucc 106), (.ofNat 54)],
  [(.ofNat 105), (.negSucc 3), (.negSucc 108), (.ofNat 61), (.ofNat 107), (.negSucc 108), (.negSucc 112), (.ofNat 113), (.ofNat 104), (.ofNat 8), (.ofNat 123), (.ofNat 61), (.negSucc 115), (.ofNat 95), (.ofNat 80), (.ofNat 87)]]

def W2 : List (List Int) := [
  [(.ofNat 88), (.negSucc 111), (.ofNat 93), (.negSucc 104), (.negSucc 92), (.ofNat 58), (.negSucc 118), (.ofNat 79), (.ofNat 117), (.ofNat 42), (.negSucc 111), (.ofNat 66), (.ofNat 69), (.negSucc 109), (.ofNat 72), (.negSucc 102)],
  [(.negSucc 10), (.negSucc 68), (.ofNat 25), (.negSucc 93), (.ofNat 46), (.negSucc 71), (.ofNat 115), (.ofNat 115), (.ofNat 92), (.negSucc 115), (.ofNat 42), (.negSucc 87), (.negSucc 110), (.ofNat 65), (.ofNat 77), (.negSucc 93)],
  [(.ofNat 2), (.ofNat 106), (.negSucc 106), (.negSucc 64), (.ofNat 65), (.negSucc 116), (.negSucc 110), (.ofNat 15), (.ofNat 96), (.negSucc 23), (.ofNat 107), (.ofNat 115), (.ofNat 87), (.ofNat 14), (.negSucc 111), (.negSucc 103)],
  [(.ofNat 40), (.ofNat 109), (.negSucc 121), (.ofNat 5), (.ofNat 87), (.negSucc 47), (.ofNat 88), (.negSucc 95), (.ofNat 47), (.ofNat 112), (.negSucc 89), (.negSucc 112), (.ofNat 37), (.negSucc 101), (.ofNat 83), (.negSucc 94)],
  [(.ofNat 3), (.ofNat 13), (.negSucc 103), (.ofNat 112), (.ofNat 111), (.ofNat 114), (.negSucc 79), (.negSucc 104), (.negSucc 53), (.negSucc 13), (.negSucc 87), (.ofNat 117), (.negSucc 114), (.ofNat 111), (.negSucc 8), (.negSucc 37)],
  [(.ofNat 81), (.negSucc 103), (.negSucc 91), (.ofNat 103), (.ofNat 64), (.ofNat 96), (.ofNat 25), (.ofNat 24), (.negSucc 113), (.negSucc 107), (.ofNat 104), (.negSucc 99), (.ofNat 107), (.negSucc 44), (.negSucc 98), (.ofNat 46)],
  [(.negSucc 121), (.negSucc 103), (.negSucc 40), (.ofNat 92), (.negSucc 27), (.negSucc 32), (.negSucc 10), (.ofNat 117), (.negSucc 115), (.ofNat 61), (.ofNat 71), (.ofNat 96), (.negSucc 75), (.negSucc 96), (.ofNat 121), (.ofNat 89)],
  [(.ofNat 123), (.ofNat 19), (.ofNat 25), (.ofNat 100), (.negSucc 98), (.negSucc 115), (.negSucc 24), (.ofNat 90), (.negSucc 96), (.ofNat 98), (.negSucc 120), (.negSucc 88), (.negSucc 73), (.ofNat 121), (.negSucc 77), (.ofNat 103)],
  [(.negSucc 107), (.ofNat 121), (.ofNat 120), (.ofNat 0), (.negSucc 94), (.negSucc 88), (.ofNat 71), (.negSucc 47), (.negSucc 98), (.negSucc 97), (.negSucc 7), (.ofNat 59), (.ofNat 127), (.negSucc 94), (.negSucc 31), (.ofNat 107)],
  [(.ofNat 106), (.ofNat 60), (.ofNat 122), (.negSucc 94), (.negSucc 100), (.ofNat 46), (.negSucc 117), (.negSucc 113), (.negSucc 56), (.negSucc 66), (.ofNat 121), (.ofNat 28), (.negSucc 100), (.ofNat 3), (.ofNat 102), (.ofNat 54)],
  [(.negSucc 89), (.negSucc 88), (.ofNat 83), (.negSucc 104), (.negSucc 82), (.ofNat 116), (.ofNat 116), (.negSucc 79), (.ofNat 11), (.ofNat 112), (.negSucc 15), (.negSucc 75), (.ofNat 5), (.ofNat 99), (.negSucc 102), (.ofNat 70)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
