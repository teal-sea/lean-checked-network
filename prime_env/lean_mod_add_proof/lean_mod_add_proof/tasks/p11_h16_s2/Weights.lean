import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.negSucc 123), (.ofNat 90), (.ofNat 117), (.ofNat 100), (.ofNat 62), (.negSucc 108), (.negSucc 80), (.negSucc 110), (.ofNat 79), (.negSucc 102), (.ofNat 85), (.ofNat 98), (.ofNat 106), (.ofNat 37), (.negSucc 108), (.negSucc 84)],
  [(.ofNat 97), (.negSucc 111), (.ofNat 101), (.ofNat 115), (.negSucc 91), (.negSucc 105), (.negSucc 103), (.negSucc 98), (.negSucc 82), (.ofNat 97), (.negSucc 85), (.negSucc 112), (.ofNat 88), (.ofNat 72), (.ofNat 87), (.ofNat 123)],
  [(.negSucc 23), (.negSucc 74), (.negSucc 114), (.ofNat 104), (.negSucc 31), (.ofNat 53), (.ofNat 95), (.ofNat 118), (.negSucc 107), (.ofNat 82), (.negSucc 121), (.ofNat 121), (.ofNat 33), (.negSucc 117), (.ofNat 101), (.ofNat 100)],
  [(.negSucc 111), (.ofNat 103), (.negSucc 113), (.ofNat 101), (.ofNat 85), (.ofNat 108), (.ofNat 91), (.ofNat 65), (.negSucc 54), (.negSucc 107), (.negSucc 112), (.negSucc 108), (.negSucc 110), (.ofNat 101), (.negSucc 108), (.ofNat 58)],
  [(.ofNat 116), (.ofNat 38), (.negSucc 108), (.ofNat 1), (.negSucc 105), (.ofNat 90), (.negSucc 109), (.negSucc 112), (.ofNat 122), (.negSucc 90), (.negSucc 107), (.ofNat 65), (.negSucc 126), (.negSucc 78), (.negSucc 78), (.negSucc 101)],
  [(.negSucc 81), (.negSucc 98), (.ofNat 123), (.negSucc 81), (.ofNat 103), (.negSucc 103), (.negSucc 82), (.ofNat 27), (.ofNat 94), (.ofNat 118), (.negSucc 66), (.negSucc 10), (.negSucc 112), (.negSucc 109), (.ofNat 113), (.negSucc 108)],
  [(.negSucc 58), (.ofNat 108), (.ofNat 113), (.negSucc 104), (.negSucc 102), (.negSucc 109), (.ofNat 123), (.ofNat 108), (.negSucc 5), (.ofNat 9), (.negSucc 62), (.negSucc 83), (.negSucc 111), (.ofNat 111), (.ofNat 88), (.ofNat 84)],
  [(.ofNat 117), (.ofNat 104), (.ofNat 72), (.negSucc 122), (.ofNat 104), (.negSucc 93), (.negSucc 27), (.negSucc 70), (.negSucc 126), (.negSucc 108), (.ofNat 71), (.ofNat 104), (.negSucc 89), (.negSucc 88), (.negSucc 110), (.ofNat 107)],
  [(.negSucc 104), (.negSucc 116), (.negSucc 123), (.negSucc 93), (.negSucc 113), (.ofNat 114), (.negSucc 112), (.negSucc 100), (.negSucc 92), (.ofNat 5), (.ofNat 112), (.negSucc 98), (.ofNat 69), (.negSucc 43), (.negSucc 35), (.ofNat 94)],
  [(.ofNat 10), (.negSucc 114), (.negSucc 104), (.negSucc 95), (.ofNat 103), (.ofNat 97), (.ofNat 70), (.ofNat 104), (.ofNat 56), (.ofNat 105), (.ofNat 112), (.ofNat 104), (.ofNat 98), (.ofNat 124), (.ofNat 91), (.negSucc 62)],
  [(.ofNat 59), (.ofNat 114), (.negSucc 29), (.ofNat 51), (.negSucc 120), (.ofNat 25), (.ofNat 100), (.ofNat 107), (.ofNat 117), (.negSucc 78), (.ofNat 91), (.negSucc 103), (.ofNat 120), (.negSucc 105), (.ofNat 0), (.negSucc 102)]]

def E2 : List (List Int) := [
  [(.negSucc 90), (.ofNat 76), (.ofNat 106), (.negSucc 109), (.negSucc 113), (.negSucc 70), (.negSucc 96), (.ofNat 116), (.ofNat 120), (.ofNat 108), (.negSucc 113), (.negSucc 54), (.negSucc 108), (.ofNat 88), (.negSucc 32), (.ofNat 38)],
  [(.negSucc 29), (.ofNat 104), (.ofNat 104), (.negSucc 99), (.ofNat 108), (.ofNat 103), (.negSucc 112), (.negSucc 124), (.ofNat 73), (.negSucc 90), (.ofNat 82), (.ofNat 45), (.negSucc 117), (.negSucc 124), (.ofNat 105), (.ofNat 106)],
  [(.ofNat 102), (.negSucc 111), (.negSucc 17), (.negSucc 108), (.negSucc 108), (.ofNat 125), (.ofNat 93), (.negSucc 92), (.negSucc 90), (.negSucc 102), (.ofNat 104), (.negSucc 97), (.negSucc 81), (.ofNat 95), (.negSucc 72), (.ofNat 108)],
  [(.negSucc 125), (.negSucc 114), (.negSucc 114), (.negSucc 100), (.ofNat 110), (.negSucc 12), (.ofNat 100), (.ofNat 127), (.negSucc 123), (.ofNat 81), (.ofNat 104), (.ofNat 110), (.ofNat 110), (.ofNat 3), (.negSucc 90), (.negSucc 44)],
  [(.ofNat 13), (.ofNat 90), (.negSucc 94), (.ofNat 95), (.negSucc 104), (.negSucc 112), (.negSucc 92), (.ofNat 92), (.ofNat 60), (.ofNat 95), (.ofNat 89), (.negSucc 103), (.ofNat 110), (.negSucc 113), (.ofNat 92), (.negSucc 116)],
  [(.ofNat 65), (.ofNat 88), (.ofNat 91), (.ofNat 116), (.ofNat 103), (.negSucc 112), (.negSucc 23), (.negSucc 110), (.ofNat 107), (.negSucc 104), (.ofNat 100), (.ofNat 103), (.ofNat 103), (.ofNat 107), (.ofNat 101), (.negSucc 69)],
  [(.negSucc 100), (.negSucc 101), (.ofNat 120), (.ofNat 106), (.negSucc 105), (.ofNat 67), (.ofNat 100), (.negSucc 100), (.ofNat 113), (.negSucc 100), (.negSucc 90), (.negSucc 122), (.ofNat 94), (.negSucc 74), (.negSucc 119), (.ofNat 92)],
  [(.ofNat 123), (.negSucc 69), (.ofNat 71), (.ofNat 103), (.negSucc 11), (.ofNat 117), (.negSucc 26), (.ofNat 119), (.negSucc 12), (.ofNat 104), (.negSucc 125), (.ofNat 122), (.ofNat 88), (.negSucc 65), (.negSucc 95), (.ofNat 118)],
  [(.negSucc 13), (.ofNat 113), (.negSucc 108), (.ofNat 116), (.ofNat 30), (.ofNat 61), (.negSucc 115), (.ofNat 99), (.negSucc 115), (.negSucc 10), (.negSucc 105), (.negSucc 106), (.negSucc 16), (.ofNat 115), (.ofNat 115), (.ofNat 42)],
  [(.negSucc 82), (.ofNat 86), (.negSucc 112), (.ofNat 12), (.negSucc 54), (.negSucc 104), (.ofNat 44), (.negSucc 113), (.negSucc 83), (.negSucc 115), (.negSucc 97), (.ofNat 101), (.negSucc 114), (.negSucc 116), (.ofNat 77), (.negSucc 110)],
  [(.ofNat 125), (.negSucc 109), (.ofNat 19), (.negSucc 121), (.ofNat 107), (.negSucc 119), (.ofNat 109), (.ofNat 28), (.ofNat 91), (.ofNat 45), (.negSucc 87), (.ofNat 13), (.negSucc 108), (.ofNat 25), (.negSucc 111), (.negSucc 106)]]

def W2 : List (List Int) := [
  [(.ofNat 87), (.ofNat 78), (.ofNat 64), (.negSucc 12), (.negSucc 97), (.ofNat 110), (.negSucc 90), (.negSucc 119), (.ofNat 87), (.negSucc 84), (.ofNat 94), (.negSucc 4), (.negSucc 92), (.ofNat 102), (.negSucc 34), (.negSucc 89)],
  [(.negSucc 43), (.ofNat 108), (.ofNat 106), (.negSucc 89), (.ofNat 100), (.negSucc 76), (.ofNat 104), (.negSucc 90), (.negSucc 81), (.ofNat 127), (.ofNat 106), (.ofNat 42), (.negSucc 50), (.negSucc 91), (.negSucc 99), (.negSucc 113)],
  [(.negSucc 100), (.negSucc 101), (.ofNat 12), (.negSucc 115), (.ofNat 21), (.negSucc 105), (.ofNat 55), (.ofNat 108), (.negSucc 106), (.ofNat 82), (.ofNat 79), (.negSucc 91), (.ofNat 93), (.negSucc 82), (.ofNat 117), (.ofNat 99)],
  [(.ofNat 99), (.ofNat 60), (.negSucc 92), (.negSucc 94), (.negSucc 1), (.negSucc 104), (.negSucc 98), (.negSucc 23), (.negSucc 27), (.negSucc 105), (.negSucc 43), (.ofNat 62), (.ofNat 98), (.ofNat 99), (.ofNat 91), (.ofNat 123)],
  [(.negSucc 87), (.ofNat 100), (.negSucc 121), (.negSucc 94), (.ofNat 53), (.ofNat 90), (.ofNat 75), (.negSucc 107), (.ofNat 90), (.ofNat 25), (.ofNat 7), (.negSucc 98), (.ofNat 112), (.negSucc 111), (.negSucc 96), (.ofNat 98)],
  [(.negSucc 108), (.negSucc 117), (.ofNat 62), (.negSucc 7), (.negSucc 70), (.ofNat 106), (.ofNat 89), (.ofNat 45), (.ofNat 95), (.ofNat 81), (.negSucc 105), (.ofNat 106), (.ofNat 98), (.negSucc 48), (.negSucc 96), (.negSucc 95)],
  [(.ofNat 103), (.negSucc 86), (.ofNat 99), (.ofNat 61), (.ofNat 95), (.negSucc 20), (.negSucc 107), (.ofNat 107), (.negSucc 74), (.negSucc 93), (.negSucc 96), (.negSucc 106), (.ofNat 78), (.ofNat 74), (.ofNat 54), (.negSucc 100)],
  [(.negSucc 84), (.ofNat 111), (.ofNat 110), (.ofNat 112), (.negSucc 90), (.negSucc 84), (.negSucc 83), (.negSucc 53), (.negSucc 85), (.negSucc 90), (.negSucc 99), (.ofNat 110), (.ofNat 69), (.negSucc 97), (.ofNat 86), (.ofNat 72)],
  [(.ofNat 92), (.ofNat 51), (.negSucc 51), (.ofNat 95), (.ofNat 101), (.negSucc 102), (.ofNat 100), (.negSucc 90), (.negSucc 100), (.ofNat 72), (.negSucc 65), (.negSucc 123), (.negSucc 25), (.ofNat 107), (.negSucc 92), (.ofNat 89)],
  [(.ofNat 70), (.negSucc 99), (.negSucc 105), (.ofNat 95), (.negSucc 110), (.ofNat 7), (.ofNat 63), (.ofNat 81), (.ofNat 87), (.ofNat 71), (.negSucc 57), (.ofNat 13), (.negSucc 114), (.ofNat 44), (.negSucc 42), (.ofNat 96)],
  [(.negSucc 91), (.negSucc 19), (.negSucc 41), (.ofNat 45), (.ofNat 107), (.ofNat 99), (.negSucc 95), (.ofNat 84), (.ofNat 101), (.negSucc 112), (.ofNat 38), (.negSucc 51), (.negSucc 95), (.negSucc 85), (.ofNat 102), (.negSucc 1)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
