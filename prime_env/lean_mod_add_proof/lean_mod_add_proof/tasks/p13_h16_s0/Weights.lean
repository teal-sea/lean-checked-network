import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 13

13 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=13 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 13

def E1 : List (List Int) := [
  [(.ofNat 115), (.ofNat 56), (.ofNat 3), (.negSucc 95), (.negSucc 98), (.ofNat 14), (.negSucc 49), (.ofNat 99), (.negSucc 91), (.negSucc 111), (.negSucc 58), (.ofNat 105), (.ofNat 103), (.negSucc 100), (.negSucc 98), (.negSucc 86)],
  [(.ofNat 86), (.ofNat 85), (.negSucc 115), (.negSucc 107), (.negSucc 99), (.negSucc 14), (.ofNat 42), (.negSucc 110), (.negSucc 107), (.ofNat 42), (.negSucc 126), (.ofNat 71), (.negSucc 107), (.ofNat 112), (.ofNat 91), (.ofNat 113)],
  [(.negSucc 53), (.negSucc 98), (.ofNat 70), (.negSucc 86), (.negSucc 97), (.ofNat 94), (.ofNat 110), (.negSucc 90), (.ofNat 73), (.ofNat 105), (.negSucc 117), (.negSucc 102), (.negSucc 95), (.negSucc 109), (.ofNat 108), (.negSucc 114)],
  [(.negSucc 109), (.ofNat 92), (.ofNat 74), (.negSucc 18), (.negSucc 79), (.negSucc 89), (.ofNat 112), (.ofNat 94), (.ofNat 105), (.ofNat 106), (.negSucc 100), (.negSucc 83), (.ofNat 107), (.ofNat 97), (.negSucc 88), (.negSucc 75)],
  [(.negSucc 94), (.negSucc 91), (.negSucc 102), (.ofNat 86), (.ofNat 37), (.ofNat 118), (.ofNat 109), (.ofNat 95), (.negSucc 3), (.negSucc 49), (.negSucc 90), (.ofNat 119), (.negSucc 15), (.negSucc 105), (.negSucc 101), (.ofNat 91)],
  [(.negSucc 11), (.negSucc 48), (.ofNat 66), (.ofNat 114), (.ofNat 125), (.negSucc 111), (.ofNat 111), (.negSucc 56), (.negSucc 100), (.negSucc 95), (.negSucc 89), (.ofNat 99), (.negSucc 98), (.ofNat 118), (.ofNat 87), (.negSucc 103)],
  [(.ofNat 98), (.ofNat 95), (.ofNat 125), (.ofNat 93), (.ofNat 107), (.ofNat 104), (.ofNat 94), (.negSucc 84), (.ofNat 6), (.negSucc 105), (.negSucc 22), (.negSucc 117), (.ofNat 105), (.negSucc 104), (.ofNat 93), (.ofNat 111)],
  [(.ofNat 104), (.negSucc 102), (.negSucc 97), (.ofNat 113), (.ofNat 103), (.negSucc 112), (.ofNat 2), (.ofNat 64), (.ofNat 111), (.negSucc 69), (.ofNat 112), (.negSucc 93), (.ofNat 121), (.ofNat 105), (.negSucc 62), (.negSucc 72)],
  [(.ofNat 55), (.ofNat 105), (.negSucc 95), (.ofNat 93), (.ofNat 92), (.ofNat 101), (.negSucc 99), (.ofNat 107), (.ofNat 76), (.ofNat 84), (.ofNat 118), (.ofNat 125), (.negSucc 105), (.ofNat 53), (.negSucc 98), (.negSucc 110)],
  [(.negSucc 66), (.ofNat 16), (.ofNat 113), (.ofNat 91), (.ofNat 105), (.negSucc 103), (.negSucc 98), (.ofNat 83), (.negSucc 103), (.ofNat 107), (.ofNat 113), (.ofNat 98), (.ofNat 123), (.negSucc 116), (.negSucc 121), (.ofNat 100)],
  [(.negSucc 116), (.negSucc 87), (.negSucc 93), (.negSucc 31), (.ofNat 85), (.ofNat 85), (.negSucc 108), (.negSucc 116), (.negSucc 114), (.ofNat 120), (.ofNat 89), (.negSucc 80), (.ofNat 91), (.ofNat 91), (.ofNat 90), (.negSucc 107)],
  [(.negSucc 72), (.ofNat 108), (.negSucc 122), (.negSucc 117), (.negSucc 89), (.negSucc 41), (.negSucc 113), (.negSucc 53), (.ofNat 97), (.negSucc 78), (.ofNat 94), (.negSucc 107), (.negSucc 111), (.negSucc 102), (.ofNat 117), (.ofNat 114)],
  [(.ofNat 57), (.negSucc 110), (.ofNat 96), (.negSucc 103), (.negSucc 116), (.ofNat 36), (.negSucc 105), (.ofNat 109), (.ofNat 104), (.negSucc 102), (.ofNat 66), (.negSucc 91), (.negSucc 101), (.ofNat 101), (.negSucc 96), (.ofNat 84)]]

def E2 : List (List Int) := [
  [(.ofNat 45), (.ofNat 96), (.negSucc 51), (.negSucc 81), (.ofNat 105), (.negSucc 107), (.negSucc 83), (.ofNat 47), (.ofNat 112), (.ofNat 89), (.negSucc 109), (.ofNat 74), (.negSucc 105), (.ofNat 92), (.ofNat 89), (.ofNat 26)],
  [(.negSucc 108), (.negSucc 70), (.ofNat 97), (.ofNat 77), (.ofNat 92), (.ofNat 96), (.negSucc 110), (.ofNat 93), (.ofNat 59), (.ofNat 100), (.negSucc 89), (.negSucc 95), (.ofNat 85), (.negSucc 99), (.ofNat 87), (.ofNat 86)],
  [(.negSucc 91), (.negSucc 106), (.negSucc 87), (.ofNat 89), (.ofNat 73), (.negSucc 98), (.negSucc 110), (.ofNat 92), (.negSucc 118), (.negSucc 4), (.negSucc 90), (.negSucc 91), (.ofNat 79), (.ofNat 56), (.negSucc 94), (.negSucc 107)],
  [(.negSucc 63), (.ofNat 127), (.negSucc 97), (.ofNat 93), (.negSucc 58), (.ofNat 106), (.negSucc 110), (.negSucc 105), (.negSucc 75), (.negSucc 82), (.negSucc 85), (.ofNat 109), (.negSucc 121), (.negSucc 55), (.negSucc 104), (.ofNat 94)],
  [(.ofNat 112), (.negSucc 96), (.ofNat 96), (.ofNat 103), (.negSucc 105), (.negSucc 97), (.negSucc 90), (.negSucc 94), (.ofNat 114), (.negSucc 109), (.ofNat 80), (.ofNat 108), (.negSucc 52), (.negSucc 17), (.ofNat 103), (.negSucc 26)],
  [(.ofNat 104), (.ofNat 84), (.negSucc 16), (.ofNat 106), (.negSucc 102), (.ofNat 83), (.negSucc 83), (.ofNat 99), (.ofNat 77), (.negSucc 53), (.ofNat 113), (.negSucc 99), (.ofNat 109), (.ofNat 18), (.ofNat 83), (.negSucc 82)],
  [(.ofNat 81), (.ofNat 57), (.negSucc 106), (.ofNat 100), (.negSucc 94), (.negSucc 78), (.negSucc 10), (.ofNat 91), (.negSucc 119), (.ofNat 83), (.ofNat 122), (.negSucc 89), (.negSucc 116), (.negSucc 82), (.negSucc 106), (.ofNat 104)],
  [(.negSucc 96), (.negSucc 121), (.ofNat 102), (.negSucc 51), (.negSucc 105), (.ofNat 66), (.ofNat 119), (.negSucc 113), (.negSucc 98), (.ofNat 103), (.ofNat 92), (.ofNat 52), (.negSucc 57), (.ofNat 93), (.negSucc 88), (.negSucc 95)],
  [(.negSucc 98), (.ofNat 94), (.ofNat 112), (.negSucc 98), (.negSucc 84), (.ofNat 87), (.ofNat 110), (.negSucc 92), (.ofNat 92), (.ofNat 77), (.ofNat 91), (.ofNat 90), (.ofNat 94), (.negSucc 91), (.ofNat 89), (.ofNat 64)],
  [(.negSucc 81), (.negSucc 89), (.negSucc 96), (.negSucc 95), (.negSucc 43), (.negSucc 103), (.ofNat 109), (.ofNat 118), (.ofNat 109), (.negSucc 55), (.ofNat 90), (.negSucc 12), (.negSucc 17), (.ofNat 110), (.ofNat 95), (.ofNat 35)],
  [(.ofNat 38), (.ofNat 84), (.ofNat 107), (.negSucc 90), (.ofNat 54), (.ofNat 119), (.ofNat 104), (.ofNat 92), (.negSucc 79), (.negSucc 95), (.ofNat 32), (.negSucc 104), (.negSucc 96), (.negSucc 106), (.negSucc 78), (.negSucc 108)],
  [(.ofNat 103), (.ofNat 90), (.ofNat 85), (.negSucc 94), (.ofNat 103), (.negSucc 108), (.ofNat 82), (.negSucc 16), (.negSucc 91), (.negSucc 87), (.negSucc 96), (.negSucc 47), (.ofNat 90), (.ofNat 96), (.negSucc 74), (.ofNat 90)],
  [(.ofNat 98), (.negSucc 110), (.negSucc 93), (.negSucc 104), (.ofNat 98), (.ofNat 107), (.ofNat 57), (.negSucc 89), (.ofNat 8), (.ofNat 9), (.negSucc 105), (.ofNat 104), (.ofNat 31), (.negSucc 113), (.negSucc 30), (.negSucc 62)]]

def W2 : List (List Int) := [
  [(.ofNat 78), (.ofNat 3), (.ofNat 96), (.ofNat 86), (.negSucc 115), (.negSucc 1), (.ofNat 124), (.ofNat 101), (.negSucc 91), (.negSucc 109), (.ofNat 28), (.ofNat 84), (.negSucc 104), (.negSucc 105), (.negSucc 92), (.negSucc 39)],
  [(.negSucc 92), (.ofNat 100), (.negSucc 75), (.negSucc 38), (.negSucc 89), (.negSucc 51), (.ofNat 98), (.ofNat 80), (.negSucc 97), (.ofNat 5), (.ofNat 54), (.negSucc 101), (.ofNat 120), (.ofNat 113), (.ofNat 90), (.negSucc 75)],
  [(.negSucc 99), (.negSucc 87), (.negSucc 105), (.negSucc 92), (.negSucc 78), (.ofNat 4), (.ofNat 100), (.negSucc 92), (.ofNat 99), (.ofNat 83), (.ofNat 120), (.negSucc 76), (.ofNat 94), (.negSucc 100), (.ofNat 91), (.ofNat 120)],
  [(.negSucc 84), (.ofNat 80), (.ofNat 90), (.negSucc 116), (.negSucc 19), (.ofNat 34), (.ofNat 20), (.negSucc 100), (.ofNat 99), (.ofNat 108), (.ofNat 105), (.ofNat 16), (.negSucc 103), (.negSucc 11), (.ofNat 8), (.negSucc 102)],
  [(.ofNat 26), (.negSucc 36), (.ofNat 66), (.negSucc 101), (.ofNat 74), (.negSucc 126), (.negSucc 85), (.ofNat 103), (.negSucc 27), (.ofNat 78), (.ofNat 100), (.ofNat 97), (.negSucc 90), (.ofNat 22), (.negSucc 93), (.ofNat 88)],
  [(.ofNat 111), (.negSucc 89), (.negSucc 104), (.negSucc 63), (.ofNat 108), (.ofNat 103), (.negSucc 101), (.ofNat 103), (.negSucc 101), (.negSucc 79), (.ofNat 71), (.negSucc 88), (.ofNat 96), (.negSucc 44), (.ofNat 31), (.ofNat 38)],
  [(.ofNat 89), (.ofNat 103), (.ofNat 111), (.negSucc 39), (.ofNat 119), (.negSucc 103), (.negSucc 115), (.ofNat 11), (.negSucc 21), (.negSucc 94), (.ofNat 16), (.negSucc 95), (.negSucc 112), (.ofNat 39), (.ofNat 114), (.negSucc 66)],
  [(.ofNat 27), (.negSucc 93), (.ofNat 90), (.ofNat 27), (.ofNat 80), (.ofNat 110), (.negSucc 103), (.negSucc 92), (.ofNat 112), (.negSucc 73), (.negSucc 71), (.ofNat 22), (.negSucc 65), (.negSucc 64), (.ofNat 36), (.ofNat 104)],
  [(.negSucc 110), (.ofNat 57), (.negSucc 91), (.ofNat 83), (.ofNat 82), (.negSucc 100), (.negSucc 91), (.ofNat 5), (.ofNat 98), (.ofNat 59), (.negSucc 101), (.ofNat 108), (.ofNat 96), (.ofNat 81), (.negSucc 98), (.negSucc 95)],
  [(.negSucc 95), (.ofNat 41), (.ofNat 1), (.ofNat 115), (.ofNat 78), (.ofNat 100), (.negSucc 65), (.ofNat 125), (.negSucc 102), (.ofNat 95), (.negSucc 95), (.ofNat 22), (.negSucc 16), (.negSucc 100), (.negSucc 43), (.ofNat 2)],
  [(.negSucc 3), (.negSucc 100), (.ofNat 99), (.ofNat 101), (.negSucc 11), (.negSucc 91), (.ofNat 11), (.ofNat 7), (.negSucc 84), (.ofNat 118), (.negSucc 104), (.negSucc 108), (.negSucc 89), (.ofNat 93), (.ofNat 82), (.ofNat 72)],
  [(.ofNat 109), (.ofNat 84), (.negSucc 77), (.ofNat 100), (.negSucc 101), (.ofNat 75), (.ofNat 68), (.negSucc 114), (.ofNat 80), (.negSucc 39), (.negSucc 92), (.negSucc 50), (.ofNat 117), (.negSucc 106), (.ofNat 55), (.negSucc 103)],
  [(.ofNat 96), (.negSucc 95), (.negSucc 110), (.ofNat 69), (.negSucc 107), (.negSucc 85), (.ofNat 111), (.negSucc 43), (.ofNat 94), (.negSucc 94), (.negSucc 56), (.ofNat 87), (.ofNat 51), (.ofNat 109), (.negSucc 93), (.ofNat 89)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 13 → ∀ b, b < 13 → answer a b = (a + b) % 13

end LeanCheckedNetwork.Net
