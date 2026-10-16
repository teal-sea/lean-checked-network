import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 13

13 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=13 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 13

def E1 : List (List Int) := [
  [(.negSucc 97), (.negSucc 108), (.negSucc 103), (.negSucc 95), (.ofNat 114), (.ofNat 72), (.negSucc 70), (.negSucc 25), (.negSucc 100), (.negSucc 113), (.ofNat 97), (.negSucc 36), (.ofNat 97), (.ofNat 108), (.negSucc 91), (.ofNat 106)],
  [(.negSucc 106), (.negSucc 81), (.ofNat 25), (.ofNat 102), (.negSucc 106), (.negSucc 59), (.negSucc 99), (.negSucc 113), (.negSucc 83), (.negSucc 30), (.negSucc 112), (.ofNat 96), (.negSucc 93), (.ofNat 19), (.ofNat 102), (.ofNat 95)],
  [(.ofNat 102), (.ofNat 105), (.ofNat 82), (.negSucc 18), (.ofNat 104), (.negSucc 114), (.ofNat 108), (.negSucc 2), (.negSucc 70), (.ofNat 105), (.ofNat 68), (.negSucc 117), (.negSucc 13), (.negSucc 102), (.negSucc 85), (.negSucc 105)],
  [(.ofNat 97), (.ofNat 118), (.negSucc 116), (.negSucc 96), (.negSucc 111), (.negSucc 97), (.negSucc 93), (.ofNat 110), (.negSucc 63), (.ofNat 39), (.ofNat 88), (.ofNat 111), (.ofNat 108), (.negSucc 34), (.negSucc 19), (.ofNat 105)],
  [(.negSucc 97), (.ofNat 89), (.negSucc 76), (.ofNat 117), (.ofNat 113), (.ofNat 13), (.ofNat 102), (.ofNat 43), (.ofNat 103), (.negSucc 111), (.negSucc 105), (.negSucc 90), (.ofNat 80), (.ofNat 111), (.ofNat 14), (.ofNat 93)],
  [(.negSucc 91), (.ofNat 4), (.ofNat 101), (.ofNat 91), (.negSucc 96), (.ofNat 105), (.ofNat 91), (.negSucc 100), (.ofNat 104), (.negSucc 67), (.ofNat 6), (.ofNat 105), (.negSucc 82), (.ofNat 52), (.negSucc 108), (.negSucc 112)],
  [(.ofNat 34), (.negSucc 99), (.negSucc 11), (.negSucc 84), (.ofNat 86), (.ofNat 99), (.negSucc 94), (.negSucc 72), (.ofNat 107), (.negSucc 31), (.ofNat 104), (.negSucc 104), (.negSucc 94), (.negSucc 126), (.ofNat 101), (.negSucc 20)],
  [(.ofNat 102), (.negSucc 96), (.negSucc 88), (.ofNat 54), (.negSucc 64), (.negSucc 1), (.ofNat 117), (.ofNat 110), (.ofNat 104), (.ofNat 93), (.negSucc 110), (.ofNat 106), (.ofNat 93), (.negSucc 99), (.negSucc 69), (.ofNat 107)],
  [(.ofNat 97), (.negSucc 70), (.ofNat 117), (.ofNat 89), (.ofNat 5), (.negSucc 99), (.negSucc 99), (.ofNat 102), (.ofNat 97), (.negSucc 95), (.negSucc 88), (.negSucc 89), (.ofNat 107), (.ofNat 124), (.negSucc 38), (.negSucc 113)],
  [(.negSucc 106), (.ofNat 112), (.ofNat 28), (.negSucc 108), (.negSucc 31), (.negSucc 101), (.ofNat 30), (.negSucc 74), (.ofNat 97), (.negSucc 114), (.ofNat 122), (.ofNat 74), (.negSucc 60), (.ofNat 87), (.ofNat 109), (.negSucc 87)],
  [(.negSucc 109), (.ofNat 108), (.negSucc 93), (.negSucc 97), (.negSucc 50), (.negSucc 31), (.ofNat 114), (.negSucc 108), (.negSucc 43), (.ofNat 49), (.negSucc 50), (.negSucc 77), (.negSucc 104), (.negSucc 109), (.negSucc 102), (.ofNat 109)],
  [(.ofNat 108), (.ofNat 74), (.ofNat 109), (.ofNat 93), (.ofNat 86), (.ofNat 106), (.negSucc 111), (.ofNat 40), (.negSucc 113), (.ofNat 113), (.negSucc 103), (.ofNat 82), (.negSucc 55), (.negSucc 98), (.ofNat 82), (.ofNat 26)],
  [(.ofNat 104), (.negSucc 86), (.ofNat 91), (.negSucc 39), (.negSucc 66), (.ofNat 109), (.ofNat 91), (.ofNat 126), (.negSucc 109), (.negSucc 8), (.ofNat 97), (.negSucc 66), (.ofNat 92), (.ofNat 74), (.negSucc 17), (.negSucc 91)]]

def E2 : List (List Int) := [
  [(.negSucc 91), (.negSucc 87), (.ofNat 106), (.ofNat 112), (.ofNat 113), (.negSucc 100), (.ofNat 34), (.ofNat 88), (.ofNat 99), (.negSucc 79), (.ofNat 10), (.ofNat 19), (.negSucc 120), (.negSucc 102), (.negSucc 90), (.negSucc 99)],
  [(.negSucc 101), (.ofNat 57), (.negSucc 25), (.negSucc 86), (.negSucc 102), (.negSucc 97), (.negSucc 77), (.ofNat 43), (.ofNat 101), (.ofNat 91), (.negSucc 110), (.ofNat 85), (.ofNat 98), (.negSucc 71), (.ofNat 122), (.negSucc 93)],
  [(.ofNat 23), (.ofNat 97), (.negSucc 98), (.negSucc 95), (.ofNat 96), (.negSucc 103), (.ofNat 106), (.negSucc 86), (.ofNat 52), (.ofNat 103), (.ofNat 77), (.negSucc 81), (.ofNat 94), (.ofNat 90), (.negSucc 115), (.ofNat 99)],
  [(.ofNat 97), (.ofNat 97), (.ofNat 94), (.ofNat 87), (.negSucc 83), (.ofNat 86), (.negSucc 124), (.negSucc 87), (.negSucc 87), (.negSucc 96), (.ofNat 97), (.ofNat 108), (.negSucc 102), (.ofNat 97), (.negSucc 74), (.ofNat 49)],
  [(.ofNat 89), (.negSucc 78), (.ofNat 53), (.negSucc 38), (.ofNat 98), (.ofNat 98), (.ofNat 40), (.ofNat 93), (.negSucc 88), (.negSucc 108), (.negSucc 99), (.negSucc 113), (.negSucc 102), (.negSucc 77), (.ofNat 92), (.negSucc 99)],
  [(.negSucc 91), (.negSucc 92), (.negSucc 104), (.negSucc 105), (.negSucc 81), (.ofNat 97), (.ofNat 67), (.ofNat 98), (.negSucc 86), (.ofNat 19), (.ofNat 24), (.ofNat 116), (.ofNat 108), (.negSucc 96), (.negSucc 114), (.ofNat 103)],
  [(.negSucc 90), (.negSucc 102), (.ofNat 45), (.ofNat 85), (.ofNat 47), (.ofNat 97), (.negSucc 98), (.negSucc 80), (.negSucc 97), (.ofNat 114), (.ofNat 101), (.negSucc 105), (.ofNat 85), (.ofNat 78), (.ofNat 104), (.ofNat 88)],
  [(.ofNat 99), (.negSucc 26), (.ofNat 98), (.negSucc 3), (.negSucc 20), (.negSucc 94), (.ofNat 115), (.negSucc 126), (.negSucc 101), (.negSucc 32), (.negSucc 84), (.ofNat 96), (.negSucc 114), (.ofNat 103), (.ofNat 62), (.negSucc 96)],
  [(.ofNat 119), (.ofNat 93), (.negSucc 98), (.negSucc 99), (.negSucc 4), (.negSucc 96), (.negSucc 72), (.ofNat 88), (.negSucc 91), (.negSucc 97), (.negSucc 49), (.negSucc 92), (.negSucc 83), (.negSucc 38), (.negSucc 79), (.ofNat 91)],
  [(.negSucc 78), (.ofNat 101), (.ofNat 13), (.ofNat 96), (.ofNat 68), (.negSucc 79), (.negSucc 55), (.ofNat 120), (.negSucc 10), (.ofNat 38), (.ofNat 102), (.ofNat 99), (.ofNat 117), (.negSucc 100), (.ofNat 116), (.ofNat 99)],
  [(.negSucc 120), (.ofNat 32), (.ofNat 97), (.ofNat 93), (.negSucc 73), (.ofNat 85), (.ofNat 92), (.negSucc 92), (.ofNat 98), (.ofNat 106), (.negSucc 36), (.negSucc 75), (.ofNat 95), (.ofNat 25), (.negSucc 113), (.negSucc 105)],
  [(.ofNat 82), (.negSucc 62), (.negSucc 88), (.negSucc 92), (.ofNat 108), (.ofNat 100), (.negSucc 94), (.negSucc 92), (.ofNat 97), (.ofNat 97), (.negSucc 112), (.ofNat 83), (.ofNat 88), (.ofNat 106), (.negSucc 87), (.negSucc 10)],
  [(.ofNat 104), (.negSucc 94), (.negSucc 81), (.negSucc 0), (.negSucc 117), (.ofNat 96), (.ofNat 79), (.ofNat 57), (.ofNat 98), (.negSucc 108), (.ofNat 104), (.negSucc 62), (.negSucc 96), (.ofNat 56), (.ofNat 88), (.ofNat 98)]]

def W2 : List (List Int) := [
  [(.negSucc 17), (.ofNat 92), (.negSucc 80), (.negSucc 49), (.ofNat 110), (.negSucc 101), (.negSucc 101), (.ofNat 52), (.negSucc 85), (.ofNat 106), (.negSucc 96), (.negSucc 105), (.ofNat 110), (.negSucc 97), (.ofNat 119), (.ofNat 97)],
  [(.ofNat 97), (.ofNat 64), (.ofNat 32), (.ofNat 104), (.negSucc 98), (.negSucc 81), (.ofNat 102), (.negSucc 95), (.negSucc 71), (.negSucc 110), (.ofNat 76), (.ofNat 113), (.ofNat 96), (.negSucc 40), (.negSucc 96), (.negSucc 98)],
  [(.ofNat 71), (.negSucc 110), (.ofNat 98), (.negSucc 70), (.ofNat 101), (.ofNat 20), (.negSucc 69), (.negSucc 52), (.negSucc 17), (.negSucc 96), (.ofNat 122), (.negSucc 88), (.negSucc 115), (.ofNat 88), (.ofNat 95), (.ofNat 90)],
  [(.negSucc 39), (.negSucc 92), (.negSucc 90), (.negSucc 123), (.negSucc 100), (.ofNat 113), (.negSucc 30), (.ofNat 103), (.ofNat 44), (.ofNat 118), (.negSucc 75), (.ofNat 87), (.negSucc 95), (.ofNat 86), (.ofNat 3), (.ofNat 99)],
  [(.negSucc 82), (.negSucc 2), (.negSucc 114), (.ofNat 103), (.ofNat 101), (.ofNat 97), (.ofNat 104), (.ofNat 41), (.ofNat 110), (.ofNat 84), (.negSucc 120), (.negSucc 55), (.ofNat 64), (.negSucc 107), (.negSucc 50), (.negSucc 109)],
  [(.ofNat 22), (.ofNat 119), (.ofNat 103), (.negSucc 29), (.negSucc 95), (.negSucc 60), (.negSucc 100), (.negSucc 115), (.ofNat 95), (.negSucc 90), (.ofNat 107), (.ofNat 15), (.ofNat 75), (.negSucc 87), (.ofNat 89), (.ofNat 33)],
  [(.ofNat 98), (.ofNat 95), (.negSucc 65), (.negSucc 107), (.ofNat 84), (.negSucc 124), (.ofNat 74), (.negSucc 87), (.ofNat 104), (.negSucc 98), (.negSucc 21), (.ofNat 9), (.negSucc 55), (.ofNat 101), (.negSucc 87), (.ofNat 102)],
  [(.ofNat 35), (.ofNat 86), (.negSucc 103), (.ofNat 88), (.negSucc 81), (.negSucc 105), (.negSucc 36), (.ofNat 127), (.ofNat 100), (.ofNat 73), (.negSucc 108), (.negSucc 23), (.negSucc 100), (.ofNat 105), (.ofNat 102), (.negSucc 106)],
  [(.negSucc 108), (.negSucc 105), (.ofNat 103), (.ofNat 66), (.ofNat 40), (.negSucc 13), (.negSucc 95), (.ofNat 103), (.ofNat 57), (.ofNat 109), (.ofNat 105), (.ofNat 29), (.negSucc 32), (.negSucc 118), (.ofNat 48), (.negSucc 57)],
  [(.ofNat 49), (.negSucc 101), (.ofNat 41), (.negSucc 94), (.ofNat 50), (.ofNat 72), (.ofNat 104), (.negSucc 95), (.negSucc 23), (.ofNat 46), (.ofNat 78), (.negSucc 91), (.ofNat 102), (.negSucc 99), (.negSucc 100), (.ofNat 100)],
  [(.ofNat 107), (.negSucc 49), (.negSucc 92), (.ofNat 16), (.ofNat 9), (.ofNat 103), (.negSucc 119), (.negSucc 100), (.ofNat 2), (.negSucc 96), (.negSucc 106), (.ofNat 94), (.ofNat 59), (.ofNat 44), (.ofNat 95), (.ofNat 23)],
  [(.ofNat 52), (.ofNat 71), (.ofNat 84), (.ofNat 93), (.ofNat 96), (.ofNat 3), (.ofNat 96), (.ofNat 63), (.negSucc 114), (.negSucc 97), (.ofNat 63), (.negSucc 114), (.negSucc 93), (.ofNat 101), (.negSucc 97), (.negSucc 100)],
  [(.negSucc 94), (.ofNat 103), (.ofNat 95), (.negSucc 87), (.negSucc 111), (.negSucc 110), (.ofNat 53), (.ofNat 57), (.negSucc 103), (.ofNat 21), (.ofNat 114), (.ofNat 119), (.negSucc 85), (.negSucc 33), (.negSucc 3), (.ofNat 100)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 13 → ∀ b, b < 13 → answer a b = (a + b) % 13

end LeanCheckedNetwork.Net
