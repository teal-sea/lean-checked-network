import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 19

19 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=19 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 19

def E1 : List (List Int) := [
  [(.ofNat 118), (.ofNat 89), (.negSucc 99), (.negSucc 88), (.negSucc 89), (.negSucc 60), (.ofNat 30), (.ofNat 98), (.ofNat 12), (.negSucc 68), (.negSucc 92), (.ofNat 116), (.negSucc 89), (.ofNat 106), (.ofNat 103), (.negSucc 93)],
  [(.negSucc 11), (.ofNat 85), (.negSucc 39), (.ofNat 76), (.ofNat 95), (.negSucc 102), (.ofNat 62), (.ofNat 91), (.negSucc 90), (.negSucc 102), (.ofNat 86), (.negSucc 103), (.ofNat 110), (.ofNat 74), (.ofNat 104), (.negSucc 81)],
  [(.negSucc 120), (.ofNat 6), (.ofNat 99), (.ofNat 126), (.ofNat 52), (.negSucc 84), (.ofNat 98), (.negSucc 83), (.negSucc 101), (.ofNat 91), (.ofNat 108), (.ofNat 102), (.negSucc 87), (.negSucc 67), (.negSucc 64), (.negSucc 79)],
  [(.ofNat 3), (.negSucc 110), (.ofNat 120), (.ofNat 94), (.negSucc 95), (.ofNat 39), (.ofNat 95), (.ofNat 54), (.ofNat 98), (.ofNat 116), (.negSucc 46), (.negSucc 92), (.ofNat 89), (.negSucc 101), (.negSucc 92), (.ofNat 76)],
  [(.ofNat 121), (.negSucc 96), (.negSucc 72), (.negSucc 61), (.ofNat 96), (.ofNat 107), (.ofNat 90), (.ofNat 105), (.ofNat 108), (.negSucc 79), (.negSucc 102), (.ofNat 87), (.ofNat 43), (.negSucc 89), (.negSucc 27), (.ofNat 87)],
  [(.negSucc 39), (.negSucc 96), (.negSucc 103), (.negSucc 116), (.ofNat 87), (.ofNat 99), (.ofNat 108), (.negSucc 94), (.negSucc 97), (.negSucc 97), (.negSucc 50), (.negSucc 91), (.negSucc 102), (.negSucc 12), (.ofNat 112), (.ofNat 108)],
  [(.negSucc 105), (.negSucc 77), (.ofNat 86), (.negSucc 102), (.negSucc 100), (.ofNat 65), (.ofNat 104), (.ofNat 63), (.negSucc 105), (.ofNat 88), (.ofNat 101), (.ofNat 87), (.ofNat 103), (.ofNat 110), (.ofNat 97), (.ofNat 121)],
  [(.ofNat 67), (.ofNat 70), (.ofNat 101), (.negSucc 49), (.ofNat 70), (.negSucc 115), (.ofNat 97), (.ofNat 105), (.negSucc 45), (.ofNat 76), (.ofNat 111), (.negSucc 56), (.negSucc 98), (.ofNat 96), (.negSucc 92), (.ofNat 98)],
  [(.ofNat 114), (.ofNat 127), (.ofNat 88), (.ofNat 121), (.ofNat 94), (.negSucc 85), (.ofNat 75), (.negSucc 73), (.ofNat 101), (.negSucc 93), (.negSucc 56), (.ofNat 87), (.ofNat 112), (.ofNat 19), (.negSucc 103), (.ofNat 90)],
  [(.negSucc 92), (.ofNat 107), (.negSucc 100), (.ofNat 103), (.negSucc 115), (.negSucc 57), (.ofNat 44), (.negSucc 84), (.ofNat 63), (.negSucc 40), (.negSucc 95), (.negSucc 47), (.negSucc 60), (.negSucc 116), (.ofNat 68), (.ofNat 98)],
  [(.negSucc 116), (.ofNat 83), (.negSucc 115), (.ofNat 65), (.ofNat 52), (.ofNat 101), (.negSucc 19), (.ofNat 106), (.negSucc 98), (.ofNat 95), (.ofNat 68), (.ofNat 88), (.negSucc 36), (.negSucc 106), (.ofNat 94), (.ofNat 75)],
  [(.ofNat 101), (.ofNat 53), (.ofNat 97), (.negSucc 119), (.ofNat 100), (.ofNat 111), (.negSucc 100), (.negSucc 112), (.negSucc 104), (.negSucc 3), (.ofNat 114), (.ofNat 51), (.ofNat 75), (.negSucc 57), (.ofNat 72), (.ofNat 93)],
  [(.ofNat 117), (.negSucc 69), (.ofNat 97), (.negSucc 92), (.negSucc 107), (.ofNat 83), (.negSucc 95), (.negSucc 110), (.ofNat 85), (.negSucc 90), (.ofNat 91), (.negSucc 91), (.negSucc 78), (.ofNat 124), (.negSucc 98), (.ofNat 2)],
  [(.negSucc 88), (.negSucc 107), (.negSucc 13), (.negSucc 66), (.negSucc 42), (.negSucc 94), (.negSucc 97), (.ofNat 89), (.ofNat 96), (.ofNat 29), (.negSucc 92), (.ofNat 67), (.ofNat 113), (.ofNat 109), (.negSucc 105), (.negSucc 47)],
  [(.negSucc 92), (.negSucc 95), (.negSucc 92), (.ofNat 90), (.ofNat 83), (.negSucc 89), (.negSucc 94), (.ofNat 7), (.ofNat 23), (.ofNat 97), (.negSucc 97), (.negSucc 113), (.negSucc 98), (.ofNat 55), (.ofNat 87), (.negSucc 93)],
  [(.ofNat 104), (.negSucc 89), (.negSucc 105), (.ofNat 104), (.negSucc 76), (.negSucc 76), (.negSucc 106), (.negSucc 103), (.negSucc 86), (.negSucc 55), (.ofNat 60), (.ofNat 109), (.ofNat 84), (.negSucc 102), (.ofNat 92), (.negSucc 108)],
  [(.ofNat 79), (.negSucc 28), (.ofNat 88), (.ofNat 86), (.negSucc 67), (.ofNat 84), (.negSucc 96), (.ofNat 88), (.negSucc 103), (.negSucc 108), (.ofNat 94), (.negSucc 116), (.negSucc 28), (.negSucc 112), (.negSucc 49), (.negSucc 92)],
  [(.negSucc 113), (.ofNat 65), (.ofNat 112), (.negSucc 78), (.ofNat 103), (.ofNat 101), (.negSucc 92), (.ofNat 48), (.ofNat 86), (.ofNat 49), (.ofNat 36), (.ofNat 95), (.negSucc 69), (.negSucc 85), (.negSucc 98), (.negSucc 91)],
  [(.negSucc 40), (.ofNat 111), (.negSucc 55), (.negSucc 104), (.ofNat 20), (.ofNat 87), (.negSucc 13), (.negSucc 95), (.ofNat 116), (.ofNat 108), (.negSucc 101), (.negSucc 99), (.ofNat 78), (.ofNat 96), (.negSucc 78), (.negSucc 85)]]

def E2 : List (List Int) := [
  [(.negSucc 105), (.negSucc 77), (.negSucc 85), (.negSucc 102), (.negSucc 100), (.ofNat 65), (.ofNat 104), (.ofNat 63), (.ofNat 106), (.negSucc 87), (.ofNat 101), (.ofNat 87), (.ofNat 103), (.ofNat 110), (.ofNat 97), (.ofNat 121)],
  [(.ofNat 67), (.ofNat 70), (.negSucc 100), (.negSucc 49), (.ofNat 70), (.negSucc 115), (.ofNat 97), (.ofNat 105), (.ofNat 46), (.negSucc 75), (.ofNat 111), (.negSucc 56), (.negSucc 98), (.ofNat 96), (.negSucc 92), (.ofNat 98)],
  [(.ofNat 114), (.ofNat 127), (.negSucc 87), (.ofNat 121), (.ofNat 94), (.negSucc 85), (.ofNat 75), (.negSucc 73), (.negSucc 100), (.ofNat 94), (.negSucc 56), (.ofNat 87), (.ofNat 112), (.ofNat 19), (.negSucc 103), (.ofNat 90)],
  [(.negSucc 92), (.ofNat 107), (.ofNat 101), (.ofNat 103), (.negSucc 115), (.negSucc 57), (.ofNat 44), (.negSucc 84), (.negSucc 62), (.ofNat 41), (.negSucc 95), (.negSucc 47), (.negSucc 60), (.negSucc 116), (.ofNat 68), (.ofNat 98)],
  [(.negSucc 116), (.ofNat 83), (.ofNat 116), (.ofNat 65), (.ofNat 52), (.ofNat 101), (.negSucc 19), (.ofNat 106), (.ofNat 99), (.negSucc 94), (.ofNat 68), (.ofNat 88), (.negSucc 36), (.negSucc 106), (.ofNat 94), (.ofNat 75)],
  [(.ofNat 101), (.ofNat 53), (.negSucc 96), (.negSucc 119), (.ofNat 100), (.ofNat 111), (.negSucc 100), (.negSucc 112), (.ofNat 105), (.ofNat 4), (.ofNat 114), (.ofNat 51), (.ofNat 75), (.negSucc 57), (.ofNat 72), (.ofNat 93)],
  [(.ofNat 117), (.negSucc 69), (.negSucc 96), (.negSucc 92), (.negSucc 107), (.ofNat 83), (.negSucc 95), (.negSucc 110), (.negSucc 84), (.ofNat 91), (.ofNat 91), (.negSucc 91), (.negSucc 78), (.ofNat 124), (.negSucc 98), (.ofNat 2)],
  [(.negSucc 88), (.negSucc 107), (.ofNat 14), (.negSucc 66), (.negSucc 42), (.negSucc 94), (.negSucc 97), (.ofNat 89), (.negSucc 95), (.negSucc 28), (.negSucc 92), (.ofNat 67), (.ofNat 113), (.ofNat 109), (.negSucc 105), (.negSucc 47)],
  [(.negSucc 92), (.negSucc 95), (.ofNat 93), (.ofNat 90), (.ofNat 83), (.negSucc 89), (.negSucc 94), (.ofNat 7), (.negSucc 22), (.negSucc 96), (.negSucc 97), (.negSucc 113), (.negSucc 98), (.ofNat 55), (.ofNat 87), (.negSucc 93)],
  [(.ofNat 104), (.negSucc 89), (.ofNat 106), (.ofNat 104), (.negSucc 76), (.negSucc 76), (.negSucc 106), (.negSucc 103), (.ofNat 87), (.ofNat 56), (.ofNat 60), (.ofNat 109), (.ofNat 84), (.negSucc 102), (.ofNat 92), (.negSucc 108)],
  [(.ofNat 79), (.negSucc 28), (.negSucc 87), (.ofNat 86), (.negSucc 67), (.ofNat 84), (.negSucc 96), (.ofNat 88), (.ofNat 104), (.ofNat 109), (.ofNat 94), (.negSucc 116), (.negSucc 28), (.negSucc 112), (.negSucc 49), (.negSucc 92)],
  [(.negSucc 113), (.ofNat 65), (.negSucc 111), (.negSucc 78), (.ofNat 103), (.ofNat 101), (.negSucc 92), (.ofNat 48), (.negSucc 85), (.negSucc 48), (.ofNat 36), (.ofNat 95), (.negSucc 69), (.negSucc 85), (.negSucc 98), (.negSucc 91)],
  [(.negSucc 40), (.ofNat 111), (.ofNat 56), (.negSucc 104), (.ofNat 20), (.ofNat 87), (.negSucc 13), (.negSucc 95), (.negSucc 115), (.negSucc 107), (.negSucc 101), (.negSucc 99), (.ofNat 78), (.ofNat 96), (.negSucc 78), (.negSucc 85)],
  [(.ofNat 118), (.ofNat 89), (.ofNat 100), (.negSucc 88), (.negSucc 89), (.negSucc 60), (.ofNat 30), (.ofNat 98), (.negSucc 11), (.ofNat 69), (.negSucc 92), (.ofNat 116), (.negSucc 89), (.ofNat 106), (.ofNat 103), (.negSucc 93)],
  [(.negSucc 11), (.ofNat 85), (.ofNat 40), (.ofNat 76), (.ofNat 95), (.negSucc 102), (.ofNat 62), (.ofNat 91), (.ofNat 91), (.ofNat 103), (.ofNat 86), (.negSucc 103), (.ofNat 110), (.ofNat 74), (.ofNat 104), (.negSucc 81)],
  [(.negSucc 120), (.ofNat 6), (.negSucc 98), (.ofNat 126), (.ofNat 52), (.negSucc 84), (.ofNat 98), (.negSucc 83), (.ofNat 102), (.negSucc 90), (.ofNat 108), (.ofNat 102), (.negSucc 87), (.negSucc 67), (.negSucc 64), (.negSucc 79)],
  [(.ofNat 3), (.negSucc 110), (.negSucc 119), (.ofNat 94), (.negSucc 95), (.ofNat 39), (.ofNat 95), (.ofNat 54), (.negSucc 97), (.negSucc 115), (.negSucc 46), (.negSucc 92), (.ofNat 89), (.negSucc 101), (.negSucc 92), (.ofNat 76)],
  [(.ofNat 121), (.negSucc 96), (.ofNat 73), (.negSucc 61), (.ofNat 96), (.ofNat 107), (.ofNat 90), (.ofNat 105), (.negSucc 107), (.ofNat 80), (.negSucc 102), (.ofNat 87), (.ofNat 43), (.negSucc 89), (.negSucc 27), (.ofNat 87)],
  [(.negSucc 39), (.negSucc 96), (.ofNat 104), (.negSucc 116), (.ofNat 87), (.ofNat 99), (.ofNat 108), (.negSucc 94), (.ofNat 98), (.ofNat 98), (.negSucc 50), (.negSucc 91), (.negSucc 102), (.negSucc 12), (.ofNat 112), (.ofNat 108)]]

def W2 : List (List Int) := [
  [(.negSucc 103), (.ofNat 37), (.ofNat 61), (.ofNat 14), (.ofNat 101), (.negSucc 98), (.ofNat 108), (.negSucc 103), (.negSucc 18), (.negSucc 60), (.negSucc 118), (.ofNat 85), (.negSucc 91), (.ofNat 109), (.ofNat 104), (.negSucc 99)],
  [(.ofNat 30), (.ofNat 43), (.ofNat 82), (.negSucc 108), (.negSucc 123), (.negSucc 57), (.ofNat 98), (.ofNat 81), (.negSucc 106), (.ofNat 90), (.negSucc 14), (.negSucc 78), (.ofNat 118), (.ofNat 118), (.negSucc 60), (.negSucc 78)],
  [(.ofNat 95), (.ofNat 114), (.ofNat 23), (.negSucc 103), (.negSucc 55), (.ofNat 42), (.ofNat 105), (.ofNat 11), (.negSucc 15), (.ofNat 22), (.ofNat 81), (.ofNat 45), (.negSucc 106), (.ofNat 3), (.negSucc 102), (.negSucc 74)],
  [(.negSucc 12), (.ofNat 105), (.negSucc 96), (.negSucc 72), (.ofNat 94), (.ofNat 109), (.ofNat 89), (.negSucc 111), (.ofNat 109), (.negSucc 120), (.ofNat 60), (.ofNat 21), (.ofNat 42), (.negSucc 91), (.negSucc 79), (.negSucc 57)],
  [(.negSucc 112), (.ofNat 83), (.negSucc 112), (.ofNat 52), (.negSucc 114), (.ofNat 86), (.ofNat 97), (.ofNat 91), (.ofNat 81), (.ofNat 8), (.negSucc 89), (.ofNat 14), (.negSucc 48), (.negSucc 111), (.ofNat 100), (.negSucc 9)],
  [(.ofNat 92), (.ofNat 38), (.ofNat 43), (.ofNat 127), (.negSucc 83), (.negSucc 95), (.ofNat 74), (.ofNat 88), (.negSucc 90), (.ofNat 112), (.negSucc 113), (.negSucc 19), (.negSucc 63), (.negSucc 14), (.ofNat 24), (.ofNat 2)],
  [(.ofNat 22), (.negSucc 100), (.ofNat 115), (.ofNat 44), (.ofNat 107), (.negSucc 112), (.ofNat 51), (.negSucc 107), (.negSucc 119), (.negSucc 76), (.ofNat 92), (.negSucc 73), (.ofNat 117), (.ofNat 62), (.negSucc 39), (.ofNat 6)],
  [(.negSucc 80), (.negSucc 103), (.ofNat 38), (.negSucc 40), (.negSucc 5), (.negSucc 61), (.ofNat 25), (.ofNat 86), (.ofNat 79), (.negSucc 113), (.ofNat 111), (.ofNat 49), (.negSucc 102), (.ofNat 117), (.negSucc 110), (.ofNat 79)],
  [(.negSucc 62), (.negSucc 95), (.negSucc 101), (.negSucc 109), (.negSucc 75), (.ofNat 57), (.negSucc 32), (.ofNat 103), (.ofNat 94), (.ofNat 61), (.ofNat 4), (.negSucc 44), (.ofNat 114), (.ofNat 69), (.negSucc 44), (.ofNat 118)],
  [(.ofNat 87), (.negSucc 68), (.negSucc 72), (.negSucc 55), (.ofNat 81), (.ofNat 123), (.negSucc 39), (.negSucc 90), (.ofNat 50), (.ofNat 97), (.negSucc 96), (.ofNat 38), (.negSucc 93), (.negSucc 72), (.ofNat 64), (.ofNat 90)],
  [(.ofNat 72), (.ofNat 78), (.ofNat 105), (.negSucc 7), (.negSucc 26), (.ofNat 89), (.negSucc 113), (.ofNat 34), (.negSucc 100), (.negSucc 73), (.negSucc 96), (.negSucc 99), (.ofNat 90), (.negSucc 107), (.ofNat 69), (.ofNat 106)],
  [(.negSucc 97), (.ofNat 69), (.ofNat 99), (.ofNat 120), (.negSucc 96), (.negSucc 71), (.negSucc 102), (.ofNat 93), (.negSucc 86), (.negSucc 125), (.ofNat 88), (.ofNat 54), (.ofNat 51), (.negSucc 75), (.negSucc 82), (.ofNat 87)],
  [(.negSucc 24), (.ofNat 109), (.negSucc 28), (.ofNat 90), (.ofNat 95), (.negSucc 118), (.negSucc 100), (.negSucc 86), (.ofNat 69), (.ofNat 79), (.ofNat 84), (.negSucc 103), (.negSucc 42), (.ofNat 26), (.negSucc 110), (.ofNat 84)],
  [(.ofNat 103), (.ofNat 72), (.negSucc 108), (.negSucc 46), (.ofNat 0), (.negSucc 92), (.negSucc 100), (.negSucc 57), (.ofNat 81), (.ofNat 57), (.negSucc 61), (.ofNat 65), (.ofNat 59), (.ofNat 111), (.negSucc 21), (.ofNat 17)],
  [(.ofNat 62), (.ofNat 102), (.negSucc 13), (.negSucc 112), (.negSucc 87), (.ofNat 33), (.negSucc 88), (.ofNat 111), (.ofNat 33), (.negSucc 101), (.negSucc 101), (.negSucc 119), (.negSucc 108), (.ofNat 89), (.ofNat 119), (.ofNat 52)],
  [(.negSucc 110), (.negSucc 105), (.ofNat 94), (.negSucc 94), (.ofNat 103), (.ofNat 99), (.negSucc 80), (.negSucc 22), (.negSucc 85), (.negSucc 30), (.negSucc 36), (.ofNat 124), (.ofNat 94), (.ofNat 29), (.ofNat 29), (.ofNat 4)],
  [(.ofNat 69), (.negSucc 105), (.ofNat 76), (.ofNat 43), (.ofNat 98), (.ofNat 101), (.negSucc 14), (.negSucc 17), (.negSucc 54), (.ofNat 97), (.ofNat 101), (.negSucc 104), (.negSucc 30), (.negSucc 120), (.negSucc 92), (.negSucc 52)],
  [(.ofNat 117), (.negSucc 105), (.negSucc 87), (.ofNat 59), (.negSucc 114), (.ofNat 27), (.negSucc 14), (.ofNat 75), (.ofNat 57), (.ofNat 87), (.ofNat 28), (.ofNat 99), (.ofNat 38), (.negSucc 89), (.negSucc 90), (.negSucc 94)],
  [(.ofNat 32), (.negSucc 89), (.negSucc 101), (.ofNat 102), (.ofNat 96), (.negSucc 103), (.ofNat 78), (.ofNat 19), (.ofNat 113), (.negSucc 126), (.negSucc 80), (.negSucc 79), (.ofNat 79), (.ofNat 41), (.ofNat 80), (.negSucc 114)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 19 → ∀ b, b < 19 → answer a b = (a + b) % 19

end LeanCheckedNetwork.Net
