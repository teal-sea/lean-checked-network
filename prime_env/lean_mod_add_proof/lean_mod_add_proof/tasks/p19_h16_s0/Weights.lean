import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 19

19 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=19 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 19

def E1 : List (List Int) := [
  [(.ofNat 100), (.ofNat 89), (.ofNat 67), (.ofNat 112), (.negSucc 109), (.ofNat 54), (.ofNat 89), (.negSucc 1), (.ofNat 88), (.ofNat 101), (.ofNat 84), (.ofNat 111), (.negSucc 78), (.negSucc 24), (.ofNat 13), (.negSucc 116)],
  [(.ofNat 30), (.negSucc 90), (.ofNat 107), (.negSucc 92), (.negSucc 73), (.negSucc 95), (.ofNat 49), (.ofNat 109), (.ofNat 99), (.ofNat 110), (.negSucc 108), (.ofNat 103), (.negSucc 104), (.ofNat 81), (.negSucc 96), (.negSucc 83)],
  [(.negSucc 65), (.negSucc 102), (.ofNat 103), (.negSucc 35), (.ofNat 111), (.ofNat 97), (.negSucc 102), (.ofNat 97), (.ofNat 86), (.ofNat 115), (.negSucc 96), (.ofNat 78), (.ofNat 85), (.ofNat 76), (.ofNat 100), (.ofNat 40)],
  [(.negSucc 104), (.negSucc 104), (.ofNat 100), (.ofNat 83), (.negSucc 47), (.negSucc 78), (.ofNat 85), (.negSucc 30), (.ofNat 109), (.ofNat 98), (.ofNat 114), (.ofNat 44), (.ofNat 103), (.ofNat 82), (.ofNat 80), (.ofNat 114)],
  [(.negSucc 96), (.ofNat 68), (.ofNat 18), (.negSucc 78), (.negSucc 101), (.negSucc 78), (.ofNat 104), (.negSucc 101), (.ofNat 127), (.ofNat 35), (.ofNat 60), (.negSucc 113), (.negSucc 85), (.ofNat 88), (.negSucc 96), (.ofNat 83)],
  [(.negSucc 70), (.ofNat 102), (.ofNat 31), (.ofNat 89), (.ofNat 7), (.ofNat 98), (.negSucc 96), (.negSucc 96), (.ofNat 109), (.negSucc 83), (.negSucc 120), (.negSucc 111), (.negSucc 92), (.ofNat 95), (.ofNat 116), (.ofNat 74)],
  [(.negSucc 12), (.ofNat 97), (.negSucc 117), (.negSucc 108), (.ofNat 101), (.negSucc 103), (.ofNat 81), (.negSucc 74), (.ofNat 91), (.negSucc 90), (.ofNat 11), (.negSucc 99), (.ofNat 101), (.ofNat 99), (.ofNat 96), (.negSucc 112)],
  [(.ofNat 75), (.ofNat 32), (.negSucc 107), (.ofNat 79), (.negSucc 89), (.ofNat 39), (.ofNat 104), (.ofNat 113), (.ofNat 53), (.negSucc 95), (.ofNat 107), (.negSucc 77), (.ofNat 66), (.ofNat 102), (.negSucc 106), (.negSucc 87)],
  [(.ofNat 106), (.negSucc 109), (.negSucc 82), (.negSucc 58), (.negSucc 89), (.ofNat 97), (.negSucc 101), (.ofNat 98), (.negSucc 50), (.negSucc 112), (.ofNat 44), (.ofNat 64), (.negSucc 111), (.ofNat 117), (.ofNat 52), (.negSucc 80)],
  [(.ofNat 104), (.negSucc 107), (.negSucc 9), (.negSucc 66), (.ofNat 110), (.negSucc 103), (.negSucc 9), (.ofNat 37), (.negSucc 82), (.negSucc 98), (.negSucc 116), (.ofNat 109), (.negSucc 81), (.ofNat 67), (.ofNat 100), (.ofNat 115)],
  [(.ofNat 93), (.negSucc 48), (.ofNat 83), (.ofNat 81), (.ofNat 97), (.ofNat 97), (.ofNat 108), (.negSucc 80), (.negSucc 80), (.negSucc 103), (.ofNat 68), (.ofNat 101), (.ofNat 104), (.ofNat 43), (.negSucc 95), (.ofNat 98)],
  [(.negSucc 58), (.ofNat 103), (.ofNat 116), (.negSucc 102), (.negSucc 99), (.ofNat 2), (.negSucc 84), (.negSucc 100), (.negSucc 103), (.negSucc 106), (.ofNat 106), (.ofNat 102), (.negSucc 4), (.negSucc 102), (.negSucc 28), (.ofNat 105)],
  [(.negSucc 112), (.ofNat 96), (.ofNat 88), (.ofNat 114), (.negSucc 80), (.negSucc 103), (.negSucc 31), (.negSucc 74), (.negSucc 104), (.negSucc 91), (.negSucc 51), (.ofNat 57), (.negSucc 107), (.negSucc 84), (.ofNat 96), (.negSucc 94)],
  [(.negSucc 107), (.ofNat 55), (.ofNat 81), (.negSucc 116), (.ofNat 98), (.ofNat 94), (.ofNat 95), (.ofNat 50), (.negSucc 107), (.negSucc 77), (.negSucc 95), (.negSucc 67), (.negSucc 43), (.negSucc 88), (.negSucc 109), (.negSucc 87)],
  [(.negSucc 101), (.negSucc 97), (.ofNat 56), (.ofNat 58), (.ofNat 69), (.negSucc 86), (.negSucc 56), (.ofNat 102), (.negSucc 125), (.ofNat 19), (.ofNat 70), (.negSucc 106), (.ofNat 111), (.negSucc 89), (.negSucc 74), (.negSucc 103)],
  [(.negSucc 64), (.negSucc 98), (.negSucc 97), (.ofNat 30), (.negSucc 117), (.negSucc 6), (.negSucc 105), (.ofNat 90), (.negSucc 74), (.ofNat 68), (.ofNat 96), (.negSucc 106), (.negSucc 74), (.negSucc 96), (.ofNat 110), (.ofNat 87)],
  [(.ofNat 57), (.negSucc 70), (.negSucc 113), (.negSucc 89), (.negSucc 69), (.ofNat 103), (.ofNat 106), (.negSucc 84), (.negSucc 77), (.ofNat 67), (.negSucc 88), (.negSucc 85), (.negSucc 112), (.negSucc 100), (.negSucc 61), (.ofNat 105)],
  [(.ofNat 103), (.ofNat 98), (.negSucc 95), (.ofNat 97), (.ofNat 111), (.negSucc 92), (.negSucc 5), (.negSucc 121), (.negSucc 5), (.ofNat 102), (.negSucc 92), (.negSucc 1), (.ofNat 51), (.negSucc 109), (.negSucc 90), (.ofNat 102)],
  [(.ofNat 108), (.ofNat 111), (.negSucc 56), (.negSucc 94), (.ofNat 30), (.ofNat 86), (.negSucc 104), (.negSucc 84), (.ofNat 50), (.ofNat 100), (.ofNat 90), (.ofNat 71), (.ofNat 96), (.negSucc 93), (.ofNat 112), (.negSucc 35)]]

def E2 : List (List Int) := [
  [(.negSucc 80), (.ofNat 98), (.negSucc 1), (.ofNat 99), (.negSucc 119), (.ofNat 64), (.negSucc 84), (.negSucc 95), (.negSucc 86), (.negSucc 70), (.ofNat 87), (.negSucc 115), (.negSucc 102), (.ofNat 98), (.ofNat 16), (.ofNat 94)],
  [(.negSucc 27), (.ofNat 97), (.negSucc 91), (.negSucc 103), (.negSucc 67), (.negSucc 115), (.ofNat 28), (.negSucc 82), (.negSucc 80), (.negSucc 95), (.negSucc 99), (.negSucc 93), (.negSucc 107), (.ofNat 80), (.ofNat 99), (.negSucc 126)],
  [(.ofNat 73), (.ofNat 30), (.negSucc 109), (.ofNat 108), (.ofNat 100), (.ofNat 99), (.ofNat 100), (.ofNat 106), (.negSucc 55), (.negSucc 92), (.negSucc 81), (.negSucc 64), (.ofNat 89), (.ofNat 108), (.negSucc 116), (.negSucc 86)],
  [(.ofNat 118), (.negSucc 100), (.negSucc 97), (.negSucc 92), (.negSucc 47), (.negSucc 52), (.negSucc 79), (.ofNat 107), (.ofNat 66), (.negSucc 106), (.ofNat 118), (.negSucc 29), (.ofNat 99), (.ofNat 114), (.negSucc 65), (.negSucc 94)],
  [(.ofNat 104), (.negSucc 103), (.ofNat 30), (.negSucc 79), (.negSucc 105), (.negSucc 75), (.negSucc 94), (.ofNat 60), (.ofNat 89), (.negSucc 107), (.ofNat 54), (.ofNat 99), (.negSucc 90), (.ofNat 84), (.ofNat 111), (.ofNat 104)],
  [(.ofNat 84), (.negSucc 88), (.ofNat 76), (.ofNat 81), (.negSucc 3), (.ofNat 104), (.ofNat 105), (.negSucc 89), (.ofNat 82), (.negSucc 101), (.negSucc 98), (.ofNat 105), (.negSucc 84), (.ofNat 48), (.negSucc 85), (.ofNat 105)],
  [(.ofNat 49), (.ofNat 98), (.ofNat 99), (.negSucc 101), (.ofNat 104), (.negSucc 104), (.negSucc 55), (.negSucc 102), (.ofNat 98), (.negSucc 105), (.ofNat 45), (.ofNat 97), (.ofNat 99), (.negSucc 94), (.negSucc 86), (.ofNat 95)],
  [(.negSucc 80), (.ofNat 102), (.ofNat 103), (.ofNat 90), (.negSucc 78), (.ofNat 64), (.negSucc 88), (.negSucc 77), (.ofNat 102), (.negSucc 99), (.ofNat 116), (.ofNat 76), (.ofNat 73), (.negSucc 87), (.ofNat 107), (.negSucc 63)],
  [(.negSucc 102), (.ofNat 83), (.ofNat 88), (.negSucc 107), (.negSucc 90), (.ofNat 96), (.ofNat 99), (.ofNat 68), (.ofNat 100), (.negSucc 96), (.ofNat 39), (.negSucc 53), (.negSucc 97), (.negSucc 86), (.negSucc 61), (.negSucc 112)],
  [(.negSucc 98), (.negSucc 85), (.ofNat 67), (.ofNat 105), (.ofNat 64), (.negSucc 101), (.ofNat 15), (.ofNat 111), (.ofNat 115), (.ofNat 19), (.negSucc 103), (.negSucc 103), (.negSucc 87), (.negSucc 100), (.negSucc 87), (.negSucc 83)],
  [(.negSucc 72), (.negSucc 93), (.negSucc 68), (.ofNat 19), (.ofNat 96), (.ofNat 90), (.negSucc 102), (.ofNat 101), (.ofNat 105), (.ofNat 57), (.ofNat 39), (.negSucc 105), (.ofNat 106), (.negSucc 91), (.ofNat 111), (.ofNat 55)],
  [(.ofNat 47), (.negSucc 101), (.negSucc 117), (.negSucc 63), (.negSucc 94), (.negSucc 10), (.ofNat 90), (.negSucc 81), (.ofNat 47), (.ofNat 86), (.ofNat 111), (.negSucc 93), (.ofNat 68), (.negSucc 93), (.ofNat 54), (.ofNat 120)],
  [(.ofNat 114), (.ofNat 15), (.negSucc 91), (.ofNat 99), (.negSucc 77), (.negSucc 108), (.ofNat 59), (.negSucc 108), (.negSucc 59), (.ofNat 99), (.negSucc 87), (.negSucc 76), (.negSucc 111), (.negSucc 95), (.negSucc 99), (.ofNat 88)],
  [(.ofNat 109), (.ofNat 95), (.negSucc 75), (.negSucc 81), (.ofNat 95), (.ofNat 103), (.negSucc 96), (.negSucc 95), (.negSucc 48), (.ofNat 100), (.negSucc 96), (.ofNat 82), (.negSucc 40), (.negSucc 63), (.ofNat 93), (.negSucc 38)],
  [(.ofNat 91), (.ofNat 92), (.ofNat 27), (.ofNat 109), (.ofNat 60), (.negSucc 79), (.ofNat 78), (.negSucc 60), (.negSucc 102), (.ofNat 95), (.ofNat 79), (.ofNat 102), (.ofNat 110), (.ofNat 13), (.ofNat 93), (.negSucc 107)],
  [(.ofNat 67), (.ofNat 9), (.ofNat 103), (.negSucc 86), (.negSucc 119), (.negSucc 14), (.ofNat 94), (.ofNat 108), (.negSucc 99), (.ofNat 98), (.ofNat 93), (.ofNat 104), (.negSucc 61), (.ofNat 58), (.negSucc 104), (.negSucc 77)],
  [(.negSucc 61), (.negSucc 90), (.ofNat 106), (.ofNat 57), (.negSucc 65), (.ofNat 108), (.negSucc 104), (.ofNat 97), (.negSucc 100), (.ofNat 97), (.negSucc 97), (.ofNat 94), (.negSucc 102), (.ofNat 63), (.ofNat 98), (.negSucc 62)],
  [(.negSucc 103), (.negSucc 102), (.ofNat 108), (.ofNat 98), (.ofNat 115), (.negSucc 97), (.ofNat 52), (.negSucc 0), (.negSucc 93), (.ofNat 103), (.negSucc 99), (.ofNat 11), (.negSucc 30), (.ofNat 88), (.ofNat 94), (.ofNat 117)],
  [(.negSucc 104), (.negSucc 36), (.ofNat 56), (.negSucc 94), (.ofNat 41), (.ofNat 87), (.ofNat 101), (.negSucc 91), (.negSucc 98), (.ofNat 70), (.ofNat 92), (.negSucc 87), (.ofNat 97), (.ofNat 87), (.negSucc 105), (.ofNat 89)]]

def W2 : List (List Int) := [
  [(.negSucc 15), (.ofNat 115), (.ofNat 88), (.ofNat 107), (.ofNat 123), (.negSucc 84), (.negSucc 7), (.negSucc 14), (.negSucc 108), (.negSucc 24), (.ofNat 4), (.negSucc 101), (.negSucc 53), (.negSucc 37), (.ofNat 97), (.negSucc 86)],
  [(.ofNat 96), (.ofNat 82), (.ofNat 92), (.negSucc 84), (.ofNat 59), (.ofNat 63), (.negSucc 108), (.negSucc 109), (.negSucc 119), (.negSucc 101), (.negSucc 99), (.negSucc 111), (.ofNat 114), (.ofNat 94), (.ofNat 6), (.ofNat 68)],
  [(.ofNat 116), (.negSucc 95), (.negSucc 72), (.ofNat 39), (.negSucc 103), (.ofNat 116), (.ofNat 100), (.negSucc 84), (.negSucc 119), (.negSucc 84), (.ofNat 81), (.negSucc 78), (.ofNat 47), (.ofNat 72), (.negSucc 88), (.ofNat 106)],
  [(.ofNat 109), (.negSucc 113), (.negSucc 108), (.ofNat 38), (.ofNat 18), (.negSucc 109), (.negSucc 21), (.negSucc 4), (.negSucc 86), (.negSucc 96), (.ofNat 106), (.negSucc 6), (.negSucc 102), (.ofNat 77), (.ofNat 118), (.ofNat 98)],
  [(.ofNat 94), (.negSucc 50), (.negSucc 113), (.negSucc 72), (.ofNat 121), (.ofNat 92), (.negSucc 112), (.ofNat 127), (.negSucc 6), (.negSucc 105), (.negSucc 61), (.ofNat 42), (.negSucc 55), (.ofNat 86), (.ofNat 52), (.negSucc 47)],
  [(.negSucc 31), (.ofNat 12), (.negSucc 90), (.ofNat 117), (.negSucc 49), (.ofNat 20), (.ofNat 97), (.ofNat 45), (.negSucc 10), (.negSucc 109), (.negSucc 95), (.ofNat 109), (.ofNat 106), (.ofNat 96), (.negSucc 97), (.negSucc 106)],
  [(.negSucc 79), (.ofNat 122), (.negSucc 12), (.negSucc 109), (.negSucc 93), (.negSucc 101), (.ofNat 35), (.negSucc 29), (.ofNat 35), (.negSucc 98), (.ofNat 87), (.ofNat 114), (.negSucc 11), (.ofNat 110), (.ofNat 67), (.negSucc 98)],
  [(.negSucc 112), (.ofNat 37), (.ofNat 50), (.ofNat 76), (.ofNat 27), (.ofNat 110), (.negSucc 98), (.negSucc 107), (.negSucc 16), (.negSucc 108), (.ofNat 75), (.ofNat 98), (.negSucc 108), (.ofNat 95), (.ofNat 25), (.ofNat 4)],
  [(.negSucc 102), (.negSucc 6), (.ofNat 54), (.negSucc 44), (.ofNat 114), (.negSucc 45), (.ofNat 100), (.negSucc 99), (.ofNat 109), (.ofNat 10), (.negSucc 110), (.ofNat 27), (.negSucc 45), (.ofNat 115), (.negSucc 109), (.ofNat 62)],
  [(.negSucc 60), (.negSucc 116), (.ofNat 113), (.negSucc 36), (.negSucc 102), (.negSucc 37), (.ofNat 53), (.negSucc 17), (.ofNat 80), (.ofNat 35), (.negSucc 81), (.negSucc 89), (.ofNat 113), (.ofNat 19), (.ofNat 41), (.ofNat 108)],
  [(.ofNat 17), (.negSucc 95), (.ofNat 52), (.negSucc 9), (.negSucc 86), (.ofNat 63), (.negSucc 99), (.ofNat 86), (.ofNat 96), (.ofNat 51), (.ofNat 106), (.negSucc 100), (.negSucc 76), (.ofNat 25), (.ofNat 63), (.negSucc 35)],
  [(.ofNat 105), (.ofNat 3), (.ofNat 4), (.negSucc 106), (.ofNat 60), (.negSucc 104), (.ofNat 82), (.ofNat 117), (.ofNat 111), (.ofNat 93), (.ofNat 17), (.negSucc 100), (.negSucc 94), (.negSucc 29), (.negSucc 120), (.negSucc 82)],
  [(.ofNat 107), (.ofNat 114), (.negSucc 102), (.ofNat 64), (.ofNat 83), (.ofNat 36), (.ofNat 101), (.negSucc 28), (.ofNat 51), (.ofNat 49), (.negSucc 107), (.negSucc 86), (.negSucc 23), (.negSucc 57), (.negSucc 32), (.negSucc 108)],
  [(.ofNat 89), (.ofNat 102), (.negSucc 106), (.negSucc 106), (.negSucc 95), (.ofNat 55), (.negSucc 87), (.negSucc 108), (.ofNat 74), (.ofNat 110), (.negSucc 58), (.negSucc 12), (.ofNat 105), (.negSucc 84), (.ofNat 71), (.negSucc 45)],
  [(.ofNat 26), (.ofNat 52), (.negSucc 99), (.ofNat 74), (.negSucc 76), (.negSucc 93), (.ofNat 46), (.negSucc 97), (.ofNat 60), (.ofNat 108), (.ofNat 114), (.ofNat 86), (.negSucc 54), (.negSucc 88), (.negSucc 108), (.ofNat 43)],
  [(.negSucc 62), (.negSucc 94), (.negSucc 90), (.negSucc 16), (.ofNat 110), (.ofNat 98), (.ofNat 112), (.negSucc 56), (.negSucc 23), (.ofNat 52), (.negSucc 10), (.ofNat 118), (.negSucc 101), (.negSucc 94), (.negSucc 40), (.ofNat 102)],
  [(.negSucc 109), (.negSucc 113), (.negSucc 27), (.negSucc 11), (.ofNat 74), (.negSucc 19), (.negSucc 103), (.ofNat 87), (.negSucc 36), (.ofNat 95), (.negSucc 109), (.ofNat 104), (.ofNat 68), (.negSucc 105), (.ofNat 107), (.ofNat 59)],
  [(.negSucc 105), (.ofNat 51), (.ofNat 96), (.ofNat 97), (.negSucc 107), (.negSucc 56), (.ofNat 11), (.ofNat 103), (.negSucc 77), (.ofNat 68), (.ofNat 26), (.ofNat 71), (.ofNat 103), (.negSucc 114), (.negSucc 96), (.negSucc 43)],
  [(.negSucc 74), (.ofNat 82), (.ofNat 120), (.negSucc 106), (.ofNat 9), (.ofNat 100), (.ofNat 98), (.ofNat 53), (.negSucc 84), (.ofNat 41), (.ofNat 99), (.negSucc 22), (.negSucc 85), (.negSucc 70), (.negSucc 54), (.negSucc 101)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 19 → ∀ b, b < 19 → answer a b = (a + b) % 19

end LeanCheckedNetwork.Net
