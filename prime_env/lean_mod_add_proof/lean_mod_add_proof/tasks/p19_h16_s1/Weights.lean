import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 19

19 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=19 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 19

def E1 : List (List Int) := [
  [(.ofNat 0), (.negSucc 50), (.ofNat 111), (.ofNat 85), (.ofNat 17), (.negSucc 73), (.negSucc 19), (.ofNat 38), (.ofNat 107), (.negSucc 112), (.negSucc 96), (.negSucc 75), (.negSucc 84), (.ofNat 111), (.ofNat 95), (.negSucc 96)],
  [(.ofNat 93), (.ofNat 40), (.negSucc 62), (.ofNat 78), (.negSucc 18), (.negSucc 94), (.ofNat 88), (.ofNat 117), (.ofNat 99), (.ofNat 123), (.ofNat 103), (.negSucc 88), (.ofNat 20), (.ofNat 86), (.negSucc 91), (.ofNat 73)],
  [(.ofNat 28), (.ofNat 25), (.negSucc 94), (.negSucc 80), (.negSucc 86), (.ofNat 78), (.negSucc 97), (.ofNat 89), (.ofNat 90), (.negSucc 110), (.negSucc 86), (.negSucc 72), (.ofNat 85), (.ofNat 78), (.negSucc 44), (.ofNat 95)],
  [(.negSucc 92), (.negSucc 86), (.negSucc 69), (.negSucc 83), (.negSucc 93), (.ofNat 27), (.ofNat 81), (.ofNat 94), (.ofNat 72), (.ofNat 114), (.ofNat 73), (.negSucc 75), (.ofNat 109), (.negSucc 72), (.ofNat 95), (.negSucc 73)],
  [(.ofNat 45), (.ofNat 100), (.ofNat 95), (.ofNat 47), (.negSucc 103), (.negSucc 86), (.negSucc 103), (.ofNat 51), (.ofNat 44), (.negSucc 112), (.negSucc 46), (.negSucc 48), (.ofNat 100), (.negSucc 97), (.negSucc 77), (.negSucc 107)],
  [(.ofNat 104), (.negSucc 108), (.ofNat 102), (.ofNat 92), (.negSucc 99), (.negSucc 74), (.ofNat 89), (.negSucc 78), (.ofNat 61), (.ofNat 102), (.negSucc 42), (.negSucc 76), (.ofNat 61), (.negSucc 72), (.negSucc 81), (.ofNat 87)],
  [(.negSucc 92), (.ofNat 127), (.negSucc 74), (.ofNat 70), (.negSucc 84), (.ofNat 95), (.negSucc 62), (.negSucc 102), (.ofNat 86), (.negSucc 93), (.ofNat 86), (.ofNat 21), (.negSucc 34), (.ofNat 49), (.ofNat 91), (.ofNat 98)],
  [(.negSucc 73), (.negSucc 103), (.negSucc 93), (.negSucc 91), (.negSucc 70), (.negSucc 5), (.negSucc 77), (.negSucc 83), (.ofNat 34), (.ofNat 82), (.negSucc 113), (.ofNat 98), (.negSucc 74), (.ofNat 96), (.negSucc 34), (.negSucc 75)],
  [(.ofNat 65), (.ofNat 110), (.negSucc 4), (.negSucc 66), (.negSucc 72), (.negSucc 100), (.ofNat 97), (.negSucc 92), (.negSucc 34), (.negSucc 89), (.ofNat 95), (.ofNat 86), (.negSucc 107), (.ofNat 89), (.negSucc 87), (.negSucc 86)],
  [(.ofNat 99), (.negSucc 118), (.ofNat 102), (.ofNat 76), (.ofNat 0), (.ofNat 72), (.negSucc 106), (.negSucc 29), (.negSucc 59), (.ofNat 85), (.negSucc 94), (.ofNat 82), (.negSucc 92), (.negSucc 29), (.ofNat 90), (.ofNat 93)],
  [(.negSucc 71), (.ofNat 115), (.ofNat 96), (.ofNat 90), (.ofNat 66), (.ofNat 111), (.ofNat 98), (.ofNat 110), (.negSucc 100), (.negSucc 84), (.ofNat 74), (.ofNat 88), (.negSucc 54), (.negSucc 105), (.ofNat 56), (.ofNat 75)],
  [(.negSucc 101), (.negSucc 102), (.negSucc 80), (.ofNat 41), (.ofNat 100), (.negSucc 55), (.negSucc 91), (.ofNat 106), (.negSucc 91), (.ofNat 81), (.negSucc 53), (.ofNat 104), (.ofNat 57), (.negSucc 75), (.negSucc 82), (.negSucc 93)],
  [(.ofNat 90), (.ofNat 101), (.negSucc 102), (.negSucc 85), (.ofNat 111), (.negSucc 93), (.ofNat 82), (.ofNat 90), (.negSucc 86), (.negSucc 80), (.negSucc 89), (.ofNat 92), (.ofNat 115), (.ofNat 11), (.ofNat 80), (.ofNat 11)],
  [(.ofNat 98), (.negSucc 94), (.ofNat 48), (.negSucc 67), (.ofNat 107), (.ofNat 82), (.ofNat 62), (.ofNat 69), (.negSucc 84), (.ofNat 36), (.ofNat 95), (.ofNat 93), (.ofNat 98), (.ofNat 95), (.ofNat 93), (.ofNat 111)],
  [(.negSucc 79), (.ofNat 86), (.ofNat 97), (.ofNat 103), (.ofNat 89), (.ofNat 95), (.negSucc 93), (.negSucc 33), (.negSucc 62), (.ofNat 2), (.negSucc 115), (.ofNat 16), (.ofNat 80), (.ofNat 87), (.negSucc 91), (.ofNat 10)],
  [(.negSucc 92), (.negSucc 82), (.ofNat 3), (.ofNat 92), (.ofNat 86), (.negSucc 89), (.ofNat 108), (.negSucc 121), (.negSucc 96), (.negSucc 18), (.ofNat 88), (.ofNat 75), (.negSucc 13), (.ofNat 31), (.ofNat 91), (.negSucc 100)],
  [(.ofNat 87), (.ofNat 81), (.negSucc 98), (.negSucc 40), (.ofNat 95), (.negSucc 97), (.negSucc 97), (.negSucc 90), (.negSucc 69), (.ofNat 87), (.negSucc 68), (.negSucc 75), (.negSucc 52), (.negSucc 101), (.ofNat 86), (.ofNat 65)],
  [(.ofNat 93), (.negSucc 46), (.negSucc 112), (.negSucc 98), (.ofNat 65), (.ofNat 90), (.ofNat 99), (.negSucc 93), (.ofNat 45), (.negSucc 15), (.ofNat 39), (.negSucc 99), (.negSucc 120), (.negSucc 96), (.negSucc 82), (.ofNat 110)],
  [(.negSucc 103), (.ofNat 99), (.ofNat 98), (.negSucc 25), (.ofNat 41), (.ofNat 90), (.negSucc 82), (.negSucc 75), (.ofNat 96), (.ofNat 114), (.ofNat 65), (.negSucc 103), (.negSucc 108), (.negSucc 88), (.ofNat 38), (.negSucc 59)]]

def E2 : List (List Int) := [
  [(.negSucc 92), (.ofNat 127), (.negSucc 74), (.ofNat 70), (.negSucc 84), (.ofNat 95), (.negSucc 62), (.ofNat 103), (.negSucc 85), (.negSucc 93), (.ofNat 86), (.ofNat 21), (.negSucc 34), (.ofNat 49), (.ofNat 91), (.ofNat 98)],
  [(.negSucc 73), (.negSucc 103), (.negSucc 93), (.negSucc 91), (.negSucc 70), (.negSucc 5), (.negSucc 77), (.ofNat 84), (.negSucc 33), (.ofNat 82), (.negSucc 113), (.ofNat 98), (.negSucc 74), (.ofNat 96), (.negSucc 34), (.negSucc 75)],
  [(.ofNat 65), (.ofNat 110), (.negSucc 4), (.negSucc 66), (.negSucc 72), (.negSucc 100), (.ofNat 97), (.ofNat 93), (.ofNat 35), (.negSucc 89), (.ofNat 95), (.ofNat 86), (.negSucc 107), (.ofNat 89), (.negSucc 87), (.negSucc 86)],
  [(.ofNat 99), (.negSucc 118), (.ofNat 102), (.ofNat 76), (.ofNat 0), (.ofNat 72), (.negSucc 106), (.ofNat 30), (.ofNat 60), (.ofNat 85), (.negSucc 94), (.ofNat 82), (.negSucc 92), (.negSucc 29), (.ofNat 90), (.ofNat 93)],
  [(.negSucc 71), (.ofNat 115), (.ofNat 96), (.ofNat 90), (.ofNat 66), (.ofNat 111), (.ofNat 98), (.negSucc 109), (.ofNat 101), (.negSucc 84), (.ofNat 74), (.ofNat 88), (.negSucc 54), (.negSucc 105), (.ofNat 56), (.ofNat 75)],
  [(.negSucc 101), (.negSucc 102), (.negSucc 80), (.ofNat 41), (.ofNat 100), (.negSucc 55), (.negSucc 91), (.negSucc 105), (.ofNat 92), (.ofNat 81), (.negSucc 53), (.ofNat 104), (.ofNat 57), (.negSucc 75), (.negSucc 82), (.negSucc 93)],
  [(.ofNat 90), (.ofNat 101), (.negSucc 102), (.negSucc 85), (.ofNat 111), (.negSucc 93), (.ofNat 82), (.negSucc 89), (.ofNat 87), (.negSucc 80), (.negSucc 89), (.ofNat 92), (.ofNat 115), (.ofNat 11), (.ofNat 80), (.ofNat 11)],
  [(.ofNat 98), (.negSucc 94), (.ofNat 48), (.negSucc 67), (.ofNat 107), (.ofNat 82), (.ofNat 62), (.negSucc 68), (.ofNat 85), (.ofNat 36), (.ofNat 95), (.ofNat 93), (.ofNat 98), (.ofNat 95), (.ofNat 93), (.ofNat 111)],
  [(.negSucc 79), (.ofNat 86), (.ofNat 97), (.ofNat 103), (.ofNat 89), (.ofNat 95), (.negSucc 93), (.ofNat 34), (.ofNat 63), (.ofNat 2), (.negSucc 115), (.ofNat 16), (.ofNat 80), (.ofNat 87), (.negSucc 91), (.ofNat 10)],
  [(.negSucc 92), (.negSucc 82), (.ofNat 3), (.ofNat 92), (.ofNat 86), (.negSucc 89), (.ofNat 108), (.ofNat 122), (.ofNat 97), (.negSucc 18), (.ofNat 88), (.ofNat 75), (.negSucc 13), (.ofNat 31), (.ofNat 91), (.negSucc 100)],
  [(.ofNat 87), (.ofNat 81), (.negSucc 98), (.negSucc 40), (.ofNat 95), (.negSucc 97), (.negSucc 97), (.ofNat 91), (.ofNat 70), (.ofNat 87), (.negSucc 68), (.negSucc 75), (.negSucc 52), (.negSucc 101), (.ofNat 86), (.ofNat 65)],
  [(.ofNat 93), (.negSucc 46), (.negSucc 112), (.negSucc 98), (.ofNat 65), (.ofNat 90), (.ofNat 99), (.ofNat 94), (.negSucc 44), (.negSucc 15), (.ofNat 39), (.negSucc 99), (.negSucc 120), (.negSucc 96), (.negSucc 82), (.ofNat 110)],
  [(.negSucc 103), (.ofNat 99), (.ofNat 98), (.negSucc 25), (.ofNat 41), (.ofNat 90), (.negSucc 82), (.ofNat 76), (.negSucc 95), (.ofNat 114), (.ofNat 65), (.negSucc 103), (.negSucc 108), (.negSucc 88), (.ofNat 38), (.negSucc 59)],
  [(.ofNat 0), (.negSucc 50), (.ofNat 111), (.ofNat 85), (.ofNat 17), (.negSucc 73), (.negSucc 19), (.negSucc 37), (.negSucc 106), (.negSucc 112), (.negSucc 96), (.negSucc 75), (.negSucc 84), (.ofNat 111), (.ofNat 95), (.negSucc 96)],
  [(.ofNat 93), (.ofNat 40), (.negSucc 62), (.ofNat 78), (.negSucc 18), (.negSucc 94), (.ofNat 88), (.negSucc 116), (.negSucc 98), (.ofNat 123), (.ofNat 103), (.negSucc 88), (.ofNat 20), (.ofNat 86), (.negSucc 91), (.ofNat 73)],
  [(.ofNat 28), (.ofNat 25), (.negSucc 94), (.negSucc 80), (.negSucc 86), (.ofNat 78), (.negSucc 97), (.negSucc 88), (.negSucc 89), (.negSucc 110), (.negSucc 86), (.negSucc 72), (.ofNat 85), (.ofNat 78), (.negSucc 44), (.ofNat 95)],
  [(.negSucc 92), (.negSucc 86), (.negSucc 69), (.negSucc 83), (.negSucc 93), (.ofNat 27), (.ofNat 81), (.negSucc 93), (.negSucc 71), (.ofNat 114), (.ofNat 73), (.negSucc 75), (.ofNat 109), (.negSucc 72), (.ofNat 95), (.negSucc 73)],
  [(.ofNat 45), (.ofNat 100), (.ofNat 95), (.ofNat 47), (.negSucc 103), (.negSucc 86), (.negSucc 103), (.negSucc 50), (.negSucc 43), (.negSucc 112), (.negSucc 46), (.negSucc 48), (.ofNat 100), (.negSucc 97), (.negSucc 77), (.negSucc 107)],
  [(.ofNat 104), (.negSucc 108), (.ofNat 102), (.ofNat 92), (.negSucc 99), (.negSucc 74), (.ofNat 89), (.ofNat 79), (.negSucc 60), (.ofNat 102), (.negSucc 42), (.negSucc 76), (.ofNat 61), (.negSucc 72), (.negSucc 81), (.ofNat 87)]]

def W2 : List (List Int) := [
  [(.ofNat 96), (.negSucc 97), (.negSucc 94), (.ofNat 84), (.negSucc 38), (.negSucc 86), (.ofNat 116), (.ofNat 24), (.negSucc 106), (.ofNat 106), (.negSucc 48), (.negSucc 16), (.ofNat 84), (.negSucc 51), (.ofNat 98), (.negSucc 77)],
  [(.ofNat 13), (.ofNat 70), (.negSucc 65), (.negSucc 16), (.ofNat 33), (.negSucc 81), (.negSucc 110), (.ofNat 114), (.negSucc 89), (.negSucc 110), (.ofNat 88), (.negSucc 86), (.ofNat 121), (.ofNat 69), (.negSucc 78), (.ofNat 112)],
  [(.negSucc 112), (.negSucc 73), (.ofNat 47), (.negSucc 95), (.ofNat 42), (.ofNat 110), (.ofNat 75), (.ofNat 104), (.negSucc 94), (.ofNat 79), (.negSucc 103), (.negSucc 99), (.ofNat 85), (.ofNat 80), (.negSucc 73), (.negSucc 41)],
  [(.ofNat 26), (.ofNat 15), (.ofNat 111), (.negSucc 71), (.ofNat 33), (.negSucc 12), (.negSucc 55), (.ofNat 93), (.negSucc 52), (.negSucc 110), (.ofNat 102), (.negSucc 93), (.ofNat 26), (.ofNat 70), (.ofNat 90), (.negSucc 109)],
  [(.ofNat 106), (.negSucc 39), (.ofNat 33), (.ofNat 112), (.ofNat 121), (.negSucc 94), (.ofNat 15), (.ofNat 18), (.ofNat 30), (.ofNat 115), (.negSucc 100), (.negSucc 104), (.negSucc 70), (.negSucc 54), (.negSucc 27), (.negSucc 30)],
  [(.negSucc 74), (.ofNat 64), (.negSucc 107), (.ofNat 93), (.ofNat 115), (.negSucc 65), (.ofNat 22), (.negSucc 23), (.ofNat 101), (.negSucc 105), (.ofNat 87), (.negSucc 80), (.negSucc 117), (.negSucc 93), (.negSucc 27), (.ofNat 121)],
  [(.negSucc 71), (.ofNat 19), (.ofNat 27), (.negSucc 108), (.ofNat 94), (.ofNat 104), (.negSucc 97), (.negSucc 106), (.ofNat 63), (.ofNat 101), (.ofNat 50), (.negSucc 98), (.negSucc 98), (.negSucc 77), (.ofNat 104), (.ofNat 9)],
  [(.ofNat 78), (.negSucc 6), (.ofNat 98), (.negSucc 102), (.ofNat 80), (.negSucc 6), (.ofNat 124), (.negSucc 121), (.ofNat 110), (.negSucc 98), (.negSucc 54), (.negSucc 88), (.negSucc 65), (.ofNat 94), (.ofNat 38), (.negSucc 101)],
  [(.ofNat 73), (.ofNat 33), (.ofNat 85), (.negSucc 39), (.ofNat 67), (.negSucc 108), (.negSucc 104), (.negSucc 103), (.ofNat 83), (.ofNat 31), (.ofNat 107), (.negSucc 97), (.negSucc 25), (.ofNat 90), (.negSucc 116), (.ofNat 43)],
  [(.negSucc 99), (.negSucc 48), (.negSucc 83), (.ofNat 122), (.negSucc 91), (.negSucc 83), (.ofNat 94), (.negSucc 51), (.ofNat 110), (.negSucc 48), (.negSucc 110), (.ofNat 28), (.ofNat 58), (.ofNat 109), (.ofNat 74), (.ofNat 95)],
  [(.negSucc 94), (.ofNat 11), (.negSucc 117), (.ofNat 70), (.negSucc 89), (.ofNat 111), (.negSucc 36), (.ofNat 21), (.ofNat 66), (.ofNat 10), (.ofNat 90), (.ofNat 26), (.ofNat 105), (.ofNat 0), (.ofNat 7), (.negSucc 88)],
  [(.ofNat 110), (.negSucc 63), (.ofNat 32), (.negSucc 114), (.negSucc 114), (.ofNat 7), (.negSucc 7), (.ofNat 117), (.ofNat 81), (.ofNat 7), (.negSucc 84), (.ofNat 106), (.ofNat 120), (.negSucc 24), (.negSucc 104), (.negSucc 126)],
  [(.ofNat 0), (.ofNat 47), (.ofNat 105), (.negSucc 72), (.negSucc 116), (.negSucc 105), (.ofNat 79), (.ofNat 126), (.negSucc 98), (.ofNat 4), (.negSucc 37), (.negSucc 18), (.ofNat 63), (.negSucc 101), (.ofNat 40), (.ofNat 82)],
  [(.negSucc 108), (.negSucc 122), (.ofNat 9), (.ofNat 101), (.negSucc 101), (.ofNat 4), (.negSucc 119), (.ofNat 99), (.negSucc 56), (.ofNat 63), (.ofNat 78), (.ofNat 88), (.negSucc 6), (.negSucc 56), (.ofNat 84), (.ofNat 92)],
  [(.negSucc 77), (.ofNat 101), (.negSucc 69), (.ofNat 98), (.negSucc 92), (.ofNat 112), (.ofNat 92), (.ofNat 9), (.negSucc 53), (.negSucc 67), (.negSucc 94), (.ofNat 78), (.negSucc 100), (.ofNat 106), (.negSucc 100), (.negSucc 82)],
  [(.ofNat 111), (.negSucc 116), (.negSucc 121), (.ofNat 29), (.negSucc 49), (.negSucc 44), (.negSucc 63), (.negSucc 47), (.negSucc 29), (.ofNat 63), (.ofNat 100), (.ofNat 101), (.negSucc 102), (.ofNat 98), (.ofNat 75), (.negSucc 39)],
  [(.negSucc 30), (.ofNat 116), (.ofNat 50), (.negSucc 106), (.negSucc 76), (.negSucc 88), (.ofNat 49), (.negSucc 126), (.negSucc 34), (.negSucc 103), (.negSucc 100), (.ofNat 110), (.negSucc 96), (.ofNat 69), (.ofNat 115), (.ofNat 107)],
  [(.negSucc 115), (.negSucc 107), (.ofNat 114), (.negSucc 54), (.ofNat 16), (.ofNat 76), (.ofNat 22), (.negSucc 98), (.negSucc 47), (.ofNat 83), (.ofNat 77), (.ofNat 92), (.negSucc 34), (.negSucc 62), (.negSucc 103), (.ofNat 71)],
  [(.ofNat 28), (.ofNat 110), (.ofNat 24), (.ofNat 121), (.negSucc 15), (.ofNat 95), (.negSucc 92), (.negSucc 73), (.negSucc 100), (.negSucc 99), (.negSucc 43), (.ofNat 89), (.ofNat 58), (.negSucc 112), (.ofNat 28), (.negSucc 109)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 19 → ∀ b, b < 19 → answer a b = (a + b) % 19

end LeanCheckedNetwork.Net
