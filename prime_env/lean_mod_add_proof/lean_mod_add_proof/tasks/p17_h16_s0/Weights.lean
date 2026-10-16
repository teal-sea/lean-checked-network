import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 17

17 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=17 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 17

def E1 : List (List Int) := [
  [(.ofNat 107), (.ofNat 74), (.ofNat 68), (.ofNat 102), (.ofNat 109), (.negSucc 102), (.negSucc 88), (.negSucc 89), (.ofNat 88), (.ofNat 96), (.ofNat 105), (.negSucc 42), (.negSucc 107), (.negSucc 90), (.ofNat 85), (.negSucc 104)],
  [(.negSucc 105), (.negSucc 100), (.negSucc 71), (.ofNat 24), (.negSucc 86), (.ofNat 102), (.negSucc 119), (.ofNat 97), (.negSucc 94), (.ofNat 83), (.ofNat 106), (.ofNat 87), (.ofNat 50), (.negSucc 106), (.negSucc 17), (.negSucc 106)],
  [(.ofNat 66), (.negSucc 85), (.negSucc 77), (.negSucc 123), (.negSucc 103), (.negSucc 93), (.ofNat 34), (.negSucc 35), (.ofNat 95), (.ofNat 74), (.ofNat 90), (.negSucc 95), (.ofNat 103), (.ofNat 113), (.negSucc 50), (.negSucc 99)],
  [(.ofNat 91), (.ofNat 110), (.negSucc 107), (.negSucc 82), (.ofNat 117), (.ofNat 23), (.ofNat 93), (.negSucc 104), (.negSucc 52), (.ofNat 64), (.ofNat 40), (.ofNat 95), (.ofNat 43), (.negSucc 94), (.negSucc 63), (.negSucc 101)],
  [(.negSucc 102), (.ofNat 90), (.negSucc 93), (.ofNat 1), (.negSucc 91), (.ofNat 24), (.ofNat 127), (.ofNat 63), (.negSucc 113), (.ofNat 44), (.negSucc 77), (.negSucc 89), (.negSucc 108), (.negSucc 7), (.negSucc 103), (.negSucc 103)],
  [(.ofNat 99), (.negSucc 85), (.ofNat 75), (.ofNat 116), (.negSucc 49), (.negSucc 94), (.negSucc 29), (.ofNat 80), (.ofNat 105), (.negSucc 0), (.negSucc 106), (.ofNat 70), (.ofNat 3), (.ofNat 117), (.negSucc 114), (.negSucc 92)],
  [(.ofNat 31), (.negSucc 101), (.ofNat 89), (.ofNat 81), (.ofNat 113), (.ofNat 90), (.negSucc 96), (.negSucc 94), (.negSucc 77), (.negSucc 117), (.negSucc 104), (.negSucc 29), (.ofNat 95), (.negSucc 108), (.negSucc 105), (.negSucc 17)],
  [(.negSucc 99), (.ofNat 79), (.ofNat 112), (.negSucc 49), (.negSucc 107), (.negSucc 110), (.negSucc 114), (.negSucc 38), (.negSucc 91), (.negSucc 97), (.negSucc 67), (.negSucc 100), (.ofNat 88), (.ofNat 75), (.negSucc 103), (.negSucc 10)],
  [(.ofNat 96), (.ofNat 98), (.ofNat 104), (.negSucc 110), (.ofNat 70), (.ofNat 76), (.ofNat 45), (.ofNat 101), (.ofNat 97), (.negSucc 92), (.ofNat 66), (.ofNat 95), (.negSucc 95), (.ofNat 95), (.negSucc 87), (.ofNat 37)],
  [(.negSucc 24), (.negSucc 77), (.negSucc 39), (.negSucc 88), (.ofNat 121), (.ofNat 21), (.ofNat 108), (.negSucc 51), (.negSucc 99), (.negSucc 103), (.ofNat 105), (.negSucc 96), (.negSucc 105), (.negSucc 101), (.negSucc 91), (.ofNat 89)],
  [(.negSucc 103), (.negSucc 122), (.negSucc 70), (.ofNat 76), (.negSucc 104), (.negSucc 65), (.ofNat 110), (.negSucc 107), (.ofNat 38), (.negSucc 99), (.ofNat 109), (.ofNat 85), (.ofNat 99), (.ofNat 91), (.negSucc 30), (.ofNat 117)],
  [(.ofNat 109), (.ofNat 16), (.negSucc 101), (.ofNat 108), (.ofNat 80), (.ofNat 102), (.negSucc 55), (.ofNat 102), (.ofNat 112), (.negSucc 64), (.ofNat 96), (.negSucc 67), (.ofNat 109), (.ofNat 95), (.ofNat 101), (.ofNat 100)],
  [(.negSucc 98), (.ofNat 102), (.negSucc 110), (.ofNat 46), (.ofNat 74), (.negSucc 100), (.negSucc 106), (.ofNat 6), (.negSucc 97), (.negSucc 39), (.negSucc 23), (.negSucc 68), (.negSucc 55), (.negSucc 104), (.ofNat 92), (.ofNat 101)],
  [(.negSucc 90), (.negSucc 69), (.ofNat 17), (.negSucc 105), (.negSucc 115), (.ofNat 118), (.negSucc 15), (.negSucc 102), (.ofNat 86), (.ofNat 72), (.negSucc 105), (.ofNat 114), (.negSucc 98), (.ofNat 102), (.ofNat 107), (.ofNat 95)],
  [(.ofNat 105), (.negSucc 108), (.ofNat 59), (.negSucc 101), (.ofNat 107), (.negSucc 94), (.ofNat 71), (.ofNat 40), (.ofNat 111), (.ofNat 76), (.negSucc 106), (.negSucc 110), (.ofNat 73), (.negSucc 72), (.ofNat 105), (.ofNat 90)],
  [(.negSucc 101), (.negSucc 32), (.ofNat 93), (.negSucc 50), (.negSucc 81), (.negSucc 36), (.ofNat 121), (.ofNat 105), (.negSucc 99), (.ofNat 104), (.negSucc 86), (.ofNat 91), (.ofNat 99), (.negSucc 109), (.ofNat 103), (.ofNat 18)],
  [(.ofNat 9), (.ofNat 120), (.ofNat 120), (.ofNat 109), (.negSucc 119), (.ofNat 67), (.ofNat 25), (.negSucc 67), (.ofNat 88), (.ofNat 106), (.ofNat 4), (.negSucc 83), (.negSucc 79), (.ofNat 98), (.ofNat 100), (.negSucc 39)]]

def E2 : List (List Int) := [
  [(.negSucc 112), (.ofNat 98), (.negSucc 92), (.ofNat 63), (.ofNat 101), (.negSucc 102), (.negSucc 91), (.ofNat 10), (.ofNat 112), (.ofNat 54), (.ofNat 12), (.negSucc 111), (.ofNat 42), (.ofNat 81), (.ofNat 109), (.negSucc 81)],
  [(.ofNat 95), (.ofNat 75), (.negSucc 43), (.ofNat 112), (.negSucc 61), (.ofNat 107), (.ofNat 59), (.ofNat 94), (.negSucc 94), (.ofNat 95), (.ofNat 100), (.ofNat 103), (.negSucc 108), (.ofNat 101), (.ofNat 102), (.negSucc 43)],
  [(.ofNat 10), (.negSucc 100), (.ofNat 64), (.ofNat 86), (.negSucc 95), (.ofNat 57), (.ofNat 105), (.negSucc 69), (.ofNat 83), (.ofNat 106), (.ofNat 100), (.negSucc 79), (.negSucc 76), (.negSucc 96), (.ofNat 103), (.ofNat 64)],
  [(.negSucc 98), (.negSucc 105), (.ofNat 107), (.negSucc 107), (.ofNat 104), (.negSucc 106), (.ofNat 53), (.negSucc 75), (.ofNat 50), (.ofNat 118), (.ofNat 95), (.ofNat 56), (.ofNat 106), (.ofNat 81), (.ofNat 68), (.ofNat 88)],
  [(.ofNat 104), (.ofNat 70), (.ofNat 98), (.negSucc 108), (.negSucc 88), (.ofNat 95), (.negSucc 76), (.ofNat 121), (.negSucc 105), (.ofNat 103), (.ofNat 63), (.ofNat 45), (.ofNat 73), (.ofNat 90), (.negSucc 57), (.ofNat 92)],
  [(.negSucc 80), (.ofNat 100), (.ofNat 53), (.negSucc 58), (.negSucc 77), (.negSucc 100), (.negSucc 103), (.negSucc 5), (.ofNat 95), (.ofNat 84), (.negSucc 83), (.negSucc 90), (.negSucc 95), (.negSucc 113), (.negSucc 35), (.ofNat 98)],
  [(.negSucc 79), (.negSucc 90), (.negSucc 83), (.ofNat 122), (.ofNat 110), (.ofNat 107), (.negSucc 8), (.negSucc 97), (.negSucc 68), (.ofNat 62), (.negSucc 98), (.ofNat 108), (.negSucc 84), (.ofNat 91), (.negSucc 81), (.ofNat 111)],
  [(.ofNat 104), (.negSucc 92), (.negSucc 97), (.ofNat 98), (.negSucc 92), (.negSucc 90), (.ofNat 87), (.ofNat 68), (.negSucc 103), (.ofNat 9), (.negSucc 93), (.negSucc 104), (.ofNat 65), (.negSucc 23), (.negSucc 80), (.ofNat 110)],
  [(.negSucc 109), (.ofNat 77), (.negSucc 93), (.ofNat 40), (.ofNat 25), (.negSucc 84), (.ofNat 111), (.ofNat 82), (.ofNat 109), (.negSucc 54), (.negSucc 47), (.ofNat 84), (.ofNat 97), (.negSucc 118), (.negSucc 116), (.ofNat 83)],
  [(.negSucc 39), (.ofNat 106), (.negSucc 66), (.negSucc 125), (.ofNat 107), (.ofNat 101), (.ofNat 12), (.negSucc 106), (.negSucc 83), (.negSucc 92), (.ofNat 82), (.negSucc 78), (.negSucc 81), (.ofNat 103), (.negSucc 116), (.ofNat 39)],
  [(.ofNat 107), (.negSucc 34), (.ofNat 39), (.negSucc 75), (.negSucc 106), (.negSucc 97), (.negSucc 95), (.negSucc 20), (.negSucc 89), (.negSucc 100), (.ofNat 106), (.negSucc 96), (.negSucc 97), (.negSucc 83), (.negSucc 105), (.negSucc 35)],
  [(.negSucc 97), (.negSucc 87), (.ofNat 88), (.negSucc 3), (.ofNat 76), (.ofNat 107), (.negSucc 103), (.ofNat 95), (.ofNat 82), (.negSucc 99), (.ofNat 93), (.ofNat 103), (.ofNat 25), (.negSucc 79), (.negSucc 89), (.negSucc 32)],
  [(.ofNat 32), (.negSucc 89), (.ofNat 93), (.ofNat 127), (.ofNat 113), (.negSucc 92), (.ofNat 23), (.negSucc 54), (.negSucc 92), (.negSucc 108), (.ofNat 73), (.negSucc 99), (.ofNat 102), (.ofNat 100), (.negSucc 60), (.negSucc 72)],
  [(.ofNat 112), (.ofNat 109), (.ofNat 90), (.ofNat 80), (.negSucc 114), (.negSucc 18), (.ofNat 106), (.negSucc 99), (.ofNat 28), (.negSucc 101), (.negSucc 28), (.ofNat 91), (.negSucc 13), (.negSucc 91), (.ofNat 3), (.negSucc 112)],
  [(.negSucc 93), (.ofNat 81), (.negSucc 20), (.negSucc 34), (.ofNat 87), (.ofNat 96), (.ofNat 114), (.ofNat 99), (.ofNat 104), (.negSucc 100), (.negSucc 104), (.negSucc 71), (.negSucc 114), (.negSucc 50), (.ofNat 73), (.negSucc 105)],
  [(.ofNat 93), (.negSucc 96), (.negSucc 92), (.negSucc 115), (.ofNat 28), (.negSucc 100), (.negSucc 45), (.ofNat 34), (.negSucc 97), (.negSucc 48), (.negSucc 99), (.ofNat 12), (.ofNat 11), (.ofNat 114), (.ofNat 85), (.negSucc 111)],
  [(.ofNat 42), (.negSucc 92), (.negSucc 101), (.negSucc 66), (.negSucc 120), (.ofNat 99), (.negSucc 97), (.negSucc 97), (.ofNat 69), (.ofNat 65), (.negSucc 72), (.ofNat 109), (.ofNat 104), (.negSucc 104), (.ofNat 97), (.negSucc 95)]]

def W2 : List (List Int) := [
  [(.negSucc 103), (.ofNat 17), (.negSucc 38), (.ofNat 55), (.ofNat 55), (.ofNat 125), (.ofNat 109), (.negSucc 108), (.negSucc 97), (.ofNat 48), (.negSucc 117), (.negSucc 63), (.negSucc 45), (.ofNat 30), (.ofNat 72), (.ofNat 110)],
  [(.ofNat 26), (.negSucc 94), (.ofNat 91), (.ofNat 79), (.negSucc 5), (.negSucc 114), (.ofNat 42), (.negSucc 69), (.negSucc 96), (.ofNat 96), (.ofNat 30), (.ofNat 21), (.ofNat 114), (.negSucc 108), (.ofNat 34), (.ofNat 117)],
  [(.negSucc 97), (.negSucc 124), (.ofNat 98), (.negSucc 76), (.negSucc 118), (.negSucc 76), (.negSucc 118), (.ofNat 102), (.ofNat 89), (.ofNat 116), (.ofNat 104), (.ofNat 80), (.ofNat 73), (.ofNat 49), (.negSucc 81), (.ofNat 63)],
  [(.ofNat 12), (.ofNat 24), (.ofNat 87), (.negSucc 104), (.ofNat 117), (.ofNat 70), (.negSucc 99), (.negSucc 84), (.negSucc 94), (.ofNat 102), (.ofNat 101), (.negSucc 117), (.negSucc 102), (.ofNat 28), (.negSucc 65), (.ofNat 72)],
  [(.ofNat 103), (.ofNat 108), (.ofNat 80), (.negSucc 126), (.negSucc 34), (.negSucc 90), (.negSucc 34), (.negSucc 90), (.ofNat 72), (.ofNat 98), (.ofNat 109), (.ofNat 101), (.negSucc 101), (.negSucc 101), (.negSucc 103), (.negSucc 17)],
  [(.negSucc 110), (.negSucc 94), (.negSucc 101), (.ofNat 54), (.negSucc 105), (.ofNat 95), (.ofNat 122), (.ofNat 85), (.ofNat 78), (.ofNat 108), (.negSucc 38), (.negSucc 104), (.ofNat 86), (.ofNat 73), (.negSucc 107), (.negSucc 42)],
  [(.ofNat 55), (.negSucc 117), (.negSucc 102), (.ofNat 105), (.ofNat 123), (.negSucc 121), (.ofNat 107), (.ofNat 40), (.negSucc 101), (.negSucc 12), (.negSucc 88), (.ofNat 76), (.ofNat 97), (.ofNat 67), (.negSucc 107), (.negSucc 83)],
  [(.ofNat 118), (.ofNat 89), (.negSucc 106), (.ofNat 126), (.negSucc 74), (.ofNat 108), (.ofNat 84), (.negSucc 101), (.ofNat 100), (.ofNat 104), (.negSucc 100), (.negSucc 2), (.negSucc 115), (.negSucc 105), (.negSucc 122), (.negSucc 100)],
  [(.negSucc 107), (.ofNat 115), (.ofNat 17), (.negSucc 53), (.ofNat 11), (.ofNat 92), (.negSucc 120), (.ofNat 112), (.ofNat 101), (.ofNat 16), (.negSucc 110), (.negSucc 81), (.negSucc 80), (.ofNat 107), (.negSucc 29), (.negSucc 98)],
  [(.ofNat 102), (.negSucc 47), (.ofNat 81), (.negSucc 112), (.ofNat 119), (.negSucc 93), (.negSucc 100), (.ofNat 93), (.negSucc 112), (.negSucc 97), (.ofNat 8), (.ofNat 118), (.ofNat 117), (.negSucc 6), (.ofNat 24), (.negSucc 112)],
  [(.ofNat 109), (.negSucc 108), (.ofNat 106), (.negSucc 56), (.negSucc 87), (.ofNat 110), (.ofNat 46), (.negSucc 115), (.ofNat 106), (.negSucc 83), (.ofNat 102), (.negSucc 100), (.ofNat 102), (.negSucc 82), (.negSucc 66), (.negSucc 110)],
  [(.negSucc 118), (.negSucc 38), (.ofNat 109), (.ofNat 76), (.negSucc 6), (.negSucc 104), (.ofNat 125), (.negSucc 92), (.negSucc 19), (.negSucc 98), (.ofNat 109), (.ofNat 92), (.ofNat 0), (.ofNat 102), (.negSucc 24), (.negSucc 88)],
  [(.ofNat 60), (.ofNat 45), (.ofNat 30), (.ofNat 102), (.ofNat 69), (.ofNat 78), (.ofNat 87), (.ofNat 89), (.negSucc 122), (.negSucc 103), (.ofNat 72), (.negSucc 71), (.negSucc 105), (.negSucc 94), (.ofNat 23), (.negSucc 106)],
  [(.ofNat 62), (.ofNat 67), (.negSucc 69), (.ofNat 23), (.negSucc 104), (.negSucc 30), (.negSucc 76), (.ofNat 43), (.ofNat 112), (.negSucc 104), (.ofNat 44), (.negSucc 75), (.ofNat 65), (.negSucc 36), (.ofNat 100), (.ofNat 37)],
  [(.negSucc 99), (.negSucc 94), (.negSucc 98), (.negSucc 88), (.ofNat 92), (.negSucc 7), (.negSucc 107), (.negSucc 95), (.negSucc 51), (.negSucc 89), (.negSucc 22), (.ofNat 106), (.ofNat 95), (.ofNat 124), (.ofNat 124), (.ofNat 89)],
  [(.ofNat 104), (.negSucc 116), (.negSucc 115), (.negSucc 113), (.ofNat 101), (.ofNat 101), (.negSucc 53), (.ofNat 119), (.negSucc 115), (.ofNat 21), (.negSucc 100), (.negSucc 107), (.ofNat 92), (.negSucc 99), (.ofNat 124), (.ofNat 98)],
  [(.negSucc 86), (.ofNat 45), (.negSucc 71), (.ofNat 16), (.negSucc 125), (.negSucc 105), (.ofNat 87), (.ofNat 84), (.ofNat 73), (.ofNat 85), (.negSucc 104), (.ofNat 104), (.negSucc 101), (.negSucc 9), (.ofNat 25), (.ofNat 109)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 17 → ∀ b, b < 17 → answer a b = (a + b) % 17

end LeanCheckedNetwork.Net
