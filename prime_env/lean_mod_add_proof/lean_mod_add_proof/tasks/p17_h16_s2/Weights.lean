import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 17

17 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=17 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 17

def E1 : List (List Int) := [
  [(.ofNat 19), (.ofNat 106), (.ofNat 31), (.negSucc 110), (.negSucc 87), (.negSucc 100), (.ofNat 82), (.negSucc 106), (.negSucc 103), (.ofNat 12), (.negSucc 96), (.negSucc 111), (.negSucc 100), (.negSucc 96), (.negSucc 96), (.ofNat 71)],
  [(.negSucc 90), (.negSucc 94), (.ofNat 46), (.negSucc 96), (.ofNat 108), (.ofNat 105), (.negSucc 110), (.negSucc 108), (.negSucc 91), (.negSucc 47), (.negSucc 111), (.ofNat 27), (.negSucc 86), (.ofNat 103), (.ofNat 102), (.negSucc 111)],
  [(.ofNat 95), (.negSucc 106), (.negSucc 92), (.negSucc 78), (.ofNat 91), (.negSucc 90), (.ofNat 40), (.ofNat 15), (.ofNat 122), (.negSucc 66), (.negSucc 86), (.ofNat 91), (.ofNat 98), (.negSucc 99), (.negSucc 88), (.negSucc 95)],
  [(.negSucc 79), (.ofNat 93), (.ofNat 100), (.negSucc 59), (.negSucc 95), (.ofNat 71), (.ofNat 91), (.ofNat 108), (.ofNat 94), (.negSucc 84), (.ofNat 88), (.negSucc 110), (.ofNat 105), (.ofNat 111), (.ofNat 114), (.negSucc 72)],
  [(.negSucc 72), (.ofNat 63), (.negSucc 97), (.ofNat 125), (.negSucc 95), (.negSucc 3), (.negSucc 107), (.ofNat 90), (.negSucc 126), (.negSucc 88), (.ofNat 95), (.ofNat 60), (.ofNat 71), (.negSucc 89), (.negSucc 52), (.ofNat 117)],
  [(.ofNat 105), (.negSucc 98), (.ofNat 106), (.ofNat 95), (.ofNat 42), (.negSucc 34), (.ofNat 85), (.negSucc 46), (.negSucc 85), (.negSucc 95), (.ofNat 83), (.ofNat 94), (.negSucc 107), (.ofNat 91), (.negSucc 10), (.ofNat 101)],
  [(.negSucc 105), (.ofNat 15), (.negSucc 19), (.ofNat 88), (.ofNat 101), (.ofNat 93), (.ofNat 85), (.negSucc 94), (.ofNat 102), (.negSucc 99), (.negSucc 117), (.negSucc 110), (.negSucc 100), (.negSucc 98), (.ofNat 60), (.ofNat 80)],
  [(.negSucc 73), (.ofNat 124), (.negSucc 100), (.ofNat 81), (.negSucc 22), (.negSucc 80), (.negSucc 99), (.negSucc 86), (.ofNat 91), (.negSucc 107), (.negSucc 103), (.ofNat 91), (.ofNat 38), (.ofNat 95), (.negSucc 101), (.negSucc 115)],
  [(.ofNat 108), (.negSucc 96), (.ofNat 88), (.negSucc 45), (.negSucc 105), (.ofNat 97), (.ofNat 108), (.ofNat 67), (.negSucc 95), (.negSucc 74), (.negSucc 65), (.ofNat 53), (.ofNat 102), (.negSucc 95), (.ofNat 92), (.negSucc 98)],
  [(.negSucc 120), (.negSucc 81), (.negSucc 98), (.negSucc 115), (.negSucc 34), (.negSucc 85), (.ofNat 60), (.ofNat 96), (.negSucc 93), (.negSucc 44), (.ofNat 99), (.negSucc 93), (.ofNat 89), (.ofNat 91), (.negSucc 96), (.ofNat 26)],
  [(.negSucc 4), (.ofNat 105), (.ofNat 104), (.negSucc 93), (.ofNat 113), (.ofNat 104), (.negSucc 79), (.ofNat 86), (.ofNat 53), (.ofNat 26), (.ofNat 105), (.ofNat 109), (.negSucc 98), (.negSucc 89), (.ofNat 89), (.ofNat 115)],
  [(.ofNat 104), (.negSucc 54), (.negSucc 62), (.negSucc 97), (.ofNat 77), (.negSucc 106), (.ofNat 116), (.negSucc 73), (.ofNat 104), (.ofNat 110), (.ofNat 50), (.negSucc 71), (.negSucc 95), (.ofNat 108), (.ofNat 64), (.ofNat 101)],
  [(.negSucc 109), (.negSucc 110), (.negSucc 73), (.ofNat 52), (.negSucc 113), (.ofNat 98), (.negSucc 86), (.negSucc 101), (.negSucc 79), (.ofNat 93), (.negSucc 116), (.negSucc 82), (.negSucc 81), (.negSucc 81), (.negSucc 90), (.negSucc 48)],
  [(.ofNat 84), (.ofNat 55), (.ofNat 99), (.ofNat 101), (.negSucc 79), (.negSucc 99), (.negSucc 87), (.negSucc 61), (.negSucc 111), (.ofNat 104), (.negSucc 112), (.ofNat 114), (.ofNat 96), (.ofNat 76), (.ofNat 99), (.negSucc 108)],
  [(.ofNat 41), (.ofNat 98), (.negSucc 91), (.ofNat 103), (.ofNat 95), (.ofNat 94), (.ofNat 103), (.ofNat 109), (.negSucc 18), (.ofNat 105), (.ofNat 51), (.negSucc 87), (.ofNat 102), (.negSucc 69), (.negSucc 110), (.negSucc 91)],
  [(.negSucc 100), (.negSucc 101), (.ofNat 97), (.ofNat 90), (.ofNat 62), (.negSucc 81), (.negSucc 94), (.ofNat 97), (.ofNat 104), (.ofNat 105), (.ofNat 101), (.negSucc 86), (.ofNat 62), (.negSucc 35), (.ofNat 50), (.ofNat 99)],
  [(.ofNat 95), (.negSucc 50), (.negSucc 82), (.ofNat 25), (.negSucc 115), (.ofNat 97), (.negSucc 87), (.ofNat 45), (.ofNat 67), (.ofNat 107), (.ofNat 104), (.ofNat 105), (.negSucc 108), (.ofNat 57), (.ofNat 91), (.ofNat 100)]]

def E2 : List (List Int) := [
  [(.negSucc 4), (.ofNat 105), (.ofNat 104), (.negSucc 93), (.ofNat 113), (.ofNat 104), (.negSucc 79), (.ofNat 86), (.ofNat 53), (.ofNat 26), (.negSucc 104), (.ofNat 109), (.ofNat 99), (.negSucc 89), (.ofNat 89), (.ofNat 115)],
  [(.ofNat 104), (.negSucc 54), (.negSucc 62), (.negSucc 97), (.ofNat 77), (.negSucc 106), (.ofNat 116), (.negSucc 73), (.ofNat 104), (.ofNat 110), (.negSucc 49), (.negSucc 71), (.ofNat 96), (.ofNat 108), (.ofNat 64), (.ofNat 101)],
  [(.negSucc 109), (.negSucc 110), (.negSucc 73), (.ofNat 52), (.negSucc 113), (.ofNat 98), (.negSucc 86), (.negSucc 101), (.negSucc 79), (.ofNat 93), (.ofNat 117), (.negSucc 82), (.ofNat 82), (.negSucc 81), (.negSucc 90), (.negSucc 48)],
  [(.ofNat 84), (.ofNat 55), (.ofNat 99), (.ofNat 101), (.negSucc 79), (.negSucc 99), (.negSucc 87), (.negSucc 61), (.negSucc 111), (.ofNat 104), (.ofNat 113), (.ofNat 114), (.negSucc 95), (.ofNat 76), (.ofNat 99), (.negSucc 108)],
  [(.ofNat 41), (.ofNat 98), (.negSucc 91), (.ofNat 103), (.ofNat 95), (.ofNat 94), (.ofNat 103), (.ofNat 109), (.negSucc 18), (.ofNat 105), (.negSucc 50), (.negSucc 87), (.negSucc 101), (.negSucc 69), (.negSucc 110), (.negSucc 91)],
  [(.negSucc 100), (.negSucc 101), (.ofNat 97), (.ofNat 90), (.ofNat 62), (.negSucc 81), (.negSucc 94), (.ofNat 97), (.ofNat 104), (.ofNat 105), (.negSucc 100), (.negSucc 86), (.negSucc 61), (.negSucc 35), (.ofNat 50), (.ofNat 99)],
  [(.ofNat 95), (.negSucc 50), (.negSucc 82), (.ofNat 25), (.negSucc 115), (.ofNat 97), (.negSucc 87), (.ofNat 45), (.ofNat 67), (.ofNat 107), (.negSucc 103), (.ofNat 105), (.ofNat 109), (.ofNat 57), (.ofNat 91), (.ofNat 100)],
  [(.ofNat 19), (.ofNat 106), (.ofNat 31), (.negSucc 110), (.negSucc 87), (.negSucc 100), (.ofNat 82), (.negSucc 106), (.negSucc 103), (.ofNat 12), (.ofNat 97), (.negSucc 111), (.ofNat 101), (.negSucc 96), (.negSucc 96), (.ofNat 71)],
  [(.negSucc 90), (.negSucc 94), (.ofNat 46), (.negSucc 96), (.ofNat 108), (.ofNat 105), (.negSucc 110), (.negSucc 108), (.negSucc 91), (.negSucc 47), (.ofNat 112), (.ofNat 27), (.ofNat 87), (.ofNat 103), (.ofNat 102), (.negSucc 111)],
  [(.ofNat 95), (.negSucc 106), (.negSucc 92), (.negSucc 78), (.ofNat 91), (.negSucc 90), (.ofNat 40), (.ofNat 15), (.ofNat 122), (.negSucc 66), (.ofNat 87), (.ofNat 91), (.negSucc 97), (.negSucc 99), (.negSucc 88), (.negSucc 95)],
  [(.negSucc 79), (.ofNat 93), (.ofNat 100), (.negSucc 59), (.negSucc 95), (.ofNat 71), (.ofNat 91), (.ofNat 108), (.ofNat 94), (.negSucc 84), (.negSucc 87), (.negSucc 110), (.negSucc 104), (.ofNat 111), (.ofNat 114), (.negSucc 72)],
  [(.negSucc 72), (.ofNat 63), (.negSucc 97), (.ofNat 125), (.negSucc 95), (.negSucc 3), (.negSucc 107), (.ofNat 90), (.negSucc 126), (.negSucc 88), (.negSucc 94), (.ofNat 60), (.negSucc 70), (.negSucc 89), (.negSucc 52), (.ofNat 117)],
  [(.ofNat 105), (.negSucc 98), (.ofNat 106), (.ofNat 95), (.ofNat 42), (.negSucc 34), (.ofNat 85), (.negSucc 46), (.negSucc 85), (.negSucc 95), (.negSucc 82), (.ofNat 94), (.ofNat 108), (.ofNat 91), (.negSucc 10), (.ofNat 101)],
  [(.negSucc 105), (.ofNat 15), (.negSucc 19), (.ofNat 88), (.ofNat 101), (.ofNat 93), (.ofNat 85), (.negSucc 94), (.ofNat 102), (.negSucc 99), (.ofNat 118), (.negSucc 110), (.ofNat 101), (.negSucc 98), (.ofNat 60), (.ofNat 80)],
  [(.negSucc 73), (.ofNat 124), (.negSucc 100), (.ofNat 81), (.negSucc 22), (.negSucc 80), (.negSucc 99), (.negSucc 86), (.ofNat 91), (.negSucc 107), (.ofNat 104), (.ofNat 91), (.negSucc 37), (.ofNat 95), (.negSucc 101), (.negSucc 115)],
  [(.ofNat 108), (.negSucc 96), (.ofNat 88), (.negSucc 45), (.negSucc 105), (.ofNat 97), (.ofNat 108), (.ofNat 67), (.negSucc 95), (.negSucc 74), (.ofNat 66), (.ofNat 53), (.negSucc 101), (.negSucc 95), (.ofNat 92), (.negSucc 98)],
  [(.negSucc 120), (.negSucc 81), (.negSucc 98), (.negSucc 115), (.negSucc 34), (.negSucc 85), (.ofNat 60), (.ofNat 96), (.negSucc 93), (.negSucc 44), (.negSucc 98), (.negSucc 93), (.negSucc 88), (.ofNat 91), (.negSucc 96), (.ofNat 26)]]

def W2 : List (List Int) := [
  [(.ofNat 114), (.ofNat 108), (.negSucc 50), (.ofNat 66), (.negSucc 87), (.negSucc 90), (.negSucc 72), (.negSucc 88), (.ofNat 7), (.ofNat 109), (.ofNat 63), (.negSucc 72), (.negSucc 72), (.ofNat 103), (.negSucc 99), (.ofNat 25)],
  [(.negSucc 80), (.negSucc 50), (.ofNat 81), (.ofNat 102), (.ofNat 53), (.ofNat 101), (.ofNat 96), (.ofNat 37), (.negSucc 113), (.ofNat 89), (.ofNat 71), (.negSucc 31), (.negSucc 81), (.negSucc 93), (.negSucc 45), (.negSucc 59)],
  [(.negSucc 13), (.negSucc 113), (.negSucc 89), (.ofNat 86), (.ofNat 103), (.negSucc 72), (.negSucc 84), (.ofNat 78), (.negSucc 27), (.ofNat 86), (.ofNat 61), (.ofNat 105), (.negSucc 27), (.ofNat 95), (.negSucc 18), (.negSucc 118)],
  [(.ofNat 87), (.ofNat 55), (.ofNat 85), (.negSucc 43), (.negSucc 82), (.ofNat 101), (.negSucc 6), (.ofNat 88), (.ofNat 100), (.ofNat 62), (.negSucc 112), (.negSucc 103), (.ofNat 79), (.negSucc 105), (.negSucc 74), (.negSucc 82)],
  [(.negSucc 115), (.ofNat 104), (.negSucc 76), (.negSucc 57), (.negSucc 116), (.negSucc 74), (.ofNat 99), (.negSucc 28), (.ofNat 14), (.ofNat 80), (.negSucc 101), (.negSucc 15), (.ofNat 110), (.ofNat 88), (.ofNat 92), (.ofNat 15)],
  [(.ofNat 75), (.negSucc 99), (.ofNat 76), (.negSucc 108), (.ofNat 61), (.ofNat 87), (.negSucc 78), (.negSucc 88), (.negSucc 94), (.ofNat 53), (.negSucc 3), (.ofNat 94), (.ofNat 70), (.negSucc 85), (.negSucc 98), (.ofNat 101)],
  [(.ofNat 99), (.negSucc 14), (.ofNat 96), (.negSucc 96), (.ofNat 127), (.negSucc 53), (.ofNat 63), (.negSucc 95), (.negSucc 80), (.negSucc 71), (.ofNat 114), (.negSucc 107), (.negSucc 125), (.ofNat 93), (.negSucc 35), (.ofNat 67)],
  [(.negSucc 108), (.ofNat 123), (.negSucc 106), (.negSucc 37), (.ofNat 36), (.ofNat 52), (.ofNat 89), (.ofNat 58), (.ofNat 61), (.negSucc 76), (.ofNat 92), (.ofNat 80), (.negSucc 102), (.negSucc 75), (.ofNat 22), (.negSucc 102)],
  [(.ofNat 44), (.negSucc 44), (.ofNat 86), (.ofNat 65), (.negSucc 124), (.ofNat 40), (.negSucc 116), (.ofNat 111), (.ofNat 98), (.negSucc 105), (.ofNat 11), (.ofNat 92), (.ofNat 30), (.ofNat 62), (.negSucc 106), (.negSucc 103)],
  [(.ofNat 70), (.negSucc 83), (.negSucc 97), (.ofNat 94), (.ofNat 38), (.ofNat 33), (.ofNat 87), (.ofNat 92), (.negSucc 72), (.negSucc 102), (.negSucc 116), (.negSucc 100), (.ofNat 119), (.negSucc 32), (.ofNat 101), (.negSucc 25)],
  [(.negSucc 95), (.ofNat 95), (.ofNat 20), (.ofNat 93), (.ofNat 124), (.ofNat 58), (.ofNat 88), (.negSucc 115), (.negSucc 83), (.negSucc 119), (.negSucc 99), (.ofNat 70), (.ofNat 66), (.negSucc 40), (.negSucc 84), (.ofNat 12)],
  [(.ofNat 88), (.ofNat 21), (.negSucc 66), (.ofNat 43), (.ofNat 32), (.negSucc 89), (.negSucc 108), (.negSucc 104), (.ofNat 27), (.negSucc 117), (.ofNat 12), (.ofNat 62), (.ofNat 15), (.ofNat 46), (.ofNat 115), (.ofNat 102)],
  [(.ofNat 18), (.negSucc 107), (.negSucc 55), (.negSucc 44), (.negSucc 108), (.ofNat 110), (.ofNat 99), (.negSucc 71), (.ofNat 101), (.ofNat 57), (.ofNat 108), (.negSucc 92), (.negSucc 97), (.ofNat 28), (.negSucc 99), (.ofNat 73)],
  [(.negSucc 91), (.ofNat 28), (.ofNat 109), (.negSucc 112), (.negSucc 55), (.negSucc 110), (.ofNat 58), (.ofNat 102), (.negSucc 39), (.ofNat 59), (.ofNat 93), (.ofNat 106), (.negSucc 75), (.ofNat 115), (.negSucc 31), (.negSucc 117)],
  [(.ofNat 111), (.ofNat 116), (.negSucc 100), (.negSucc 85), (.ofNat 43), (.ofNat 89), (.negSucc 92), (.ofNat 88), (.negSucc 106), (.ofNat 97), (.negSucc 44), (.negSucc 5), (.ofNat 36), (.negSucc 71), (.ofNat 46), (.negSucc 90)],
  [(.negSucc 12), (.negSucc 86), (.ofNat 95), (.negSucc 52), (.ofNat 79), (.negSucc 113), (.ofNat 95), (.ofNat 81), (.negSucc 14), (.ofNat 98), (.negSucc 104), (.negSucc 107), (.ofNat 104), (.ofNat 105), (.negSucc 111), (.negSucc 31)],
  [(.negSucc 69), (.negSucc 23), (.negSucc 47), (.ofNat 46), (.negSucc 103), (.ofNat 103), (.negSucc 26), (.negSucc 100), (.ofNat 95), (.ofNat 72), (.negSucc 72), (.ofNat 97), (.ofNat 82), (.negSucc 104), (.ofNat 85), (.ofNat 6)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 17 → ∀ b, b < 17 → answer a b = (a + b) % 17

end LeanCheckedNetwork.Net
