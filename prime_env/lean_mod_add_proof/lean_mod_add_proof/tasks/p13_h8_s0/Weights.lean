import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 13

13 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=13 H=8 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 13

def E1 : List (List Int) := [
  [(.ofNat 42), (.ofNat 97), (.ofNat 109), (.negSucc 98), (.ofNat 120), (.negSucc 96), (.negSucc 116), (.ofNat 25)],
  [(.negSucc 77), (.negSucc 81), (.negSucc 116), (.negSucc 86), (.ofNat 86), (.negSucc 102), (.negSucc 89), (.negSucc 116)],
  [(.ofNat 87), (.negSucc 117), (.negSucc 83), (.ofNat 119), (.negSucc 116), (.negSucc 94), (.ofNat 59), (.ofNat 105)],
  [(.negSucc 90), (.negSucc 100), (.ofNat 127), (.negSucc 88), (.negSucc 76), (.negSucc 5), (.ofNat 103), (.ofNat 90)],
  [(.ofNat 104), (.ofNat 25), (.negSucc 78), (.negSucc 93), (.ofNat 98), (.ofNat 109), (.ofNat 76), (.negSucc 120)],
  [(.negSucc 105), (.ofNat 114), (.negSucc 94), (.ofNat 99), (.ofNat 94), (.ofNat 96), (.ofNat 83), (.negSucc 11)],
  [(.ofNat 115), (.ofNat 91), (.ofNat 106), (.negSucc 8), (.negSucc 88), (.ofNat 53), (.negSucc 115), (.ofNat 98)],
  [(.negSucc 116), (.ofNat 49), (.ofNat 68), (.negSucc 104), (.negSucc 109), (.negSucc 92), (.negSucc 81), (.negSucc 93)],
  [(.ofNat 112), (.negSucc 74), (.negSucc 114), (.ofNat 93), (.ofNat 46), (.negSucc 97), (.negSucc 107), (.negSucc 77)],
  [(.negSucc 81), (.negSucc 98), (.ofNat 70), (.ofNat 64), (.ofNat 118), (.negSucc 88), (.ofNat 14), (.ofNat 111)],
  [(.ofNat 59), (.negSucc 80), (.ofNat 90), (.negSucc 103), (.negSucc 9), (.ofNat 69), (.ofNat 113), (.negSucc 27)],
  [(.negSucc 67), (.ofNat 94), (.negSucc 105), (.negSucc 35), (.negSucc 118), (.ofNat 107), (.ofNat 88), (.negSucc 98)],
  [(.negSucc 21), (.ofNat 108), (.negSucc 54), (.ofNat 102), (.negSucc 65), (.ofNat 102), (.negSucc 91), (.ofNat 117)]]

def E2 : List (List Int) := [
  [(.negSucc 89), (.ofNat 98), (.ofNat 127), (.negSucc 86), (.negSucc 79), (.negSucc 34), (.negSucc 105), (.ofNat 88)],
  [(.ofNat 105), (.negSucc 25), (.negSucc 82), (.negSucc 92), (.ofNat 98), (.negSucc 102), (.negSucc 71), (.negSucc 121)],
  [(.negSucc 104), (.negSucc 119), (.negSucc 93), (.ofNat 100), (.ofNat 94), (.negSucc 92), (.negSucc 81), (.negSucc 5)],
  [(.ofNat 111), (.negSucc 92), (.ofNat 105), (.negSucc 5), (.negSucc 86), (.negSucc 42), (.ofNat 118), (.ofNat 96)],
  [(.negSucc 114), (.negSucc 58), (.ofNat 67), (.negSucc 104), (.negSucc 108), (.ofNat 83), (.ofNat 83), (.negSucc 94)],
  [(.ofNat 113), (.ofNat 85), (.negSucc 114), (.ofNat 92), (.ofNat 46), (.ofNat 98), (.ofNat 109), (.negSucc 75)],
  [(.negSucc 85), (.ofNat 102), (.ofNat 65), (.ofNat 64), (.ofNat 117), (.ofNat 87), (.negSucc 21), (.ofNat 111)],
  [(.ofNat 60), (.ofNat 86), (.ofNat 89), (.negSucc 102), (.negSucc 11), (.negSucc 65), (.negSucc 112), (.negSucc 29)],
  [(.negSucc 71), (.negSucc 101), (.negSucc 104), (.negSucc 33), (.negSucc 118), (.negSucc 106), (.negSucc 88), (.negSucc 96)],
  [(.negSucc 20), (.negSucc 108), (.negSucc 51), (.ofNat 101), (.negSucc 66), (.negSucc 94), (.ofNat 91), (.ofNat 116)],
  [(.ofNat 42), (.negSucc 101), (.ofNat 107), (.negSucc 98), (.ofNat 119), (.ofNat 89), (.ofNat 111), (.ofNat 19)],
  [(.negSucc 76), (.ofNat 90), (.negSucc 115), (.negSucc 86), (.ofNat 87), (.ofNat 104), (.ofNat 87), (.negSucc 116)],
  [(.ofNat 85), (.ofNat 121), (.negSucc 80), (.ofNat 117), (.negSucc 117), (.ofNat 94), (.negSucc 55), (.ofNat 106)]]

def W2 : List (List Int) := [
  [(.ofNat 72), (.ofNat 27), (.ofNat 104), (.negSucc 76), (.negSucc 87), (.negSucc 92), (.ofNat 55), (.negSucc 64)],
  [(.negSucc 17), (.negSucc 108), (.negSucc 80), (.ofNat 116), (.ofNat 98), (.negSucc 47), (.ofNat 88), (.negSucc 35)],
  [(.negSucc 14), (.negSucc 99), (.negSucc 82), (.negSucc 79), (.ofNat 82), (.ofNat 50), (.ofNat 63), (.ofNat 111)],
  [(.ofNat 25), (.negSucc 70), (.ofNat 101), (.negSucc 77), (.ofNat 43), (.ofNat 127), (.negSucc 37), (.negSucc 79)],
  [(.negSucc 23), (.ofNat 92), (.negSucc 9), (.ofNat 109), (.negSucc 112), (.ofNat 66), (.negSucc 101), (.negSucc 90)],
  [(.ofNat 73), (.ofNat 92), (.negSucc 105), (.negSucc 2), (.ofNat 21), (.negSucc 69), (.negSucc 86), (.ofNat 81)],
  [(.negSucc 102), (.ofNat 58), (.ofNat 56), (.negSucc 90), (.ofNat 107), (.negSucc 99), (.ofNat 25), (.ofNat 21)],
  [(.ofNat 77), (.negSucc 34), (.ofNat 12), (.ofNat 15), (.ofNat 85), (.negSucc 58), (.ofNat 70), (.negSucc 106)],
  [(.negSucc 104), (.negSucc 104), (.negSucc 109), (.ofNat 69), (.negSucc 68), (.ofNat 18), (.ofNat 103), (.ofNat 93)],
  [(.ofNat 83), (.negSucc 78), (.negSucc 14), (.negSucc 110), (.negSucc 22), (.ofNat 116), (.negSucc 50), (.ofNat 85)],
  [(.negSucc 101), (.ofNat 38), (.ofNat 92), (.negSucc 0), (.ofNat 89), (.ofNat 90), (.negSucc 115), (.negSucc 101)],
  [(.ofNat 71), (.ofNat 45), (.negSucc 101), (.ofNat 104), (.ofNat 54), (.ofNat 17), (.negSucc 79), (.negSucc 36)],
  [(.negSucc 10), (.ofNat 116), (.ofNat 9), (.negSucc 86), (.negSucc 14), (.negSucc 117), (.negSucc 42), (.ofNat 110)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 13 → ∀ b, b < 13 → answer a b = (a + b) % 13

end LeanCheckedNetwork.Net
