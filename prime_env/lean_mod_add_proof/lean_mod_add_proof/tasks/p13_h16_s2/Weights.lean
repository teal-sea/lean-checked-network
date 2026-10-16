import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 13

13 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=13 H=16 seed=2 lr=0.01 wd=0.2 train_fraction=0.9 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 13

def E1 : List (List Int) := [
  [(.negSucc 37), (.ofNat 67), (.negSucc 80), (.ofNat 58), (.negSucc 90), (.ofNat 54), (.ofNat 88), (.ofNat 19), (.negSucc 81), (.negSucc 74), (.ofNat 116), (.negSucc 83), (.ofNat 46), (.ofNat 102), (.ofNat 81), (.ofNat 75)],
  [(.ofNat 60), (.ofNat 116), (.ofNat 65), (.negSucc 100), (.ofNat 70), (.ofNat 76), (.ofNat 77), (.ofNat 56), (.negSucc 46), (.negSucc 67), (.ofNat 37), (.negSucc 35), (.ofNat 59), (.negSucc 91), (.ofNat 78), (.negSucc 90)],
  [(.ofNat 84), (.negSucc 23), (.ofNat 77), (.negSucc 43), (.ofNat 50), (.ofNat 63), (.ofNat 40), (.negSucc 91), (.ofNat 100), (.ofNat 69), (.negSucc 102), (.ofNat 65), (.negSucc 70), (.negSucc 16), (.ofNat 99), (.ofNat 64)],
  [(.ofNat 101), (.negSucc 126), (.negSucc 52), (.ofNat 97), (.negSucc 106), (.ofNat 42), (.negSucc 47), (.negSucc 22), (.ofNat 1), (.ofNat 82), (.negSucc 44), (.negSucc 67), (.ofNat 102), (.ofNat 107), (.ofNat 95), (.negSucc 49)],
  [(.ofNat 86), (.negSucc 0), (.negSucc 109), (.ofNat 80), (.ofNat 55), (.negSucc 69), (.negSucc 97), (.ofNat 98), (.negSucc 81), (.ofNat 22), (.ofNat 119), (.negSucc 65), (.negSucc 42), (.negSucc 58), (.ofNat 61), (.negSucc 63)],
  [(.ofNat 82), (.ofNat 103), (.ofNat 12), (.negSucc 46), (.ofNat 85), (.negSucc 94), (.negSucc 90), (.negSucc 82), (.ofNat 66), (.negSucc 76), (.ofNat 66), (.ofNat 85), (.negSucc 45), (.negSucc 75), (.negSucc 26), (.ofNat 75)],
  [(.ofNat 46), (.ofNat 40), (.ofNat 111), (.negSucc 98), (.negSucc 74), (.negSucc 39), (.negSucc 93), (.negSucc 50), (.ofNat 42), (.negSucc 78), (.negSucc 101), (.negSucc 9), (.ofNat 67), (.ofNat 87), (.negSucc 60), (.negSucc 80)],
  [(.ofNat 7), (.negSucc 106), (.ofNat 18), (.ofNat 69), (.negSucc 36), (.ofNat 71), (.negSucc 88), (.ofNat 99), (.negSucc 100), (.negSucc 61), (.negSucc 77), (.negSucc 91), (.negSucc 84), (.negSucc 38), (.negSucc 89), (.ofNat 61)],
  [(.negSucc 85), (.negSucc 64), (.negSucc 99), (.ofNat 97), (.ofNat 80), (.ofNat 88), (.negSucc 37), (.negSucc 1), (.ofNat 22), (.ofNat 49), (.ofNat 81), (.ofNat 78), (.ofNat 51), (.negSucc 86), (.negSucc 93), (.ofNat 59)],
  [(.negSucc 102), (.ofNat 93), (.negSucc 15), (.negSucc 15), (.negSucc 61), (.ofNat 58), (.ofNat 31), (.negSucc 92), (.ofNat 90), (.ofNat 81), (.ofNat 89), (.ofNat 78), (.ofNat 33), (.ofNat 79), (.negSucc 90), (.negSucc 80)],
  [(.negSucc 74), (.ofNat 87), (.ofNat 89), (.negSucc 113), (.negSucc 56), (.negSucc 59), (.ofNat 66), (.ofNat 80), (.negSucc 72), (.ofNat 78), (.negSucc 58), (.negSucc 63), (.negSucc 74), (.ofNat 36), (.negSucc 64), (.ofNat 83)],
  [(.negSucc 87), (.negSucc 76), (.ofNat 73), (.negSucc 7), (.ofNat 99), (.negSucc 74), (.ofNat 104), (.ofNat 35), (.negSucc 2), (.negSucc 20), (.negSucc 110), (.ofNat 72), (.ofNat 94), (.negSucc 103), (.negSucc 49), (.negSucc 83)],
  [(.negSucc 69), (.negSucc 108), (.negSucc 69), (.ofNat 90), (.ofNat 11), (.negSucc 67), (.ofNat 78), (.negSucc 86), (.ofNat 104), (.negSucc 87), (.ofNat 16), (.ofNat 91), (.negSucc 63), (.ofNat 65), (.ofNat 49), (.negSucc 11)]]

def E2 : List (List Int) := [
  [(.ofNat 92), (.negSucc 126), (.ofNat 77), (.ofNat 112), (.ofNat 54), (.negSucc 33), (.ofNat 80), (.ofNat 14), (.ofNat 77), (.ofNat 64), (.negSucc 20), (.negSucc 57), (.ofNat 99), (.ofNat 98), (.ofNat 70), (.negSucc 60)],
  [(.ofNat 62), (.ofNat 61), (.ofNat 55), (.ofNat 69), (.ofNat 67), (.negSucc 90), (.ofNat 81), (.negSucc 96), (.negSucc 78), (.negSucc 48), (.negSucc 110), (.negSucc 42), (.negSucc 62), (.negSucc 49), (.negSucc 41), (.negSucc 63)],
  [(.ofNat 69), (.ofNat 112), (.negSucc 53), (.negSucc 64), (.negSucc 111), (.negSucc 83), (.ofNat 83), (.ofNat 64), (.negSucc 38), (.negSucc 86), (.negSucc 25), (.ofNat 92), (.ofNat 51), (.negSucc 91), (.negSucc 60), (.ofNat 78)],
  [(.ofNat 26), (.negSucc 26), (.negSucc 108), (.negSucc 87), (.ofNat 19), (.ofNat 12), (.ofNat 106), (.ofNat 70), (.ofNat 98), (.negSucc 72), (.ofNat 124), (.ofNat 2), (.ofNat 77), (.ofNat 87), (.negSucc 87), (.negSucc 95)],
  [(.negSucc 78), (.negSucc 113), (.ofNat 65), (.ofNat 68), (.ofNat 104), (.ofNat 60), (.ofNat 74), (.negSucc 92), (.negSucc 21), (.negSucc 7), (.ofNat 67), (.negSucc 72), (.negSucc 82), (.negSucc 21), (.negSucc 92), (.ofNat 50)],
  [(.negSucc 95), (.ofNat 8), (.ofNat 66), (.ofNat 65), (.negSucc 62), (.ofNat 69), (.negSucc 10), (.negSucc 26), (.negSucc 63), (.ofNat 53), (.negSucc 98), (.ofNat 72), (.ofNat 55), (.negSucc 90), (.negSucc 72), (.ofNat 51)],
  [(.negSucc 95), (.ofNat 113), (.negSucc 64), (.ofNat 17), (.negSucc 51), (.ofNat 75), (.negSucc 55), (.ofNat 98), (.ofNat 92), (.ofNat 93), (.negSucc 70), (.ofNat 76), (.negSucc 48), (.ofNat 97), (.negSucc 90), (.negSucc 80)],
  [(.negSucc 79), (.ofNat 29), (.negSucc 110), (.negSucc 85), (.ofNat 101), (.negSucc 74), (.negSucc 95), (.negSucc 87), (.ofNat 2), (.negSucc 47), (.ofNat 112), (.negSucc 80), (.negSucc 71), (.ofNat 57), (.negSucc 19), (.ofNat 94)],
  [(.negSucc 63), (.negSucc 91), (.ofNat 63), (.negSucc 44), (.negSucc 34), (.negSucc 87), (.negSucc 95), (.negSucc 42), (.negSucc 84), (.negSucc 65), (.ofNat 77), (.ofNat 59), (.ofNat 89), (.negSucc 95), (.ofNat 32), (.negSucc 80)],
  [(.negSucc 51), (.negSucc 79), (.ofNat 107), (.ofNat 102), (.negSucc 74), (.negSucc 43), (.negSucc 75), (.ofNat 77), (.ofNat 58), (.negSucc 91), (.negSucc 64), (.ofNat 67), (.negSucc 84), (.ofNat 52), (.ofNat 74), (.ofNat 30)],
  [(.ofNat 49), (.ofNat 96), (.negSucc 41), (.ofNat 71), (.ofNat 97), (.ofNat 81), (.negSucc 85), (.negSucc 64), (.ofNat 86), (.negSucc 44), (.negSucc 104), (.negSucc 104), (.ofNat 64), (.ofNat 97), (.ofNat 107), (.ofNat 66)],
  [(.ofNat 89), (.ofNat 88), (.negSucc 83), (.negSucc 91), (.ofNat 17), (.ofNat 76), (.negSucc 37), (.negSucc 76), (.negSucc 99), (.ofNat 74), (.ofNat 54), (.negSucc 31), (.ofNat 60), (.negSucc 84), (.ofNat 89), (.negSucc 88)],
  [(.ofNat 89), (.negSucc 74), (.ofNat 60), (.negSucc 77), (.negSucc 103), (.ofNat 85), (.ofNat 45), (.ofNat 109), (.ofNat 15), (.ofNat 82), (.ofNat 84), (.ofNat 86), (.negSucc 67), (.negSucc 49), (.ofNat 78), (.ofNat 61)]]

def W2 : List (List Int) := [
  [(.negSucc 23), (.negSucc 93), (.negSucc 69), (.ofNat 80), (.negSucc 52), (.ofNat 70), (.ofNat 79), (.ofNat 64), (.negSucc 61), (.negSucc 34), (.negSucc 22), (.negSucc 6), (.ofNat 31), (.ofNat 61), (.ofNat 62), (.negSucc 82)],
  [(.ofNat 48), (.negSucc 79), (.ofNat 33), (.negSucc 20), (.negSucc 14), (.ofNat 3), (.ofNat 112), (.negSucc 54), (.negSucc 31), (.ofNat 52), (.negSucc 112), (.ofNat 72), (.ofNat 51), (.negSucc 90), (.ofNat 79), (.ofNat 26)],
  [(.ofNat 64), (.ofNat 54), (.ofNat 74), (.negSucc 95), (.ofNat 48), (.negSucc 66), (.ofNat 46), (.negSucc 63), (.ofNat 40), (.ofNat 70), (.negSucc 22), (.negSucc 69), (.negSucc 96), (.negSucc 20), (.ofNat 12), (.ofNat 30)],
  [(.ofNat 76), (.ofNat 51), (.negSucc 45), (.negSucc 14), (.negSucc 57), (.negSucc 90), (.ofNat 35), (.ofNat 40), (.negSucc 59), (.ofNat 24), (.ofNat 88), (.negSucc 64), (.ofNat 43), (.ofNat 57), (.negSucc 35), (.negSucc 85)],
  [(.ofNat 96), (.negSucc 61), (.negSucc 89), (.ofNat 105), (.negSucc 60), (.negSucc 19), (.ofNat 29), (.negSucc 2), (.negSucc 49), (.negSucc 20), (.ofNat 51), (.ofNat 91), (.negSucc 28), (.negSucc 79), (.negSucc 56), (.ofNat 97)],
  [(.ofNat 83), (.negSucc 88), (.ofNat 8), (.ofNat 43), (.ofNat 119), (.ofNat 60), (.negSucc 0), (.negSucc 63), (.ofNat 127), (.negSucc 70), (.negSucc 76), (.negSucc 0), (.ofNat 7), (.negSucc 7), (.negSucc 79), (.negSucc 36)],
  [(.ofNat 11), (.ofNat 37), (.ofNat 90), (.negSucc 83), (.negSucc 10), (.ofNat 93), (.negSucc 86), (.ofNat 49), (.negSucc 0), (.negSucc 40), (.negSucc 54), (.negSucc 73), (.ofNat 72), (.ofNat 86), (.negSucc 69), (.negSucc 32)],
  [(.negSucc 33), (.ofNat 127), (.ofNat 45), (.negSucc 17), (.negSucc 77), (.ofNat 38), (.negSucc 98), (.ofNat 0), (.negSucc 66), (.ofNat 18), (.ofNat 87), (.ofNat 48), (.negSucc 73), (.negSucc 39), (.negSucc 86), (.ofNat 58)],
  [(.negSucc 56), (.ofNat 0), (.negSucc 65), (.ofNat 77), (.ofNat 60), (.negSucc 21), (.negSucc 80), (.negSucc 60), (.ofNat 65), (.ofNat 90), (.ofNat 101), (.ofNat 27), (.ofNat 42), (.negSucc 63), (.negSucc 52), (.negSucc 69)],
  [(.negSucc 65), (.negSucc 91), (.negSucc 46), (.ofNat 34), (.ofNat 74), (.negSucc 66), (.negSucc 61), (.ofNat 69), (.ofNat 38), (.ofNat 74), (.negSucc 47), (.negSucc 52), (.ofNat 29), (.ofNat 96), (.ofNat 6), (.ofNat 64)],
  [(.negSucc 80), (.ofNat 22), (.ofNat 89), (.negSucc 54), (.negSucc 84), (.negSucc 66), (.ofNat 11), (.ofNat 118), (.negSucc 72), (.negSucc 6), (.negSucc 86), (.ofNat 66), (.negSucc 51), (.ofNat 59), (.ofNat 84), (.ofNat 40)],
  [(.negSucc 74), (.ofNat 93), (.ofNat 53), (.negSucc 84), (.ofNat 7), (.ofNat 33), (.ofNat 14), (.negSucc 70), (.ofNat 16), (.negSucc 75), (.ofNat 23), (.ofNat 47), (.ofNat 81), (.negSucc 88), (.ofNat 61), (.negSucc 48)],
  [(.negSucc 60), (.ofNat 31), (.negSucc 73), (.ofNat 33), (.ofNat 27), (.ofNat 42), (.ofNat 20), (.negSucc 52), (.ofNat 24), (.negSucc 81), (.ofNat 72), (.negSucc 78), (.negSucc 78), (.ofNat 38), (.ofNat 76), (.ofNat 49)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 13 → ∀ b, b < 13 → answer a b = (a + b) % 13

end LeanCheckedNetwork.Net
