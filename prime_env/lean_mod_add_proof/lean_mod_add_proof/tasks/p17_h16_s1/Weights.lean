import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 17

17 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=17 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 17

def E1 : List (List Int) := [
  [(.ofNat 69), (.negSucc 119), (.negSucc 20), (.negSucc 126), (.ofNat 108), (.negSucc 8), (.negSucc 80), (.negSucc 111), (.ofNat 97), (.negSucc 86), (.ofNat 109), (.ofNat 120), (.ofNat 14), (.negSucc 39), (.negSucc 27), (.ofNat 44)],
  [(.negSucc 118), (.negSucc 30), (.ofNat 14), (.negSucc 122), (.ofNat 58), (.negSucc 105), (.ofNat 81), (.ofNat 98), (.negSucc 85), (.ofNat 108), (.ofNat 89), (.negSucc 44), (.negSucc 96), (.negSucc 118), (.negSucc 69), (.ofNat 111)],
  [(.ofNat 6), (.ofNat 122), (.ofNat 35), (.negSucc 100), (.negSucc 106), (.negSucc 26), (.ofNat 105), (.ofNat 93), (.ofNat 96), (.negSucc 66), (.ofNat 39), (.negSucc 111), (.ofNat 101), (.negSucc 107), (.negSucc 100), (.ofNat 92)],
  [(.ofNat 119), (.negSucc 28), (.negSucc 65), (.negSucc 95), (.negSucc 104), (.ofNat 105), (.ofNat 61), (.negSucc 108), (.negSucc 97), (.negSucc 69), (.negSucc 98), (.ofNat 5), (.negSucc 105), (.negSucc 109), (.negSucc 91), (.negSucc 60)],
  [(.negSucc 80), (.negSucc 107), (.ofNat 31), (.negSucc 23), (.negSucc 48), (.ofNat 45), (.negSucc 71), (.ofNat 95), (.ofNat 89), (.ofNat 101), (.negSucc 84), (.ofNat 113), (.ofNat 88), (.negSucc 9), (.negSucc 111), (.negSucc 109)],
  [(.negSucc 82), (.ofNat 96), (.negSucc 102), (.ofNat 71), (.ofNat 116), (.negSucc 105), (.negSucc 111), (.ofNat 83), (.negSucc 100), (.negSucc 97), (.ofNat 55), (.ofNat 84), (.ofNat 97), (.ofNat 106), (.negSucc 111), (.negSucc 79)],
  [(.ofNat 112), (.ofNat 72), (.ofNat 101), (.ofNat 74), (.ofNat 92), (.negSucc 81), (.negSucc 64), (.negSucc 100), (.ofNat 104), (.ofNat 17), (.ofNat 109), (.negSucc 92), (.negSucc 94), (.ofNat 108), (.negSucc 93), (.ofNat 101)],
  [(.ofNat 13), (.negSucc 121), (.negSucc 102), (.ofNat 90), (.ofNat 7), (.ofNat 100), (.ofNat 97), (.ofNat 102), (.negSucc 82), (.ofNat 95), (.ofNat 78), (.negSucc 83), (.ofNat 108), (.ofNat 93), (.negSucc 67), (.ofNat 107)],
  [(.negSucc 123), (.ofNat 4), (.ofNat 110), (.ofNat 100), (.negSucc 107), (.ofNat 87), (.ofNat 108), (.negSucc 51), (.ofNat 88), (.negSucc 104), (.negSucc 71), (.ofNat 91), (.negSucc 110), (.ofNat 18), (.negSucc 45), (.ofNat 70)],
  [(.ofNat 65), (.ofNat 111), (.negSucc 103), (.ofNat 117), (.negSucc 99), (.negSucc 88), (.ofNat 1), (.negSucc 84), (.negSucc 19), (.ofNat 104), (.negSucc 104), (.ofNat 102), (.ofNat 106), (.negSucc 87), (.ofNat 44), (.negSucc 104)],
  [(.ofNat 94), (.negSucc 83), (.ofNat 106), (.ofNat 94), (.ofNat 32), (.negSucc 102), (.negSucc 108), (.ofNat 102), (.ofNat 7), (.ofNat 72), (.negSucc 41), (.negSucc 73), (.ofNat 41), (.negSucc 104), (.ofNat 77), (.negSucc 99)],
  [(.negSucc 113), (.negSucc 78), (.negSucc 86), (.ofNat 90), (.ofNat 120), (.ofNat 85), (.negSucc 92), (.negSucc 81), (.negSucc 3), (.negSucc 99), (.ofNat 99), (.negSucc 92), (.negSucc 71), (.negSucc 87), (.ofNat 97), (.negSucc 15)],
  [(.negSucc 39), (.ofNat 124), (.ofNat 109), (.ofNat 72), (.ofNat 91), (.ofNat 112), (.ofNat 31), (.negSucc 43), (.negSucc 107), (.ofNat 95), (.ofNat 101), (.ofNat 89), (.ofNat 104), (.negSucc 17), (.ofNat 109), (.ofNat 110)],
  [(.ofNat 121), (.ofNat 33), (.negSucc 87), (.negSucc 9), (.negSucc 68), (.negSucc 71), (.ofNat 110), (.ofNat 91), (.ofNat 108), (.negSucc 31), (.ofNat 42), (.ofNat 109), (.negSucc 90), (.ofNat 60), (.ofNat 124), (.ofNat 102)],
  [(.negSucc 32), (.negSucc 105), (.ofNat 85), (.negSucc 63), (.negSucc 110), (.negSucc 113), (.ofNat 78), (.negSucc 103), (.negSucc 95), (.negSucc 99), (.negSucc 83), (.negSucc 53), (.ofNat 110), (.ofNat 92), (.ofNat 109), (.ofNat 29)],
  [(.negSucc 100), (.ofNat 69), (.negSucc 84), (.negSucc 64), (.negSucc 84), (.ofNat 26), (.negSucc 48), (.ofNat 45), (.ofNat 105), (.ofNat 103), (.negSucc 115), (.negSucc 118), (.negSucc 123), (.ofNat 99), (.ofNat 105), (.negSucc 111)],
  [(.ofNat 97), (.ofNat 103), (.ofNat 90), (.negSucc 105), (.ofNat 79), (.ofNat 115), (.negSucc 114), (.ofNat 109), (.negSucc 116), (.negSucc 16), (.negSucc 49), (.ofNat 58), (.negSucc 77), (.ofNat 80), (.ofNat 85), (.negSucc 95)]]

def E2 : List (List Int) := [
  [(.ofNat 117), (.ofNat 2), (.negSucc 97), (.negSucc 99), (.ofNat 119), (.ofNat 110), (.negSucc 87), (.negSucc 94), (.negSucc 84), (.ofNat 78), (.negSucc 82), (.negSucc 28), (.negSucc 98), (.negSucc 107), (.ofNat 47), (.negSucc 45)],
  [(.negSucc 60), (.ofNat 119), (.ofNat 96), (.negSucc 87), (.ofNat 72), (.ofNat 44), (.ofNat 85), (.ofNat 105), (.ofNat 62), (.ofNat 85), (.negSucc 119), (.negSucc 114), (.ofNat 102), (.negSucc 103), (.ofNat 87), (.negSucc 105)],
  [(.negSucc 124), (.negSucc 71), (.negSucc 96), (.negSucc 64), (.negSucc 101), (.negSucc 125), (.ofNat 110), (.negSucc 97), (.negSucc 33), (.negSucc 117), (.ofNat 45), (.ofNat 11), (.negSucc 77), (.negSucc 99), (.ofNat 121), (.negSucc 123)],
  [(.ofNat 93), (.negSucc 97), (.ofNat 108), (.negSucc 48), (.negSucc 118), (.negSucc 56), (.ofNat 74), (.negSucc 62), (.negSucc 86), (.ofNat 97), (.ofNat 99), (.ofNat 121), (.ofNat 102), (.negSucc 20), (.ofNat 127), (.ofNat 42)],
  [(.ofNat 69), (.ofNat 98), (.negSucc 105), (.ofNat 77), (.negSucc 26), (.ofNat 123), (.negSucc 91), (.ofNat 111), (.ofNat 76), (.ofNat 38), (.ofNat 94), (.ofNat 53), (.ofNat 66), (.ofNat 116), (.ofNat 104), (.ofNat 104)],
  [(.negSucc 110), (.ofNat 16), (.ofNat 115), (.ofNat 93), (.ofNat 85), (.ofNat 73), (.negSucc 108), (.negSucc 92), (.negSucc 77), (.negSucc 97), (.negSucc 73), (.negSucc 107), (.negSucc 89), (.ofNat 120), (.ofNat 77), (.ofNat 105)],
  [(.ofNat 18), (.negSucc 122), (.negSucc 125), (.ofNat 106), (.ofNat 118), (.negSucc 114), (.negSucc 51), (.ofNat 19), (.ofNat 100), (.ofNat 115), (.negSucc 111), (.negSucc 39), (.ofNat 91), (.ofNat 86), (.ofNat 72), (.negSucc 79)],
  [(.ofNat 119), (.ofNat 39), (.ofNat 119), (.ofNat 116), (.ofNat 19), (.negSucc 63), (.ofNat 81), (.ofNat 100), (.negSucc 103), (.negSucc 76), (.negSucc 105), (.ofNat 121), (.negSucc 94), (.ofNat 55), (.ofNat 41), (.negSucc 108)],
  [(.negSucc 75), (.ofNat 115), (.negSucc 109), (.ofNat 115), (.negSucc 91), (.ofNat 106), (.ofNat 115), (.negSucc 102), (.ofNat 98), (.negSucc 93), (.ofNat 80), (.ofNat 92), (.ofNat 97), (.negSucc 80), (.negSucc 62), (.negSucc 77)],
  [(.negSucc 109), (.negSucc 96), (.ofNat 104), (.ofNat 87), (.negSucc 88), (.ofNat 80), (.ofNat 15), (.ofNat 72), (.negSucc 101), (.ofNat 113), (.ofNat 109), (.negSucc 88), (.ofNat 30), (.negSucc 117), (.negSucc 77), (.ofNat 81)],
  [(.ofNat 108), (.negSucc 86), (.negSucc 75), (.ofNat 86), (.ofNat 14), (.negSucc 95), (.negSucc 96), (.ofNat 102), (.ofNat 108), (.negSucc 83), (.ofNat 113), (.negSucc 76), (.negSucc 53), (.negSucc 104), (.negSucc 101), (.ofNat 113)],
  [(.ofNat 11), (.ofNat 122), (.negSucc 20), (.ofNat 77), (.ofNat 97), (.negSucc 92), (.negSucc 106), (.negSucc 126), (.negSucc 115), (.negSucc 71), (.negSucc 80), (.ofNat 102), (.ofNat 93), (.negSucc 98), (.negSucc 114), (.ofNat 10)],
  [(.negSucc 125), (.negSucc 22), (.ofNat 24), (.ofNat 9), (.ofNat 96), (.ofNat 93), (.ofNat 22), (.ofNat 96), (.ofNat 112), (.ofNat 111), (.negSucc 113), (.ofNat 85), (.negSucc 91), (.ofNat 80), (.negSucc 115), (.negSucc 88)],
  [(.ofNat 48), (.negSucc 115), (.negSucc 94), (.negSucc 79), (.negSucc 62), (.ofNat 103), (.ofNat 102), (.ofNat 86), (.negSucc 104), (.negSucc 92), (.negSucc 68), (.negSucc 79), (.ofNat 103), (.ofNat 115), (.negSucc 105), (.negSucc 108)],
  [(.ofNat 110), (.ofNat 78), (.ofNat 89), (.negSucc 102), (.negSucc 106), (.negSucc 73), (.ofNat 116), (.negSucc 97), (.ofNat 116), (.negSucc 9), (.ofNat 76), (.negSucc 114), (.negSucc 76), (.ofNat 106), (.negSucc 100), (.ofNat 24)],
  [(.negSucc 100), (.ofNat 85), (.negSucc 84), (.negSucc 119), (.negSucc 61), (.negSucc 113), (.negSucc 40), (.ofNat 124), (.negSucc 123), (.ofNat 101), (.ofNat 113), (.ofNat 79), (.negSucc 56), (.ofNat 90), (.negSucc 55), (.ofNat 94)],
  [(.negSucc 50), (.negSucc 110), (.ofNat 111), (.negSucc 109), (.ofNat 85), (.negSucc 17), (.negSucc 112), (.negSucc 40), (.ofNat 109), (.negSucc 104), (.negSucc 46), (.ofNat 118), (.ofNat 102), (.negSucc 31), (.ofNat 3), (.ofNat 108)]]

def W2 : List (List Int) := [
  [(.ofNat 19), (.ofNat 51), (.ofNat 92), (.ofNat 103), (.ofNat 77), (.negSucc 78), (.negSucc 108), (.ofNat 113), (.negSucc 112), (.negSucc 114), (.negSucc 115), (.negSucc 96), (.negSucc 48), (.negSucc 40), (.ofNat 117), (.ofNat 92)],
  [(.negSucc 98), (.negSucc 93), (.negSucc 65), (.ofNat 94), (.ofNat 61), (.negSucc 91), (.negSucc 100), (.negSucc 113), (.ofNat 92), (.ofNat 87), (.negSucc 96), (.negSucc 100), (.ofNat 54), (.ofNat 70), (.ofNat 99), (.ofNat 75)],
  [(.negSucc 32), (.negSucc 25), (.ofNat 84), (.ofNat 106), (.negSucc 117), (.ofNat 44), (.negSucc 86), (.negSucc 4), (.negSucc 46), (.ofNat 82), (.negSucc 84), (.ofNat 98), (.negSucc 99), (.ofNat 119), (.ofNat 99), (.negSucc 111)],
  [(.ofNat 94), (.ofNat 90), (.negSucc 46), (.negSucc 37), (.negSucc 100), (.ofNat 72), (.negSucc 11), (.ofNat 47), (.ofNat 14), (.negSucc 105), (.negSucc 9), (.ofNat 75), (.ofNat 33), (.ofNat 49), (.negSucc 42), (.negSucc 98)],
  [(.negSucc 111), (.negSucc 103), (.negSucc 2), (.negSucc 80), (.negSucc 16), (.ofNat 106), (.ofNat 100), (.negSucc 113), (.ofNat 19), (.ofNat 111), (.ofNat 92), (.ofNat 93), (.negSucc 60), (.ofNat 86), (.negSucc 102), (.ofNat 20)],
  [(.negSucc 93), (.negSucc 91), (.ofNat 12), (.negSucc 33), (.ofNat 107), (.negSucc 93), (.ofNat 67), (.ofNat 92), (.ofNat 21), (.ofNat 0), (.ofNat 92), (.negSucc 98), (.ofNat 18), (.negSucc 9), (.negSucc 70), (.ofNat 104)],
  [(.ofNat 114), (.ofNat 103), (.negSucc 58), (.negSucc 84), (.ofNat 91), (.negSucc 42), (.negSucc 120), (.ofNat 79), (.ofNat 72), (.negSucc 95), (.negSucc 103), (.negSucc 35), (.ofNat 46), (.negSucc 51), (.negSucc 100), (.ofNat 103)],
  [(.ofNat 74), (.ofNat 106), (.ofNat 105), (.negSucc 87), (.negSucc 24), (.ofNat 99), (.negSucc 93), (.negSucc 101), (.negSucc 89), (.ofNat 124), (.negSucc 89), (.ofNat 102), (.negSucc 93), (.negSucc 111), (.negSucc 90), (.negSucc 1)],
  [(.negSucc 106), (.negSucc 102), (.negSucc 57), (.negSucc 105), (.negSucc 111), (.ofNat 102), (.ofNat 0), (.ofNat 127), (.ofNat 93), (.negSucc 14), (.ofNat 62), (.ofNat 87), (.ofNat 94), (.negSucc 59), (.negSucc 101), (.negSucc 105)],
  [(.ofNat 104), (.ofNat 97), (.ofNat 97), (.negSucc 116), (.negSucc 83), (.negSucc 102), (.ofNat 102), (.ofNat 76), (.negSucc 87), (.negSucc 72), (.ofNat 96), (.negSucc 110), (.negSucc 32), (.ofNat 61), (.negSucc 95), (.negSucc 61)],
  [(.ofNat 82), (.ofNat 77), (.negSucc 108), (.negSucc 105), (.negSucc 30), (.negSucc 107), (.ofNat 82), (.negSucc 90), (.ofNat 95), (.ofNat 109), (.negSucc 17), (.negSucc 92), (.ofNat 6), (.ofNat 74), (.negSucc 94), (.ofNat 64)],
  [(.negSucc 112), (.negSucc 93), (.ofNat 89), (.negSucc 105), (.ofNat 86), (.ofNat 75), (.negSucc 51), (.ofNat 114), (.negSucc 89), (.negSucc 108), (.negSucc 28), (.ofNat 103), (.negSucc 29), (.ofNat 100), (.negSucc 82), (.ofNat 69)],
  [(.negSucc 68), (.negSucc 97), (.negSucc 100), (.negSucc 60), (.ofNat 105), (.ofNat 112), (.negSucc 109), (.negSucc 64), (.ofNat 109), (.negSucc 7), (.negSucc 104), (.ofNat 114), (.negSucc 58), (.ofNat 99), (.negSucc 20), (.ofNat 102)],
  [(.ofNat 103), (.ofNat 101), (.ofNat 101), (.ofNat 46), (.negSucc 100), (.negSucc 89), (.negSucc 89), (.negSucc 74), (.negSucc 103), (.ofNat 100), (.negSucc 93), (.negSucc 97), (.ofNat 103), (.ofNat 1), (.ofNat 78), (.negSucc 100)],
  [(.negSucc 37), (.negSucc 17), (.negSucc 86), (.ofNat 80), (.negSucc 99), (.negSucc 94), (.ofNat 81), (.ofNat 110), (.ofNat 97), (.negSucc 114), (.ofNat 95), (.negSucc 83), (.negSucc 74), (.negSucc 2), (.ofNat 94), (.negSucc 95)],
  [(.negSucc 91), (.negSucc 93), (.ofNat 97), (.ofNat 88), (.negSucc 79), (.ofNat 5), (.ofNat 82), (.negSucc 42), (.negSucc 103), (.negSucc 16), (.ofNat 103), (.ofNat 21), (.ofNat 65), (.negSucc 121), (.ofNat 87), (.negSucc 65)],
  [(.ofNat 43), (.ofNat 42), (.negSucc 89), (.ofNat 70), (.negSucc 14), (.ofNat 55), (.ofNat 31), (.negSucc 56), (.ofNat 22), (.ofNat 35), (.negSucc 32), (.ofNat 13), (.negSucc 67), (.negSucc 98), (.ofNat 69), (.ofNat 66)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 17 → ∀ b, b < 17 → answer a b = (a + b) % 17

end LeanCheckedNetwork.Net
