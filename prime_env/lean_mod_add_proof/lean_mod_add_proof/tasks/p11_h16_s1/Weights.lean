import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.negSucc 72), (.negSucc 89), (.ofNat 81), (.ofNat 109), (.negSucc 38), (.negSucc 114), (.ofNat 102), (.ofNat 100), (.ofNat 115), (.ofNat 108), (.negSucc 110), (.ofNat 101), (.ofNat 69), (.ofNat 41), (.negSucc 100), (.ofNat 104)],
  [(.ofNat 106), (.ofNat 40), (.negSucc 48), (.negSucc 104), (.ofNat 116), (.ofNat 88), (.ofNat 76), (.negSucc 98), (.ofNat 73), (.negSucc 100), (.negSucc 91), (.negSucc 103), (.ofNat 111), (.ofNat 104), (.ofNat 100), (.ofNat 114)],
  [(.negSucc 125), (.ofNat 119), (.negSucc 5), (.ofNat 109), (.negSucc 1), (.ofNat 108), (.negSucc 100), (.ofNat 54), (.ofNat 26), (.ofNat 111), (.ofNat 121), (.ofNat 103), (.negSucc 107), (.ofNat 111), (.ofNat 101), (.negSucc 40)],
  [(.ofNat 123), (.negSucc 103), (.ofNat 97), (.negSucc 105), (.negSucc 105), (.ofNat 84), (.negSucc 125), (.ofNat 117), (.negSucc 68), (.negSucc 34), (.ofNat 89), (.negSucc 70), (.ofNat 95), (.negSucc 91), (.negSucc 102), (.negSucc 102)],
  [(.negSucc 110), (.ofNat 102), (.negSucc 100), (.ofNat 91), (.ofNat 78), (.negSucc 97), (.ofNat 63), (.negSucc 99), (.negSucc 105), (.negSucc 110), (.negSucc 111), (.ofNat 84), (.ofNat 24), (.negSucc 105), (.negSucc 96), (.negSucc 101)],
  [(.ofNat 105), (.ofNat 45), (.ofNat 97), (.negSucc 92), (.ofNat 95), (.negSucc 104), (.ofNat 97), (.ofNat 87), (.negSucc 120), (.ofNat 100), (.negSucc 18), (.ofNat 62), (.negSucc 112), (.negSucc 67), (.ofNat 108), (.ofNat 93)],
  [(.negSucc 97), (.negSucc 114), (.negSucc 108), (.ofNat 43), (.negSucc 120), (.ofNat 3), (.ofNat 116), (.ofNat 22), (.negSucc 87), (.negSucc 92), (.ofNat 110), (.negSucc 17), (.ofNat 94), (.ofNat 110), (.ofNat 83), (.ofNat 99)],
  [(.ofNat 108), (.ofNat 115), (.ofNat 100), (.ofNat 3), (.negSucc 99), (.ofNat 108), (.negSucc 84), (.negSucc 115), (.negSucc 60), (.negSucc 75), (.negSucc 79), (.ofNat 119), (.negSucc 87), (.ofNat 100), (.negSucc 124), (.ofNat 81)],
  [(.negSucc 93), (.negSucc 100), (.negSucc 106), (.negSucc 77), (.ofNat 127), (.ofNat 114), (.negSucc 102), (.ofNat 104), (.ofNat 73), (.ofNat 122), (.negSucc 100), (.negSucc 118), (.negSucc 98), (.ofNat 11), (.negSucc 63), (.negSucc 105)],
  [(.ofNat 53), (.negSucc 71), (.ofNat 106), (.ofNat 94), (.ofNat 88), (.negSucc 90), (.negSucc 111), (.negSucc 68), (.ofNat 90), (.negSucc 105), (.ofNat 78), (.ofNat 107), (.ofNat 113), (.negSucc 110), (.ofNat 113), (.negSucc 104)],
  [(.ofNat 18), (.ofNat 112), (.negSucc 100), (.negSucc 111), (.negSucc 102), (.negSucc 98), (.ofNat 87), (.negSucc 95), (.ofNat 117), (.ofNat 73), (.ofNat 93), (.negSucc 101), (.negSucc 105), (.negSucc 114), (.ofNat 4), (.negSucc 60)]]

def E2 : List (List Int) := [
  [(.negSucc 119), (.ofNat 119), (.ofNat 10), (.ofNat 110), (.ofNat 31), (.negSucc 107), (.negSucc 98), (.ofNat 58), (.ofNat 26), (.ofNat 109), (.ofNat 120), (.ofNat 104), (.negSucc 112), (.ofNat 105), (.ofNat 104), (.ofNat 46)],
  [(.ofNat 126), (.negSucc 107), (.ofNat 87), (.negSucc 107), (.negSucc 112), (.negSucc 62), (.negSucc 125), (.ofNat 112), (.negSucc 61), (.negSucc 48), (.ofNat 89), (.negSucc 73), (.ofNat 98), (.negSucc 89), (.negSucc 101), (.ofNat 100)],
  [(.negSucc 118), (.ofNat 106), (.negSucc 92), (.ofNat 98), (.ofNat 64), (.ofNat 101), (.ofNat 81), (.negSucc 106), (.negSucc 100), (.negSucc 99), (.negSucc 117), (.ofNat 85), (.ofNat 13), (.negSucc 110), (.negSucc 101), (.ofNat 92)],
  [(.ofNat 108), (.ofNat 39), (.ofNat 96), (.negSucc 94), (.ofNat 98), (.ofNat 108), (.ofNat 94), (.ofNat 94), (.negSucc 118), (.ofNat 103), (.negSucc 26), (.ofNat 60), (.negSucc 111), (.negSucc 66), (.ofNat 106), (.negSucc 89)],
  [(.negSucc 95), (.negSucc 112), (.negSucc 114), (.ofNat 58), (.negSucc 102), (.negSucc 37), (.ofNat 112), (.negSucc 20), (.negSucc 103), (.negSucc 92), (.ofNat 113), (.ofNat 7), (.ofNat 101), (.ofNat 111), (.ofNat 83), (.negSucc 104)],
  [(.ofNat 107), (.ofNat 118), (.ofNat 102), (.negSucc 10), (.negSucc 100), (.negSucc 109), (.negSucc 90), (.negSucc 114), (.negSucc 75), (.negSucc 67), (.negSucc 70), (.ofNat 114), (.negSucc 89), (.ofNat 105), (.negSucc 120), (.negSucc 72)],
  [(.negSucc 98), (.negSucc 101), (.negSucc 108), (.negSucc 65), (.ofNat 127), (.negSucc 114), (.negSucc 104), (.ofNat 110), (.ofNat 75), (.ofNat 115), (.negSucc 103), (.negSucc 122), (.negSucc 89), (.negSucc 32), (.negSucc 58), (.ofNat 110)],
  [(.ofNat 52), (.negSucc 55), (.ofNat 107), (.ofNat 72), (.ofNat 94), (.ofNat 89), (.negSucc 109), (.negSucc 74), (.ofNat 90), (.negSucc 103), (.ofNat 71), (.ofNat 105), (.ofNat 106), (.negSucc 108), (.ofNat 115), (.ofNat 109)],
  [(.ofNat 18), (.ofNat 113), (.negSucc 101), (.negSucc 102), (.negSucc 103), (.ofNat 101), (.ofNat 90), (.negSucc 89), (.ofNat 112), (.ofNat 76), (.ofNat 96), (.negSucc 105), (.negSucc 109), (.negSucc 111), (.ofNat 16), (.ofNat 43)],
  [(.negSucc 60), (.negSucc 90), (.ofNat 81), (.ofNat 108), (.negSucc 42), (.ofNat 104), (.ofNat 104), (.ofNat 103), (.ofNat 120), (.ofNat 103), (.negSucc 108), (.ofNat 102), (.ofNat 66), (.ofNat 65), (.negSucc 103), (.negSucc 102)],
  [(.ofNat 97), (.ofNat 57), (.negSucc 70), (.negSucc 110), (.ofNat 119), (.negSucc 88), (.ofNat 68), (.negSucc 100), (.ofNat 80), (.negSucc 104), (.negSucc 93), (.negSucc 101), (.ofNat 96), (.ofNat 101), (.ofNat 99), (.negSucc 122)]]

def W2 : List (List Int) := [
  [(.negSucc 48), (.negSucc 114), (.negSucc 120), (.ofNat 120), (.ofNat 125), (.ofNat 82), (.negSucc 97), (.ofNat 84), (.negSucc 48), (.ofNat 113), (.negSucc 45), (.ofNat 84), (.negSucc 69), (.ofNat 102), (.negSucc 97), (.negSucc 82)],
  [(.ofNat 5), (.ofNat 108), (.ofNat 108), (.negSucc 114), (.ofNat 20), (.negSucc 89), (.negSucc 102), (.ofNat 78), (.negSucc 106), (.negSucc 95), (.negSucc 103), (.negSucc 40), (.negSucc 98), (.ofNat 119), (.ofNat 116), (.ofNat 100)],
  [(.ofNat 34), (.negSucc 15), (.negSucc 100), (.ofNat 108), (.negSucc 110), (.negSucc 109), (.ofNat 61), (.negSucc 119), (.negSucc 110), (.ofNat 49), (.ofNat 69), (.negSucc 15), (.ofNat 108), (.negSucc 84), (.ofNat 48), (.ofNat 119)],
  [(.negSucc 82), (.negSucc 59), (.ofNat 100), (.negSucc 90), (.ofNat 43), (.negSucc 2), (.ofNat 119), (.ofNat 103), (.negSucc 111), (.ofNat 72), (.ofNat 95), (.ofNat 75), (.negSucc 88), (.negSucc 106), (.negSucc 112), (.negSucc 10)],
  [(.ofNat 101), (.ofNat 121), (.negSucc 89), (.ofNat 84), (.ofNat 109), (.ofNat 116), (.ofNat 99), (.ofNat 12), (.negSucc 36), (.negSucc 106), (.negSucc 107), (.negSucc 90), (.negSucc 18), (.negSucc 65), (.negSucc 61), (.negSucc 95)],
  [(.negSucc 117), (.negSucc 101), (.ofNat 89), (.negSucc 78), (.negSucc 103), (.ofNat 108), (.negSucc 80), (.negSucc 100), (.negSucc 10), (.ofNat 100), (.negSucc 81), (.ofNat 106), (.ofNat 87), (.ofNat 102), (.ofNat 123), (.negSucc 120)],
  [(.ofNat 117), (.negSucc 27), (.negSucc 74), (.ofNat 29), (.negSucc 97), (.negSucc 50), (.negSucc 113), (.ofNat 111), (.ofNat 78), (.negSucc 16), (.ofNat 127), (.negSucc 116), (.negSucc 108), (.ofNat 121), (.negSucc 49), (.ofNat 69)],
  [(.negSucc 105), (.ofNat 110), (.negSucc 40), (.ofNat 19), (.ofNat 74), (.negSucc 104), (.negSucc 48), (.negSucc 86), (.ofNat 89), (.negSucc 116), (.ofNat 32), (.ofNat 114), (.ofNat 70), (.ofNat 14), (.negSucc 110), (.ofNat 95)],
  [(.ofNat 106), (.negSucc 110), (.ofNat 13), (.negSucc 76), (.ofNat 74), (.negSucc 97), (.ofNat 72), (.negSucc 21), (.ofNat 98), (.ofNat 111), (.negSucc 118), (.negSucc 101), (.ofNat 13), (.negSucc 101), (.negSucc 5), (.ofNat 82)],
  [(.negSucc 104), (.ofNat 48), (.negSucc 106), (.ofNat 100), (.negSucc 123), (.ofNat 55), (.ofNat 100), (.ofNat 100), (.ofNat 111), (.negSucc 87), (.negSucc 53), (.ofNat 100), (.negSucc 107), (.negSucc 109), (.ofNat 105), (.negSucc 87)],
  [(.ofNat 88), (.ofNat 23), (.ofNat 102), (.negSucc 115), (.negSucc 52), (.ofNat 109), (.negSucc 13), (.negSucc 105), (.ofNat 63), (.negSucc 64), (.ofNat 117), (.negSucc 91), (.ofNat 113), (.ofNat 24), (.negSucc 92), (.negSucc 113)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
