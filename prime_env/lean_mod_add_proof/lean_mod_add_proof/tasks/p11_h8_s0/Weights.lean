import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 11

11 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=11 H=8 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 11

def E1 : List (List Int) := [
  [(.ofNat 111), (.negSucc 2), (.ofNat 113), (.negSucc 102), (.negSucc 71), (.ofNat 55), (.negSucc 102), (.ofNat 7)],
  [(.negSucc 91), (.ofNat 80), (.negSucc 84), (.negSucc 43), (.negSucc 102), (.ofNat 93), (.ofNat 113), (.ofNat 63)],
  [(.negSucc 105), (.negSucc 101), (.ofNat 96), (.ofNat 106), (.negSucc 90), (.negSucc 95), (.negSucc 91), (.negSucc 78)],
  [(.ofNat 103), (.ofNat 47), (.negSucc 105), (.negSucc 6), (.negSucc 112), (.negSucc 99), (.negSucc 59), (.ofNat 103)],
  [(.ofNat 74), (.ofNat 88), (.ofNat 98), (.negSucc 103), (.negSucc 21), (.ofNat 84), (.ofNat 111), (.negSucc 99)],
  [(.negSucc 102), (.negSucc 88), (.negSucc 97), (.ofNat 69), (.ofNat 85), (.ofNat 104), (.negSucc 100), (.ofNat 113)],
  [(.negSucc 68), (.ofNat 104), (.ofNat 67), (.ofNat 119), (.ofNat 93), (.ofNat 31), (.ofNat 78), (.negSucc 100)],
  [(.ofNat 111), (.ofNat 1), (.negSucc 78), (.negSucc 86), (.ofNat 104), (.negSucc 11), (.ofNat 95), (.ofNat 105)],
  [(.negSucc 28), (.negSucc 92), (.negSucc 30), (.negSucc 120), (.ofNat 91), (.negSucc 89), (.negSucc 123), (.negSucc 90)],
  [(.negSucc 111), (.ofNat 94), (.negSucc 42), (.ofNat 99), (.ofNat 86), (.negSucc 69), (.ofNat 111), (.ofNat 95)],
  [(.ofNat 93), (.negSucc 126), (.negSucc 73), (.ofNat 117), (.negSucc 14), (.ofNat 122), (.negSucc 39), (.negSucc 71)]]

def E2 : List (List Int) := [
  [(.negSucc 91), (.ofNat 80), (.negSucc 84), (.negSucc 43), (.negSucc 102), (.ofNat 92), (.negSucc 112), (.ofNat 63)],
  [(.negSucc 105), (.negSucc 101), (.ofNat 96), (.ofNat 106), (.negSucc 90), (.negSucc 96), (.ofNat 92), (.negSucc 78)],
  [(.ofNat 102), (.ofNat 47), (.negSucc 105), (.negSucc 6), (.negSucc 112), (.negSucc 98), (.ofNat 60), (.ofNat 103)],
  [(.ofNat 74), (.ofNat 88), (.ofNat 97), (.negSucc 103), (.negSucc 21), (.ofNat 84), (.negSucc 111), (.negSucc 99)],
  [(.negSucc 102), (.negSucc 89), (.negSucc 97), (.ofNat 69), (.ofNat 86), (.ofNat 105), (.ofNat 101), (.ofNat 114)],
  [(.negSucc 67), (.ofNat 103), (.ofNat 67), (.ofNat 119), (.ofNat 93), (.ofNat 31), (.negSucc 76), (.negSucc 100)],
  [(.ofNat 111), (.ofNat 1), (.negSucc 78), (.negSucc 86), (.ofNat 104), (.negSucc 11), (.negSucc 94), (.ofNat 105)],
  [(.negSucc 28), (.negSucc 91), (.negSucc 29), (.negSucc 119), (.ofNat 91), (.negSucc 89), (.ofNat 124), (.negSucc 90)],
  [(.negSucc 111), (.ofNat 94), (.negSucc 41), (.ofNat 99), (.ofNat 86), (.negSucc 68), (.negSucc 109), (.ofNat 94)],
  [(.ofNat 93), (.negSucc 126), (.negSucc 72), (.ofNat 117), (.negSucc 14), (.ofNat 122), (.ofNat 40), (.negSucc 70)],
  [(.ofNat 111), (.negSucc 2), (.ofNat 114), (.negSucc 102), (.negSucc 71), (.ofNat 55), (.ofNat 103), (.ofNat 7)]]

def W2 : List (List Int) := [
  [(.negSucc 93), (.ofNat 32), (.negSucc 73), (.ofNat 54), (.ofNat 32), (.negSucc 26), (.ofNat 40), (.ofNat 97)],
  [(.ofNat 23), (.ofNat 105), (.ofNat 118), (.negSucc 90), (.ofNat 101), (.negSucc 97), (.negSucc 123), (.negSucc 98)],
  [(.ofNat 95), (.negSucc 96), (.negSucc 124), (.negSucc 93), (.ofNat 70), (.negSucc 31), (.ofNat 16), (.ofNat 92)],
  [(.negSucc 38), (.ofNat 49), (.ofNat 100), (.ofNat 49), (.ofNat 77), (.negSucc 48), (.negSucc 1), (.negSucc 83)],
  [(.negSucc 113), (.negSucc 73), (.negSucc 99), (.ofNat 68), (.ofNat 98), (.ofNat 106), (.negSucc 100), (.ofNat 93)],
  [(.ofNat 58), (.negSucc 56), (.ofNat 103), (.negSucc 113), (.ofNat 24), (.negSucc 6), (.ofNat 46), (.negSucc 42)],
  [(.ofNat 99), (.ofNat 106), (.negSucc 89), (.negSucc 34), (.negSucc 64), (.negSucc 112), (.ofNat 32), (.ofNat 48)],
  [(.negSucc 66), (.negSucc 58), (.ofNat 85), (.ofNat 114), (.negSucc 84), (.negSucc 85), (.negSucc 52), (.ofNat 72)],
  [(.negSucc 36), (.ofNat 94), (.negSucc 75), (.ofNat 6), (.negSucc 103), (.ofNat 12), (.ofNat 102), (.negSucc 47)],
  [(.ofNat 105), (.ofNat 43), (.ofNat 24), (.negSucc 118), (.negSucc 98), (.negSucc 17), (.negSucc 99), (.ofNat 96)],
  [(.ofNat 44), (.negSucc 126), (.ofNat 20), (.ofNat 69), (.ofNat 34), (.ofNat 94), (.negSucc 55), (.negSucc 102)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 11 → ∀ b, b < 11 → answer a b = (a + b) % 11

end LeanCheckedNetwork.Net
