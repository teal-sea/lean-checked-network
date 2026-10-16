import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 7

7 possible inputs per side, 8 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: WRONG network for tests: p7_h8_s0.npz.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 7

def E1 : List (List Int) := [
  [(.ofNat 106), (.ofNat 115), (.ofNat 82), (.negSucc 109), (.negSucc 117), (.ofNat 114), (.negSucc 100), (.negSucc 74)],
  [(.negSucc 73), (.negSucc 113), (.negSucc 72), (.ofNat 78), (.ofNat 100), (.negSucc 120), (.ofNat 120), (.negSucc 111)],
  [(.negSucc 103), (.negSucc 101), (.negSucc 115), (.negSucc 90), (.negSucc 109), (.ofNat 106), (.ofNat 108), (.ofNat 109)],
  [(.ofNat 117), (.ofNat 86), (.negSucc 103), (.ofNat 105), (.ofNat 56), (.negSucc 99), (.negSucc 112), (.negSucc 110)],
  [(.negSucc 126), (.ofNat 110), (.negSucc 85), (.ofNat 105), (.ofNat 99), (.ofNat 114), (.ofNat 2), (.ofNat 105)],
  [(.ofNat 113), (.negSucc 106), (.ofNat 24), (.ofNat 48), (.negSucc 113), (.negSucc 43), (.ofNat 108), (.negSucc 105)],
  [(.negSucc 107), (.negSucc 115), (.ofNat 116), (.negSucc 96), (.ofNat 114), (.negSucc 114), (.negSucc 73), (.ofNat 19)]]

def E2 : List (List Int) := [
  [(.negSucc 17), (.ofNat 74), (.negSucc 99), (.ofNat 105), (.ofNat 118), (.ofNat 108), (.ofNat 127), (.negSucc 116)],
  [(.ofNat 92), (.ofNat 115), (.ofNat 114), (.ofNat 108), (.negSucc 119), (.negSucc 113), (.ofNat 107), (.ofNat 94)],
  [(.negSucc 115), (.negSucc 114), (.ofNat 102), (.negSucc 116), (.ofNat 70), (.ofNat 116), (.negSucc 109), (.negSucc 103)],
  [(.ofNat 111), (.negSucc 112), (.ofNat 112), (.negSucc 106), (.ofNat 112), (.negSucc 117), (.ofNat 116), (.ofNat 115)],
  [(.negSucc 104), (.ofNat 116), (.ofNat 52), (.negSucc 109), (.negSucc 113), (.negSucc 14), (.ofNat 106), (.negSucc 107)],
  [(.ofNat 98), (.negSucc 115), (.negSucc 111), (.negSucc 114), (.ofNat 72), (.ofNat 119), (.negSucc 94), (.ofNat 104)],
  [(.negSucc 88), (.negSucc 111), (.negSucc 101), (.ofNat 111), (.negSucc 123), (.negSucc 117), (.negSucc 100), (.ofNat 9)]]

def W2 : List (List Int) := [
  [(.negSucc 106), (.ofNat 111), (.ofNat 75), (.negSucc 109), (.negSucc 126), (.ofNat 113), (.negSucc 101), (.ofNat 100)],
  [(.ofNat 108), (.ofNat 106), (.ofNat 107), (.negSucc 106), (.negSucc 60), (.negSucc 116), (.ofNat 69), (.negSucc 102)],
  [(.negSucc 107), (.negSucc 116), (.negSucc 47), (.ofNat 121), (.negSucc 114), (.ofNat 108), (.ofNat 104), (.negSucc 101)],
  [(.ofNat 94), (.negSucc 109), (.ofNat 103), (.ofNat 97), (.negSucc 96), (.negSucc 106), (.negSucc 110), (.ofNat 108)],
  [(.negSucc 107), (.ofNat 116), (.negSucc 109), (.ofNat 111), (.ofNat 40), (.ofNat 107), (.negSucc 57), (.negSucc 113)],
  [(.ofNat 30), (.negSucc 51), (.negSucc 99), (.ofNat 34), (.negSucc 104), (.negSucc 95), (.ofNat 112), (.ofNat 111)],
  [(.ofNat 109), (.negSucc 109), (.negSucc 108), (.negSucc 31), (.ofNat 117), (.ofNat 1), (.ofNat 43), (.negSucc 97)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7

end LeanCheckedNetwork.Net
