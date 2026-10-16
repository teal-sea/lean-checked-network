import PhaseGridInstances.Network

/-! # Planted fault: the p = 7 network with the read-out rows of answers 0 and 1 swapped (14 pairs wrong). -/

set_option maxRecDepth 100000

namespace PhaseGridInstances.P7Fault

def E1 : List (List Int) := [
  [(.ofNat 25), (.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0), (.ofNat 25), (.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0), (.ofNat 25), (.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0)],
  [(.ofNat 16), (.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20), (.negSucc 5), (.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24), (.negSucc 22), (.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11)],
  [(.negSucc 5), (.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24), (.negSucc 22), (.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10), (.ofNat 16), (.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19)],
  [(.negSucc 22), (.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11), (.ofNat 16), (.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19), (.negSucc 5), (.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24)],
  [(.negSucc 22), (.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10), (.ofNat 16), (.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20), (.negSucc 5), (.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23)],
  [(.negSucc 5), (.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23), (.negSucc 22), (.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11), (.ofNat 16), (.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20)],
  [(.ofNat 16), (.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19), (.negSucc 5), (.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23), (.negSucc 22), (.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10)]]

def E2 : List (List Int) := [
  [(.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0), (.ofNat 25), (.ofNat 0)],
  [(.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10)],
  [(.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20)],
  [(.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23), (.negSucc 5), (.negSucc 23)],
  [(.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24)],
  [(.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.negSucc 22), (.negSucc 10), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19), (.ofNat 16), (.negSucc 19)],
  [(.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.ofNat 16), (.ofNat 20), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 5), (.ofNat 24), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11), (.negSucc 22), (.ofNat 11)]]

def W2 : List (List Int) := [
  [(.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20), (.ofNat 16), (.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24), (.negSucc 5), (.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11), (.negSucc 22)],
  [(.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0), (.ofNat 25), (.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0), (.ofNat 25), (.ofNat 25), (.ofNat 0), (.ofNat 0), (.negSucc 24), (.negSucc 24), (.ofNat 0), (.ofNat 0), (.ofNat 25)],
  [(.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24), (.negSucc 5), (.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10), (.negSucc 22), (.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19), (.ofNat 16)],
  [(.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11), (.negSucc 22), (.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19), (.ofNat 16), (.negSucc 5), (.negSucc 23), (.negSucc 23), (.ofNat 6), (.ofNat 6), (.ofNat 24), (.ofNat 24), (.negSucc 5)],
  [(.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10), (.negSucc 22), (.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20), (.ofNat 16), (.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23), (.negSucc 5)],
  [(.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23), (.negSucc 5), (.negSucc 22), (.negSucc 10), (.negSucc 10), (.ofNat 23), (.ofNat 23), (.ofNat 11), (.ofNat 11), (.negSucc 22), (.ofNat 16), (.negSucc 19), (.negSucc 19), (.negSucc 15), (.negSucc 15), (.ofNat 20), (.ofNat 20), (.ofNat 16)],
  [(.ofNat 16), (.ofNat 20), (.ofNat 20), (.negSucc 15), (.negSucc 15), (.negSucc 19), (.negSucc 19), (.ofNat 16), (.negSucc 5), (.ofNat 24), (.ofNat 24), (.ofNat 6), (.ofNat 6), (.negSucc 23), (.negSucc 23), (.negSucc 5), (.negSucc 22), (.ofNat 11), (.ofNat 11), (.ofNat 23), (.ofNat 23), (.negSucc 10), (.negSucc 10), (.negSucc 22)]]

def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

end PhaseGridInstances.P7Fault
