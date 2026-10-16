import RnnAdder.Network

/-!
# Planted fault: Wc[3][0] changed from 127 to -127. This file must be REJECTED by the kernel.

`.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1). `H = 4` units.
Certificate check in Python: FAILS; smallest |pre-activation| on a reachable transition: 27.
-/

namespace RnnAdder.FaultB

open RnnAdder

def net : Net := {
  Wh := [
    [(.negSucc 11), (.ofNat 47), (.ofNat 39), (.negSucc 62)],
    [(.negSucc 1), (.ofNat 18), (.ofNat 7), (.negSucc 79)],
    [(.negSucc 1), (.ofNat 15), (.ofNat 14), (.negSucc 83)],
    [(.ofNat 4), (.negSucc 9), (.negSucc 16), (.ofNat 82)]],
  Wxa := [(.negSucc 5), (.negSucc 89), (.negSucc 98), (.ofNat 92)],
  Wxb := [(.negSucc 1), (.negSucc 89), (.negSucc 99), (.ofNat 92)],
  bh := [(.ofNat 36), (.ofNat 118), (.ofNat 127), (.negSucc 118)],
  Wo := [(.negSucc 126), (.ofNat 63), (.ofNat 80), (.negSucc 119)],
  Woa := (.ofNat 125),
  Wob := (.ofNat 125),
  bo := (.negSucc 72),
  Wc := [(.ofNat 28), (.negSucc 40), (.negSucc 33), (.negSucc 126)],
  bc := (.negSucc 64),
  h0 := [false, false, false, false],
  reach := [
    [false, false, false, false],
    [true, true, true, false],
    [true, false, false, true],
    [false, true, true, false],
    [false, false, false, true]]
}

/-- The finite check: the kernel evaluates `transOk` on the 5 reachable states and 4 inputs. -/
theorem trans_ok : transOk net = true := by decide +kernel

end RnnAdder.FaultB
