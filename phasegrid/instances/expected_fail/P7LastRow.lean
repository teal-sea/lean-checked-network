import PhaseGridInstances.P7LastFault.Table

/-!
# Planted fault at the last pair: this file must FAIL

`P7LastFault` is the p = 7 network with E2 row 6 replaced by E2 row 5 (`gen_last_fault.py`), so
column b = 6 is wrong and the last row's check is right on b = 0 to 5 and wrong only at its last
pair (6, 6). The kernel cannot short-circuit on an early pair here. If this file ever builds, the
check is broken.
-/

namespace PhaseGridInstances.P7LastFault

open LeanCheckedNetwork

theorem fast_6 : ∀ b, b < 7 →
    (fastOk E1 E2 24 6 b && fastAnswer E1 E2 W2 24 6 b == (6 + b) % 7) = true := by
  decide +kernel

end PhaseGridInstances.P7LastFault
