import PhaseGridInstances.P113LastFault.Table

/-!
# Planted fault at the last pair of the 448-neuron network: this file must FAIL

`P113LastFault` is `P113Full` with `E2_112` replaced by `E2_111` (`gen_last_fault.py`), so column
b = 112 is wrong. This is the last of the five chunks of the last row (a = 112, b = 90 to 112), the
statement of `P113Full.fast_112_4`; it is right on b = 90 to 111 and wrong only at (112, 112). If
this file ever builds, the check is broken.
-/

namespace PhaseGridInstances.P113LastFault

open LeanCheckedNetwork

theorem fast_112_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 112 (90 + b) && fastAnswer E1 E2 W2 448 112 (90 + b) == (112 + (90 + b)) % 113) = true := by
  decide +kernel

end PhaseGridInstances.P113LastFault
