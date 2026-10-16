import PhaseGridInstances.P7Fault.Table

/-!
# Planted fault: this file must FAIL

`P7Fault` is the p = 7 phase-grid network with the read-out rows of answers 0 and 1 swapped
(14 of 49 pairs wrong, 2 of them in row 0). The same proof that succeeds for the real
network must be rejected here, by the kernel. If this file ever builds, the check is broken.
-/

namespace PhaseGridInstances.P7Fault

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 7 →
    (fastOk E1 E2 24 0 b && fastAnswer E1 E2 W2 24 0 b == (0 + b) % 7) = true := by
  decide +kernel

end PhaseGridInstances.P7Fault
