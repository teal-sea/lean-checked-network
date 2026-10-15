import LeanCheckedNetwork.Fault.Table

/-!
# Planted fault: this file must FAIL

`Fault` is the trained network with the read-out rows of answers 0 and 1 swapped, so every
weight stays in range but the network answers 1 where the answer is 0 and the other way round
(226 pairs wrong). The same proof that succeeds for the real network must be rejected here, by
the kernel. If this file ever builds, the check is broken.
-/

namespace LeanCheckedNetwork.Fault

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 113 →
    (fastOk E1 E2 128 0 b && fastAnswer E1 E2 W2 128 0 b == (0 + b) % 113) = true := by
  decide +kernel

end LeanCheckedNetwork.Fault
