import LeanCheckedNetwork.Fault.Fixed12Table

/-!
# Planted fault in the 12-neuron fixed-phase network: this file must FAIL

`FaultFixed12` is `FixedPhase12` with one read-out weight raised by 22, so the network answers
104 instead of 46 on the pair (11, 35) (16 pairs wrong in all). The same row proof that
succeeds for `FixedPhase12` must be rejected here, by the kernel. If this file ever builds, the
check is broken.
-/

namespace LeanCheckedNetwork.FaultFixed12

open LeanCheckedNetwork

theorem fast_11 : ∀ b, b < 113 →
    (fastOk E1 E2 12 11 b && fastAnswer E1 E2 W2 12 11 b == (11 + b) % 113) = true := by
  decide +kernel

end LeanCheckedNetwork.FaultFixed12
