-- Packaging fixture: the gate changes the right-hand 0 to 1 in a scratch bundle.
theorem release_kernel_control : (0 : Nat) = 0 := by
  decide +kernel
