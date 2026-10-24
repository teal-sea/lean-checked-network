import ACASChecked.UnsafeNode13
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem unsafe13_rejected : Unsafe13.marginCheck = false := by decide +kernel
#print axioms unsafe13_rejected
