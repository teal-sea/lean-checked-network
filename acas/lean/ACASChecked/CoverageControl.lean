import ACASChecked.CoverageData
open TreePilot
set_option maxHeartbeats 0
/-- Removing a real terminal leaves a gap in the covering tree. -/
theorem coverage_gap_rejected : TreePilot.check root nodes.pop = false := by decide +kernel
#print axioms coverage_gap_rejected
