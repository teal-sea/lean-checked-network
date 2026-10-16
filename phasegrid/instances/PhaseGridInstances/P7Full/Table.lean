import PhaseGridInstances.Fast
import PhaseGridInstances.P7Full.Weights

namespace PhaseGridInstances.P7Full

open LeanCheckedNetwork

/-- Every read-out row has 24 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 24 = true := by decide +kernel

end PhaseGridInstances.P7Full
