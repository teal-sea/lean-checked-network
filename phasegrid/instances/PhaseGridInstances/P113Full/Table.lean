import PhaseGridInstances.Fast
import PhaseGridInstances.P113Full.Weights

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

/-- Every read-out row has 448 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 448 = true := by decide +kernel

end PhaseGridInstances.P113Full
