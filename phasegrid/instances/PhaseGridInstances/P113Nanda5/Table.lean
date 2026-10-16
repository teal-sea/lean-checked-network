import PhaseGridInstances.Fast
import PhaseGridInstances.P113Nanda5.Weights

namespace PhaseGridInstances.P113Nanda5

open LeanCheckedNetwork

/-- Every read-out row has 40 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 40 = true := by decide +kernel

end PhaseGridInstances.P113Nanda5
