import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.FixedPhase16.Weights

namespace LeanCheckedNetwork.FixedPhase16

/-- Every read-out row has 16 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 16 = true := by decide +kernel

end LeanCheckedNetwork.FixedPhase16
