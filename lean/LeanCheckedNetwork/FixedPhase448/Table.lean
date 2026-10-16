import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.FixedPhase448.Weights

namespace LeanCheckedNetwork.FixedPhase448

/-- Every read-out row has 448 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 448 = true := by decide +kernel

end LeanCheckedNetwork.FixedPhase448
