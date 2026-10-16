import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.FixedPhase40.Weights

namespace LeanCheckedNetwork.FixedPhase40

/-- Every read-out row has 40 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 40 = true := by decide +kernel

end LeanCheckedNetwork.FixedPhase40
