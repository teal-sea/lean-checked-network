import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.Trained.Weights

namespace LeanCheckedNetwork.Trained

/-- Every read-out row has 128 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 128 = true := by decide +kernel

end LeanCheckedNetwork.Trained
