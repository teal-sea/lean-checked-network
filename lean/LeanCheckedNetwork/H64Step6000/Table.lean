import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.H64Step6000.Weights

namespace LeanCheckedNetwork.H64Step6000

/-- Every read-out row has 64 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 64 = true := by decide +kernel

end LeanCheckedNetwork.H64Step6000
