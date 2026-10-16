import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.Mod7All.Weights

namespace LeanCheckedNetwork.Mod7All

/-- Every read-out row has 24 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 24 = true := by decide +kernel

end LeanCheckedNetwork.Mod7All
