import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.Mod12All.Weights

namespace LeanCheckedNetwork.Mod12All

/-- Every read-out row has 40 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 40 = true := by decide +kernel

end LeanCheckedNetwork.Mod12All
