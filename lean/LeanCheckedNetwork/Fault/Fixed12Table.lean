import LeanCheckedNetwork.Fast
import LeanCheckedNetwork.Fault.Fixed12Weights

namespace LeanCheckedNetwork.FaultFixed12

/-- Every read-out row has 12 entries, each in [-128, 127]: the condition the fast evaluator needs. -/
theorem table_ok : tableOk W2 12 = true := by decide +kernel

end LeanCheckedNetwork.FaultFixed12
