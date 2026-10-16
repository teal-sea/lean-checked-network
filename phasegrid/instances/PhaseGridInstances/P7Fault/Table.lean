import PhaseGridInstances.Fast
import PhaseGridInstances.P7Fault.Weights

namespace PhaseGridInstances.P7Fault

open LeanCheckedNetwork

theorem table_ok : tableOk W2 24 = true := by decide +kernel

end PhaseGridInstances.P7Fault
