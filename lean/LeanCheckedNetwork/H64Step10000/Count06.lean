import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step10000.Table

/-! Rows 85 to 98: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step10000

open LeanCheckedNetwork

theorem row_85 : rowOk E1 E2 64 113 85 = true ∧ fastRowCount E1 E2 W2 64 113 85 = 113 := by
  decide +kernel

theorem row_86 : rowOk E1 E2 64 113 86 = true ∧ fastRowCount E1 E2 W2 64 113 86 = 113 := by
  decide +kernel

theorem row_87 : rowOk E1 E2 64 113 87 = true ∧ fastRowCount E1 E2 W2 64 113 87 = 113 := by
  decide +kernel

theorem row_88 : rowOk E1 E2 64 113 88 = true ∧ fastRowCount E1 E2 W2 64 113 88 = 113 := by
  decide +kernel

theorem row_89 : rowOk E1 E2 64 113 89 = true ∧ fastRowCount E1 E2 W2 64 113 89 = 113 := by
  decide +kernel

theorem row_90 : rowOk E1 E2 64 113 90 = true ∧ fastRowCount E1 E2 W2 64 113 90 = 113 := by
  decide +kernel

theorem row_91 : rowOk E1 E2 64 113 91 = true ∧ fastRowCount E1 E2 W2 64 113 91 = 113 := by
  decide +kernel

theorem row_92 : rowOk E1 E2 64 113 92 = true ∧ fastRowCount E1 E2 W2 64 113 92 = 113 := by
  decide +kernel

theorem row_93 : rowOk E1 E2 64 113 93 = true ∧ fastRowCount E1 E2 W2 64 113 93 = 113 := by
  decide +kernel

theorem row_94 : rowOk E1 E2 64 113 94 = true ∧ fastRowCount E1 E2 W2 64 113 94 = 113 := by
  decide +kernel

theorem row_95 : rowOk E1 E2 64 113 95 = true ∧ fastRowCount E1 E2 W2 64 113 95 = 113 := by
  decide +kernel

theorem row_96 : rowOk E1 E2 64 113 96 = true ∧ fastRowCount E1 E2 W2 64 113 96 = 113 := by
  decide +kernel

theorem row_97 : rowOk E1 E2 64 113 97 = true ∧ fastRowCount E1 E2 W2 64 113 97 = 113 := by
  decide +kernel

theorem row_98 : rowOk E1 E2 64 113 98 = true ∧ fastRowCount E1 E2 W2 64 113 98 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step10000
