import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step10000.Table

/-! Rows 0 to 14: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step10000

open LeanCheckedNetwork

theorem row_0 : rowOk E1 E2 64 113 0 = true ∧ fastRowCount E1 E2 W2 64 113 0 = 113 := by
  decide +kernel

theorem row_1 : rowOk E1 E2 64 113 1 = true ∧ fastRowCount E1 E2 W2 64 113 1 = 113 := by
  decide +kernel

theorem row_2 : rowOk E1 E2 64 113 2 = true ∧ fastRowCount E1 E2 W2 64 113 2 = 113 := by
  decide +kernel

theorem row_3 : rowOk E1 E2 64 113 3 = true ∧ fastRowCount E1 E2 W2 64 113 3 = 113 := by
  decide +kernel

theorem row_4 : rowOk E1 E2 64 113 4 = true ∧ fastRowCount E1 E2 W2 64 113 4 = 113 := by
  decide +kernel

theorem row_5 : rowOk E1 E2 64 113 5 = true ∧ fastRowCount E1 E2 W2 64 113 5 = 112 := by
  decide +kernel

theorem row_6 : rowOk E1 E2 64 113 6 = true ∧ fastRowCount E1 E2 W2 64 113 6 = 113 := by
  decide +kernel

theorem row_7 : rowOk E1 E2 64 113 7 = true ∧ fastRowCount E1 E2 W2 64 113 7 = 113 := by
  decide +kernel

theorem row_8 : rowOk E1 E2 64 113 8 = true ∧ fastRowCount E1 E2 W2 64 113 8 = 113 := by
  decide +kernel

theorem row_9 : rowOk E1 E2 64 113 9 = true ∧ fastRowCount E1 E2 W2 64 113 9 = 112 := by
  decide +kernel

theorem row_10 : rowOk E1 E2 64 113 10 = true ∧ fastRowCount E1 E2 W2 64 113 10 = 113 := by
  decide +kernel

theorem row_11 : rowOk E1 E2 64 113 11 = true ∧ fastRowCount E1 E2 W2 64 113 11 = 113 := by
  decide +kernel

theorem row_12 : rowOk E1 E2 64 113 12 = true ∧ fastRowCount E1 E2 W2 64 113 12 = 113 := by
  decide +kernel

theorem row_13 : rowOk E1 E2 64 113 13 = true ∧ fastRowCount E1 E2 W2 64 113 13 = 113 := by
  decide +kernel

theorem row_14 : rowOk E1 E2 64 113 14 = true ∧ fastRowCount E1 E2 W2 64 113 14 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step10000
