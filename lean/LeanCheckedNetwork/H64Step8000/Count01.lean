import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step8000.Table

/-! Rows 15 to 28: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step8000

open LeanCheckedNetwork

theorem row_15 : rowOk E1 E2 64 113 15 = true ∧ fastRowCount E1 E2 W2 64 113 15 = 113 := by
  decide +kernel

theorem row_16 : rowOk E1 E2 64 113 16 = true ∧ fastRowCount E1 E2 W2 64 113 16 = 113 := by
  decide +kernel

theorem row_17 : rowOk E1 E2 64 113 17 = true ∧ fastRowCount E1 E2 W2 64 113 17 = 113 := by
  decide +kernel

theorem row_18 : rowOk E1 E2 64 113 18 = true ∧ fastRowCount E1 E2 W2 64 113 18 = 113 := by
  decide +kernel

theorem row_19 : rowOk E1 E2 64 113 19 = true ∧ fastRowCount E1 E2 W2 64 113 19 = 113 := by
  decide +kernel

theorem row_20 : rowOk E1 E2 64 113 20 = true ∧ fastRowCount E1 E2 W2 64 113 20 = 113 := by
  decide +kernel

theorem row_21 : rowOk E1 E2 64 113 21 = true ∧ fastRowCount E1 E2 W2 64 113 21 = 113 := by
  decide +kernel

theorem row_22 : rowOk E1 E2 64 113 22 = true ∧ fastRowCount E1 E2 W2 64 113 22 = 113 := by
  decide +kernel

theorem row_23 : rowOk E1 E2 64 113 23 = true ∧ fastRowCount E1 E2 W2 64 113 23 = 113 := by
  decide +kernel

theorem row_24 : rowOk E1 E2 64 113 24 = true ∧ fastRowCount E1 E2 W2 64 113 24 = 113 := by
  decide +kernel

theorem row_25 : rowOk E1 E2 64 113 25 = true ∧ fastRowCount E1 E2 W2 64 113 25 = 113 := by
  decide +kernel

theorem row_26 : rowOk E1 E2 64 113 26 = true ∧ fastRowCount E1 E2 W2 64 113 26 = 113 := by
  decide +kernel

theorem row_27 : rowOk E1 E2 64 113 27 = true ∧ fastRowCount E1 E2 W2 64 113 27 = 113 := by
  decide +kernel

theorem row_28 : rowOk E1 E2 64 113 28 = true ∧ fastRowCount E1 E2 W2 64 113 28 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step8000
