import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step6000.Table

/-! Rows 29 to 42: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step6000

open LeanCheckedNetwork

theorem row_29 : rowOk E1 E2 64 113 29 = true ∧ fastRowCount E1 E2 W2 64 113 29 = 113 := by
  decide +kernel

theorem row_30 : rowOk E1 E2 64 113 30 = true ∧ fastRowCount E1 E2 W2 64 113 30 = 113 := by
  decide +kernel

theorem row_31 : rowOk E1 E2 64 113 31 = true ∧ fastRowCount E1 E2 W2 64 113 31 = 113 := by
  decide +kernel

theorem row_32 : rowOk E1 E2 64 113 32 = true ∧ fastRowCount E1 E2 W2 64 113 32 = 113 := by
  decide +kernel

theorem row_33 : rowOk E1 E2 64 113 33 = true ∧ fastRowCount E1 E2 W2 64 113 33 = 113 := by
  decide +kernel

theorem row_34 : rowOk E1 E2 64 113 34 = true ∧ fastRowCount E1 E2 W2 64 113 34 = 113 := by
  decide +kernel

theorem row_35 : rowOk E1 E2 64 113 35 = true ∧ fastRowCount E1 E2 W2 64 113 35 = 113 := by
  decide +kernel

theorem row_36 : rowOk E1 E2 64 113 36 = true ∧ fastRowCount E1 E2 W2 64 113 36 = 113 := by
  decide +kernel

theorem row_37 : rowOk E1 E2 64 113 37 = true ∧ fastRowCount E1 E2 W2 64 113 37 = 113 := by
  decide +kernel

theorem row_38 : rowOk E1 E2 64 113 38 = true ∧ fastRowCount E1 E2 W2 64 113 38 = 113 := by
  decide +kernel

theorem row_39 : rowOk E1 E2 64 113 39 = true ∧ fastRowCount E1 E2 W2 64 113 39 = 113 := by
  decide +kernel

theorem row_40 : rowOk E1 E2 64 113 40 = true ∧ fastRowCount E1 E2 W2 64 113 40 = 113 := by
  decide +kernel

theorem row_41 : rowOk E1 E2 64 113 41 = true ∧ fastRowCount E1 E2 W2 64 113 41 = 113 := by
  decide +kernel

theorem row_42 : rowOk E1 E2 64 113 42 = true ∧ fastRowCount E1 E2 W2 64 113 42 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step6000
