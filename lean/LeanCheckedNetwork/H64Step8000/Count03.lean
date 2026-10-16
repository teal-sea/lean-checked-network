import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step8000.Table

/-! Rows 43 to 56: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step8000

open LeanCheckedNetwork

theorem row_43 : rowOk E1 E2 64 113 43 = true ∧ fastRowCount E1 E2 W2 64 113 43 = 113 := by
  decide +kernel

theorem row_44 : rowOk E1 E2 64 113 44 = true ∧ fastRowCount E1 E2 W2 64 113 44 = 113 := by
  decide +kernel

theorem row_45 : rowOk E1 E2 64 113 45 = true ∧ fastRowCount E1 E2 W2 64 113 45 = 113 := by
  decide +kernel

theorem row_46 : rowOk E1 E2 64 113 46 = true ∧ fastRowCount E1 E2 W2 64 113 46 = 113 := by
  decide +kernel

theorem row_47 : rowOk E1 E2 64 113 47 = true ∧ fastRowCount E1 E2 W2 64 113 47 = 113 := by
  decide +kernel

theorem row_48 : rowOk E1 E2 64 113 48 = true ∧ fastRowCount E1 E2 W2 64 113 48 = 113 := by
  decide +kernel

theorem row_49 : rowOk E1 E2 64 113 49 = true ∧ fastRowCount E1 E2 W2 64 113 49 = 113 := by
  decide +kernel

theorem row_50 : rowOk E1 E2 64 113 50 = true ∧ fastRowCount E1 E2 W2 64 113 50 = 113 := by
  decide +kernel

theorem row_51 : rowOk E1 E2 64 113 51 = true ∧ fastRowCount E1 E2 W2 64 113 51 = 113 := by
  decide +kernel

theorem row_52 : rowOk E1 E2 64 113 52 = true ∧ fastRowCount E1 E2 W2 64 113 52 = 113 := by
  decide +kernel

theorem row_53 : rowOk E1 E2 64 113 53 = true ∧ fastRowCount E1 E2 W2 64 113 53 = 113 := by
  decide +kernel

theorem row_54 : rowOk E1 E2 64 113 54 = true ∧ fastRowCount E1 E2 W2 64 113 54 = 113 := by
  decide +kernel

theorem row_55 : rowOk E1 E2 64 113 55 = true ∧ fastRowCount E1 E2 W2 64 113 55 = 113 := by
  decide +kernel

theorem row_56 : rowOk E1 E2 64 113 56 = true ∧ fastRowCount E1 E2 W2 64 113 56 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step8000
