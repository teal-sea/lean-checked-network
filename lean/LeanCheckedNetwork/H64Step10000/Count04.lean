import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step10000.Table

/-! Rows 57 to 70: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step10000

open LeanCheckedNetwork

theorem row_57 : rowOk E1 E2 64 113 57 = true ∧ fastRowCount E1 E2 W2 64 113 57 = 113 := by
  decide +kernel

theorem row_58 : rowOk E1 E2 64 113 58 = true ∧ fastRowCount E1 E2 W2 64 113 58 = 113 := by
  decide +kernel

theorem row_59 : rowOk E1 E2 64 113 59 = true ∧ fastRowCount E1 E2 W2 64 113 59 = 113 := by
  decide +kernel

theorem row_60 : rowOk E1 E2 64 113 60 = true ∧ fastRowCount E1 E2 W2 64 113 60 = 113 := by
  decide +kernel

theorem row_61 : rowOk E1 E2 64 113 61 = true ∧ fastRowCount E1 E2 W2 64 113 61 = 113 := by
  decide +kernel

theorem row_62 : rowOk E1 E2 64 113 62 = true ∧ fastRowCount E1 E2 W2 64 113 62 = 113 := by
  decide +kernel

theorem row_63 : rowOk E1 E2 64 113 63 = true ∧ fastRowCount E1 E2 W2 64 113 63 = 113 := by
  decide +kernel

theorem row_64 : rowOk E1 E2 64 113 64 = true ∧ fastRowCount E1 E2 W2 64 113 64 = 113 := by
  decide +kernel

theorem row_65 : rowOk E1 E2 64 113 65 = true ∧ fastRowCount E1 E2 W2 64 113 65 = 113 := by
  decide +kernel

theorem row_66 : rowOk E1 E2 64 113 66 = true ∧ fastRowCount E1 E2 W2 64 113 66 = 113 := by
  decide +kernel

theorem row_67 : rowOk E1 E2 64 113 67 = true ∧ fastRowCount E1 E2 W2 64 113 67 = 113 := by
  decide +kernel

theorem row_68 : rowOk E1 E2 64 113 68 = true ∧ fastRowCount E1 E2 W2 64 113 68 = 113 := by
  decide +kernel

theorem row_69 : rowOk E1 E2 64 113 69 = true ∧ fastRowCount E1 E2 W2 64 113 69 = 113 := by
  decide +kernel

theorem row_70 : rowOk E1 E2 64 113 70 = true ∧ fastRowCount E1 E2 W2 64 113 70 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step10000
