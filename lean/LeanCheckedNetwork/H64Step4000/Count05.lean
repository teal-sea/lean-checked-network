import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step4000.Table

/-! Rows 71 to 84: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step4000

open LeanCheckedNetwork

theorem row_71 : rowOk E1 E2 64 113 71 = true ∧ fastRowCount E1 E2 W2 64 113 71 = 113 := by
  decide +kernel

theorem row_72 : rowOk E1 E2 64 113 72 = true ∧ fastRowCount E1 E2 W2 64 113 72 = 113 := by
  decide +kernel

theorem row_73 : rowOk E1 E2 64 113 73 = true ∧ fastRowCount E1 E2 W2 64 113 73 = 113 := by
  decide +kernel

theorem row_74 : rowOk E1 E2 64 113 74 = true ∧ fastRowCount E1 E2 W2 64 113 74 = 113 := by
  decide +kernel

theorem row_75 : rowOk E1 E2 64 113 75 = true ∧ fastRowCount E1 E2 W2 64 113 75 = 113 := by
  decide +kernel

theorem row_76 : rowOk E1 E2 64 113 76 = true ∧ fastRowCount E1 E2 W2 64 113 76 = 113 := by
  decide +kernel

theorem row_77 : rowOk E1 E2 64 113 77 = true ∧ fastRowCount E1 E2 W2 64 113 77 = 113 := by
  decide +kernel

theorem row_78 : rowOk E1 E2 64 113 78 = true ∧ fastRowCount E1 E2 W2 64 113 78 = 113 := by
  decide +kernel

theorem row_79 : rowOk E1 E2 64 113 79 = true ∧ fastRowCount E1 E2 W2 64 113 79 = 113 := by
  decide +kernel

theorem row_80 : rowOk E1 E2 64 113 80 = true ∧ fastRowCount E1 E2 W2 64 113 80 = 113 := by
  decide +kernel

theorem row_81 : rowOk E1 E2 64 113 81 = true ∧ fastRowCount E1 E2 W2 64 113 81 = 113 := by
  decide +kernel

theorem row_82 : rowOk E1 E2 64 113 82 = true ∧ fastRowCount E1 E2 W2 64 113 82 = 113 := by
  decide +kernel

theorem row_83 : rowOk E1 E2 64 113 83 = true ∧ fastRowCount E1 E2 W2 64 113 83 = 113 := by
  decide +kernel

theorem row_84 : rowOk E1 E2 64 113 84 = true ∧ fastRowCount E1 E2 W2 64 113 84 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step4000
