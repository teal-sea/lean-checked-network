import LeanCheckedNetwork.Count
import LeanCheckedNetwork.H64Step8000.Table

/-! Rows 99 to 112: the fast evaluator's checks pass and the number of right answers, by the kernel. -/

set_option Elab.async false

namespace LeanCheckedNetwork.H64Step8000

open LeanCheckedNetwork

theorem row_99 : rowOk E1 E2 64 113 99 = true ∧ fastRowCount E1 E2 W2 64 113 99 = 113 := by
  decide +kernel

theorem row_100 : rowOk E1 E2 64 113 100 = true ∧ fastRowCount E1 E2 W2 64 113 100 = 113 := by
  decide +kernel

theorem row_101 : rowOk E1 E2 64 113 101 = true ∧ fastRowCount E1 E2 W2 64 113 101 = 113 := by
  decide +kernel

theorem row_102 : rowOk E1 E2 64 113 102 = true ∧ fastRowCount E1 E2 W2 64 113 102 = 113 := by
  decide +kernel

theorem row_103 : rowOk E1 E2 64 113 103 = true ∧ fastRowCount E1 E2 W2 64 113 103 = 113 := by
  decide +kernel

theorem row_104 : rowOk E1 E2 64 113 104 = true ∧ fastRowCount E1 E2 W2 64 113 104 = 113 := by
  decide +kernel

theorem row_105 : rowOk E1 E2 64 113 105 = true ∧ fastRowCount E1 E2 W2 64 113 105 = 113 := by
  decide +kernel

theorem row_106 : rowOk E1 E2 64 113 106 = true ∧ fastRowCount E1 E2 W2 64 113 106 = 113 := by
  decide +kernel

theorem row_107 : rowOk E1 E2 64 113 107 = true ∧ fastRowCount E1 E2 W2 64 113 107 = 113 := by
  decide +kernel

theorem row_108 : rowOk E1 E2 64 113 108 = true ∧ fastRowCount E1 E2 W2 64 113 108 = 113 := by
  decide +kernel

theorem row_109 : rowOk E1 E2 64 113 109 = true ∧ fastRowCount E1 E2 W2 64 113 109 = 113 := by
  decide +kernel

theorem row_110 : rowOk E1 E2 64 113 110 = true ∧ fastRowCount E1 E2 W2 64 113 110 = 113 := by
  decide +kernel

theorem row_111 : rowOk E1 E2 64 113 111 = true ∧ fastRowCount E1 E2 W2 64 113 111 = 113 := by
  decide +kernel

theorem row_112 : rowOk E1 E2 64 113 112 = true ∧ fastRowCount E1 E2 W2 64 113 112 = 113 := by
  decide +kernel

end LeanCheckedNetwork.H64Step8000
