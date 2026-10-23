import Transformer.BoundsLib
import Transformer.Net.W.Misc

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Transformer.Net

theorem ok_TI2_0 : vecOk 512 26092444094 TI2_0 = true := by decide +kernel
theorem ok_TI2_1 : vecOk 512 26092444094 TI2_1 = true := by decide +kernel
theorem ok_TI2_2 : vecOk 512 26092444094 TI2_2 = true := by decide +kernel
theorem ok_TI2_3 : vecOk 512 26092444094 TI2_3 = true := by decide +kernel

theorem ok_TI2 : TI2.all (vecOk 512 26092444094) = true := by
  refine all_cons_of (vecOk 512 26092444094) TI2_0 _ ok_TI2_0 ?_
  refine all_cons_of (vecOk 512 26092444094) TI2_1 _ ok_TI2_1 ?_
  refine all_cons_of (vecOk 512 26092444094) TI2_2 _ ok_TI2_2 ?_
  refine all_cons_of (vecOk 512 26092444094) TI2_3 _ ok_TI2_3 ?_
  exact all_nil_true _

theorem ok_TU2_0 : vecOk 113 10601584377 TU2_0 = true := by decide +kernel
theorem ok_TU2_1 : vecOk 113 10601584377 TU2_1 = true := by decide +kernel
theorem ok_TU2_2 : vecOk 113 10601584377 TU2_2 = true := by decide +kernel
theorem ok_TU2_3 : vecOk 113 10601584377 TU2_3 = true := by decide +kernel

theorem ok_TU2 : TU2.all (vecOk 113 10601584377) = true := by
  refine all_cons_of (vecOk 113 10601584377) TU2_0 _ ok_TU2_0 ?_
  refine all_cons_of (vecOk 113 10601584377) TU2_1 _ ok_TU2_1 ?_
  refine all_cons_of (vecOk 113 10601584377) TU2_2 _ ok_TU2_2 ?_
  refine all_cons_of (vecOk 113 10601584377) TU2_3 _ ok_TU2_3 ?_
  exact all_nil_true _

theorem ok_CI : vecOk 512 5106312128 CI = true := by decide +kernel

theorem ok_CU : vecOk 113 122325928744832 CU = true := by decide +kernel

end Transformer.Net
