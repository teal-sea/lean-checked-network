import Transformer.BoundsLib
import Transformer.Net.Weights
import Transformer.Net.B.TI0_0
import Transformer.Net.B.TI0_1
import Transformer.Net.B.TI0_2
import Transformer.Net.B.TI0_3
import Transformer.Net.B.TI1_0
import Transformer.Net.B.TI1_1
import Transformer.Net.B.TI1_2
import Transformer.Net.B.TI1_3
import Transformer.Net.B.TU0
import Transformer.Net.B.TU1
import Transformer.Net.B.Misc
import Transformer.Net.B.G

set_option maxRecDepth 100000

namespace Transformer.Net

/-! `tables_ok` is `tablesOk tab bnd = true` exactly as before, but proved from one small kernel check per
table vector (`B/*.lean`), glued by `tablesOk_of` (`Transformer/BoundsLib.lean`). The per-vector theorems state the
bound as a numeral, `bnd` is a structure of the same numerals, and the unifier identifies them by unfolding `bnd`;
nothing here evaluates a table. -/

theorem tab_TI0_len : (tab.TI0.length == 4) = true := by decide +kernel

theorem tab_TI0_all : tab.TI0.all (fun h => h.length == 114 && h.all (vecOk 512 bnd.kTI)) = true := by
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI0_0 _ ok_TI0_0 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI0_1 _ ok_TI0_1 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI0_2 _ ok_TI0_2 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI0_3 _ ok_TI0_3 ?_
  exact all_nil_true _

theorem tab_TI1_len : (tab.TI1.length == 4) = true := by decide +kernel

theorem tab_TI1_all : tab.TI1.all (fun h => h.length == 114 && h.all (vecOk 512 bnd.kTI)) = true := by
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI1_0 _ ok_TI1_0 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI1_1 _ ok_TI1_1 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI1_2 _ ok_TI1_2 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 512 bnd.kTI)) TI1_3 _ ok_TI1_3 ?_
  exact all_nil_true _

theorem tab_TI2_len : (tab.TI2.length == 4) = true := by decide +kernel

theorem tab_TI2_all : tab.TI2.all (vecOk 512 bnd.kTI) = true := ok_TI2

theorem tab_TU0_len : (tab.TU0.length == 4) = true := by decide +kernel

theorem tab_TU0_all : tab.TU0.all (fun h => h.length == 114 && h.all (vecOk 113 bnd.kTU)) = true := by
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU0_0 _ ok_TU0_0 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU0_1 _ ok_TU0_1 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU0_2 _ ok_TU0_2 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU0_3 _ ok_TU0_3 ?_
  exact all_nil_true _

theorem tab_TU1_len : (tab.TU1.length == 4) = true := by decide +kernel

theorem tab_TU1_all : tab.TU1.all (fun h => h.length == 114 && h.all (vecOk 113 bnd.kTU)) = true := by
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU1_0 _ ok_TU1_0 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU1_1 _ ok_TU1_1 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU1_2 _ ok_TU1_2 ?_
  refine all_cons_of (fun (h : List (List Int)) => h.length == 114 && h.all (vecOk 113 bnd.kTU)) TU1_3 _ ok_TU1_3 ?_
  exact all_nil_true _

theorem tab_TU2_len : (tab.TU2.length == 4) = true := by decide +kernel

theorem tab_TU2_all : tab.TU2.all (vecOk 113 bnd.kTU) = true := ok_TU2

/-- Every table has the right shape and its entries are within `bnd`: the one-time check the fast
evaluator's proof needs. -/
theorem tables_ok : tablesOk tab bnd = true :=
  tablesOk_of tab bnd tab_TI0_len tab_TI0_all tab_TI1_len tab_TI1_all tab_TI2_len tab_TI2_all
    tab_TU0_len tab_TU0_all tab_TU1_len tab_TU1_all tab_TU2_len tab_TU2_all
    ok_CI ok_CU ok_G

end Transformer.Net
