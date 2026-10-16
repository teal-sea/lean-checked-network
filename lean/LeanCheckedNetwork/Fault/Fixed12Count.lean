import LeanCheckedNetwork.Count
import LeanCheckedNetwork.Fault.Fixed12Table

/-!
# The planted fault, counted

`FaultFixed12` is wrong on 16 of the 12,769 pairs (`FIXED_PHASE.md`). The row proof rejects it;
this file says exactly how wrong it is, with the kernel: right on 12753 pairs and no more. One
kernel evaluation per row (`row_a`: the evaluator's checks pass on the row and its count), then
the sum. Generated from `network/fault12.npz`.
-/

set_option Elab.async false

namespace LeanCheckedNetwork.FaultFixed12

open LeanCheckedNetwork

theorem row_0 : rowOk E1 E2 12 113 0 = true ∧ fastRowCount E1 E2 W2 12 113 0 = 113 := by
  decide +kernel
theorem row_1 : rowOk E1 E2 12 113 1 = true ∧ fastRowCount E1 E2 W2 12 113 1 = 112 := by
  decide +kernel
theorem row_2 : rowOk E1 E2 12 113 2 = true ∧ fastRowCount E1 E2 W2 12 113 2 = 113 := by
  decide +kernel
theorem row_3 : rowOk E1 E2 12 113 3 = true ∧ fastRowCount E1 E2 W2 12 113 3 = 113 := by
  decide +kernel
theorem row_4 : rowOk E1 E2 12 113 4 = true ∧ fastRowCount E1 E2 W2 12 113 4 = 113 := by
  decide +kernel
theorem row_5 : rowOk E1 E2 12 113 5 = true ∧ fastRowCount E1 E2 W2 12 113 5 = 113 := by
  decide +kernel
theorem row_6 : rowOk E1 E2 12 113 6 = true ∧ fastRowCount E1 E2 W2 12 113 6 = 112 := by
  decide +kernel
theorem row_7 : rowOk E1 E2 12 113 7 = true ∧ fastRowCount E1 E2 W2 12 113 7 = 113 := by
  decide +kernel
theorem row_8 : rowOk E1 E2 12 113 8 = true ∧ fastRowCount E1 E2 W2 12 113 8 = 113 := by
  decide +kernel
theorem row_9 : rowOk E1 E2 12 113 9 = true ∧ fastRowCount E1 E2 W2 12 113 9 = 113 := by
  decide +kernel
theorem row_10 : rowOk E1 E2 12 113 10 = true ∧ fastRowCount E1 E2 W2 12 113 10 = 113 := by
  decide +kernel
theorem row_11 : rowOk E1 E2 12 113 11 = true ∧ fastRowCount E1 E2 W2 12 113 11 = 112 := by
  decide +kernel
theorem row_12 : rowOk E1 E2 12 113 12 = true ∧ fastRowCount E1 E2 W2 12 113 12 = 113 := by
  decide +kernel
theorem row_13 : rowOk E1 E2 12 113 13 = true ∧ fastRowCount E1 E2 W2 12 113 13 = 113 := by
  decide +kernel
theorem row_14 : rowOk E1 E2 12 113 14 = true ∧ fastRowCount E1 E2 W2 12 113 14 = 113 := by
  decide +kernel
theorem row_15 : rowOk E1 E2 12 113 15 = true ∧ fastRowCount E1 E2 W2 12 113 15 = 113 := by
  decide +kernel
theorem row_16 : rowOk E1 E2 12 113 16 = true ∧ fastRowCount E1 E2 W2 12 113 16 = 113 := by
  decide +kernel
theorem row_17 : rowOk E1 E2 12 113 17 = true ∧ fastRowCount E1 E2 W2 12 113 17 = 113 := by
  decide +kernel
theorem row_18 : rowOk E1 E2 12 113 18 = true ∧ fastRowCount E1 E2 W2 12 113 18 = 113 := by
  decide +kernel
theorem row_19 : rowOk E1 E2 12 113 19 = true ∧ fastRowCount E1 E2 W2 12 113 19 = 113 := by
  decide +kernel
theorem row_20 : rowOk E1 E2 12 113 20 = true ∧ fastRowCount E1 E2 W2 12 113 20 = 113 := by
  decide +kernel
theorem row_21 : rowOk E1 E2 12 113 21 = true ∧ fastRowCount E1 E2 W2 12 113 21 = 113 := by
  decide +kernel
theorem row_22 : rowOk E1 E2 12 113 22 = true ∧ fastRowCount E1 E2 W2 12 113 22 = 113 := by
  decide +kernel
theorem row_23 : rowOk E1 E2 12 113 23 = true ∧ fastRowCount E1 E2 W2 12 113 23 = 113 := by
  decide +kernel
theorem row_24 : rowOk E1 E2 12 113 24 = true ∧ fastRowCount E1 E2 W2 12 113 24 = 113 := by
  decide +kernel
theorem row_25 : rowOk E1 E2 12 113 25 = true ∧ fastRowCount E1 E2 W2 12 113 25 = 113 := by
  decide +kernel
theorem row_26 : rowOk E1 E2 12 113 26 = true ∧ fastRowCount E1 E2 W2 12 113 26 = 113 := by
  decide +kernel
theorem row_27 : rowOk E1 E2 12 113 27 = true ∧ fastRowCount E1 E2 W2 12 113 27 = 113 := by
  decide +kernel
theorem row_28 : rowOk E1 E2 12 113 28 = true ∧ fastRowCount E1 E2 W2 12 113 28 = 113 := by
  decide +kernel
theorem row_29 : rowOk E1 E2 12 113 29 = true ∧ fastRowCount E1 E2 W2 12 113 29 = 113 := by
  decide +kernel
theorem row_30 : rowOk E1 E2 12 113 30 = true ∧ fastRowCount E1 E2 W2 12 113 30 = 113 := by
  decide +kernel
theorem row_31 : rowOk E1 E2 12 113 31 = true ∧ fastRowCount E1 E2 W2 12 113 31 = 113 := by
  decide +kernel
theorem row_32 : rowOk E1 E2 12 113 32 = true ∧ fastRowCount E1 E2 W2 12 113 32 = 113 := by
  decide +kernel
theorem row_33 : rowOk E1 E2 12 113 33 = true ∧ fastRowCount E1 E2 W2 12 113 33 = 113 := by
  decide +kernel
theorem row_34 : rowOk E1 E2 12 113 34 = true ∧ fastRowCount E1 E2 W2 12 113 34 = 113 := by
  decide +kernel
theorem row_35 : rowOk E1 E2 12 113 35 = true ∧ fastRowCount E1 E2 W2 12 113 35 = 112 := by
  decide +kernel
theorem row_36 : rowOk E1 E2 12 113 36 = true ∧ fastRowCount E1 E2 W2 12 113 36 = 113 := by
  decide +kernel
theorem row_37 : rowOk E1 E2 12 113 37 = true ∧ fastRowCount E1 E2 W2 12 113 37 = 113 := by
  decide +kernel
theorem row_38 : rowOk E1 E2 12 113 38 = true ∧ fastRowCount E1 E2 W2 12 113 38 = 113 := by
  decide +kernel
theorem row_39 : rowOk E1 E2 12 113 39 = true ∧ fastRowCount E1 E2 W2 12 113 39 = 113 := by
  decide +kernel
theorem row_40 : rowOk E1 E2 12 113 40 = true ∧ fastRowCount E1 E2 W2 12 113 40 = 112 := by
  decide +kernel
theorem row_41 : rowOk E1 E2 12 113 41 = true ∧ fastRowCount E1 E2 W2 12 113 41 = 113 := by
  decide +kernel
theorem row_42 : rowOk E1 E2 12 113 42 = true ∧ fastRowCount E1 E2 W2 12 113 42 = 113 := by
  decide +kernel
theorem row_43 : rowOk E1 E2 12 113 43 = true ∧ fastRowCount E1 E2 W2 12 113 43 = 113 := by
  decide +kernel
theorem row_44 : rowOk E1 E2 12 113 44 = true ∧ fastRowCount E1 E2 W2 12 113 44 = 113 := by
  decide +kernel
theorem row_45 : rowOk E1 E2 12 113 45 = true ∧ fastRowCount E1 E2 W2 12 113 45 = 112 := by
  decide +kernel
theorem row_46 : rowOk E1 E2 12 113 46 = true ∧ fastRowCount E1 E2 W2 12 113 46 = 113 := by
  decide +kernel
theorem row_47 : rowOk E1 E2 12 113 47 = true ∧ fastRowCount E1 E2 W2 12 113 47 = 113 := by
  decide +kernel
theorem row_48 : rowOk E1 E2 12 113 48 = true ∧ fastRowCount E1 E2 W2 12 113 48 = 113 := by
  decide +kernel
theorem row_49 : rowOk E1 E2 12 113 49 = true ∧ fastRowCount E1 E2 W2 12 113 49 = 113 := by
  decide +kernel
theorem row_50 : rowOk E1 E2 12 113 50 = true ∧ fastRowCount E1 E2 W2 12 113 50 = 112 := by
  decide +kernel
theorem row_51 : rowOk E1 E2 12 113 51 = true ∧ fastRowCount E1 E2 W2 12 113 51 = 113 := by
  decide +kernel
theorem row_52 : rowOk E1 E2 12 113 52 = true ∧ fastRowCount E1 E2 W2 12 113 52 = 113 := by
  decide +kernel
theorem row_53 : rowOk E1 E2 12 113 53 = true ∧ fastRowCount E1 E2 W2 12 113 53 = 113 := by
  decide +kernel
theorem row_54 : rowOk E1 E2 12 113 54 = true ∧ fastRowCount E1 E2 W2 12 113 54 = 113 := by
  decide +kernel
theorem row_55 : rowOk E1 E2 12 113 55 = true ∧ fastRowCount E1 E2 W2 12 113 55 = 112 := by
  decide +kernel
theorem row_56 : rowOk E1 E2 12 113 56 = true ∧ fastRowCount E1 E2 W2 12 113 56 = 113 := by
  decide +kernel
theorem row_57 : rowOk E1 E2 12 113 57 = true ∧ fastRowCount E1 E2 W2 12 113 57 = 113 := by
  decide +kernel
theorem row_58 : rowOk E1 E2 12 113 58 = true ∧ fastRowCount E1 E2 W2 12 113 58 = 113 := by
  decide +kernel
theorem row_59 : rowOk E1 E2 12 113 59 = true ∧ fastRowCount E1 E2 W2 12 113 59 = 113 := by
  decide +kernel
theorem row_60 : rowOk E1 E2 12 113 60 = true ∧ fastRowCount E1 E2 W2 12 113 60 = 112 := by
  decide +kernel
theorem row_61 : rowOk E1 E2 12 113 61 = true ∧ fastRowCount E1 E2 W2 12 113 61 = 113 := by
  decide +kernel
theorem row_62 : rowOk E1 E2 12 113 62 = true ∧ fastRowCount E1 E2 W2 12 113 62 = 113 := by
  decide +kernel
theorem row_63 : rowOk E1 E2 12 113 63 = true ∧ fastRowCount E1 E2 W2 12 113 63 = 113 := by
  decide +kernel
theorem row_64 : rowOk E1 E2 12 113 64 = true ∧ fastRowCount E1 E2 W2 12 113 64 = 113 := by
  decide +kernel
theorem row_65 : rowOk E1 E2 12 113 65 = true ∧ fastRowCount E1 E2 W2 12 113 65 = 112 := by
  decide +kernel
theorem row_66 : rowOk E1 E2 12 113 66 = true ∧ fastRowCount E1 E2 W2 12 113 66 = 113 := by
  decide +kernel
theorem row_67 : rowOk E1 E2 12 113 67 = true ∧ fastRowCount E1 E2 W2 12 113 67 = 113 := by
  decide +kernel
theorem row_68 : rowOk E1 E2 12 113 68 = true ∧ fastRowCount E1 E2 W2 12 113 68 = 113 := by
  decide +kernel
theorem row_69 : rowOk E1 E2 12 113 69 = true ∧ fastRowCount E1 E2 W2 12 113 69 = 113 := by
  decide +kernel
theorem row_70 : rowOk E1 E2 12 113 70 = true ∧ fastRowCount E1 E2 W2 12 113 70 = 112 := by
  decide +kernel
theorem row_71 : rowOk E1 E2 12 113 71 = true ∧ fastRowCount E1 E2 W2 12 113 71 = 113 := by
  decide +kernel
theorem row_72 : rowOk E1 E2 12 113 72 = true ∧ fastRowCount E1 E2 W2 12 113 72 = 113 := by
  decide +kernel
theorem row_73 : rowOk E1 E2 12 113 73 = true ∧ fastRowCount E1 E2 W2 12 113 73 = 113 := by
  decide +kernel
theorem row_74 : rowOk E1 E2 12 113 74 = true ∧ fastRowCount E1 E2 W2 12 113 74 = 113 := by
  decide +kernel
theorem row_75 : rowOk E1 E2 12 113 75 = true ∧ fastRowCount E1 E2 W2 12 113 75 = 113 := by
  decide +kernel
theorem row_76 : rowOk E1 E2 12 113 76 = true ∧ fastRowCount E1 E2 W2 12 113 76 = 113 := by
  decide +kernel
theorem row_77 : rowOk E1 E2 12 113 77 = true ∧ fastRowCount E1 E2 W2 12 113 77 = 113 := by
  decide +kernel
theorem row_78 : rowOk E1 E2 12 113 78 = true ∧ fastRowCount E1 E2 W2 12 113 78 = 113 := by
  decide +kernel
theorem row_79 : rowOk E1 E2 12 113 79 = true ∧ fastRowCount E1 E2 W2 12 113 79 = 113 := by
  decide +kernel
theorem row_80 : rowOk E1 E2 12 113 80 = true ∧ fastRowCount E1 E2 W2 12 113 80 = 113 := by
  decide +kernel
theorem row_81 : rowOk E1 E2 12 113 81 = true ∧ fastRowCount E1 E2 W2 12 113 81 = 113 := by
  decide +kernel
theorem row_82 : rowOk E1 E2 12 113 82 = true ∧ fastRowCount E1 E2 W2 12 113 82 = 113 := by
  decide +kernel
theorem row_83 : rowOk E1 E2 12 113 83 = true ∧ fastRowCount E1 E2 W2 12 113 83 = 113 := by
  decide +kernel
theorem row_84 : rowOk E1 E2 12 113 84 = true ∧ fastRowCount E1 E2 W2 12 113 84 = 113 := by
  decide +kernel
theorem row_85 : rowOk E1 E2 12 113 85 = true ∧ fastRowCount E1 E2 W2 12 113 85 = 113 := by
  decide +kernel
theorem row_86 : rowOk E1 E2 12 113 86 = true ∧ fastRowCount E1 E2 W2 12 113 86 = 113 := by
  decide +kernel
theorem row_87 : rowOk E1 E2 12 113 87 = true ∧ fastRowCount E1 E2 W2 12 113 87 = 113 := by
  decide +kernel
theorem row_88 : rowOk E1 E2 12 113 88 = true ∧ fastRowCount E1 E2 W2 12 113 88 = 113 := by
  decide +kernel
theorem row_89 : rowOk E1 E2 12 113 89 = true ∧ fastRowCount E1 E2 W2 12 113 89 = 112 := by
  decide +kernel
theorem row_90 : rowOk E1 E2 12 113 90 = true ∧ fastRowCount E1 E2 W2 12 113 90 = 113 := by
  decide +kernel
theorem row_91 : rowOk E1 E2 12 113 91 = true ∧ fastRowCount E1 E2 W2 12 113 91 = 113 := by
  decide +kernel
theorem row_92 : rowOk E1 E2 12 113 92 = true ∧ fastRowCount E1 E2 W2 12 113 92 = 113 := by
  decide +kernel
theorem row_93 : rowOk E1 E2 12 113 93 = true ∧ fastRowCount E1 E2 W2 12 113 93 = 113 := by
  decide +kernel
theorem row_94 : rowOk E1 E2 12 113 94 = true ∧ fastRowCount E1 E2 W2 12 113 94 = 112 := by
  decide +kernel
theorem row_95 : rowOk E1 E2 12 113 95 = true ∧ fastRowCount E1 E2 W2 12 113 95 = 113 := by
  decide +kernel
theorem row_96 : rowOk E1 E2 12 113 96 = true ∧ fastRowCount E1 E2 W2 12 113 96 = 113 := by
  decide +kernel
theorem row_97 : rowOk E1 E2 12 113 97 = true ∧ fastRowCount E1 E2 W2 12 113 97 = 113 := by
  decide +kernel
theorem row_98 : rowOk E1 E2 12 113 98 = true ∧ fastRowCount E1 E2 W2 12 113 98 = 113 := by
  decide +kernel
theorem row_99 : rowOk E1 E2 12 113 99 = true ∧ fastRowCount E1 E2 W2 12 113 99 = 112 := by
  decide +kernel
theorem row_100 : rowOk E1 E2 12 113 100 = true ∧ fastRowCount E1 E2 W2 12 113 100 = 113 := by
  decide +kernel
theorem row_101 : rowOk E1 E2 12 113 101 = true ∧ fastRowCount E1 E2 W2 12 113 101 = 113 := by
  decide +kernel
theorem row_102 : rowOk E1 E2 12 113 102 = true ∧ fastRowCount E1 E2 W2 12 113 102 = 113 := by
  decide +kernel
theorem row_103 : rowOk E1 E2 12 113 103 = true ∧ fastRowCount E1 E2 W2 12 113 103 = 113 := by
  decide +kernel
theorem row_104 : rowOk E1 E2 12 113 104 = true ∧ fastRowCount E1 E2 W2 12 113 104 = 112 := by
  decide +kernel
theorem row_105 : rowOk E1 E2 12 113 105 = true ∧ fastRowCount E1 E2 W2 12 113 105 = 113 := by
  decide +kernel
theorem row_106 : rowOk E1 E2 12 113 106 = true ∧ fastRowCount E1 E2 W2 12 113 106 = 113 := by
  decide +kernel
theorem row_107 : rowOk E1 E2 12 113 107 = true ∧ fastRowCount E1 E2 W2 12 113 107 = 113 := by
  decide +kernel
theorem row_108 : rowOk E1 E2 12 113 108 = true ∧ fastRowCount E1 E2 W2 12 113 108 = 113 := by
  decide +kernel
theorem row_109 : rowOk E1 E2 12 113 109 = true ∧ fastRowCount E1 E2 W2 12 113 109 = 112 := by
  decide +kernel
theorem row_110 : rowOk E1 E2 12 113 110 = true ∧ fastRowCount E1 E2 W2 12 113 110 = 113 := by
  decide +kernel
theorem row_111 : rowOk E1 E2 12 113 111 = true ∧ fastRowCount E1 E2 W2 12 113 111 = 113 := by
  decide +kernel
theorem row_112 : rowOk E1 E2 12 113 112 = true ∧ fastRowCount E1 E2 W2 12 113 112 = 113 := by
  decide +kernel

/-- The planted fault answers `(a + b) % 113` on exactly 12753 of the 12769 pairs: 16 wrong. -/
theorem right_on_12753 : count E1 E2 W2 113 = 12753 := by
  unfold count
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, List.range_zero,
    row_0.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 0 table_ok row_0.1,
    row_1.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 1 table_ok row_1.1,
    row_2.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 2 table_ok row_2.1,
    row_3.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 3 table_ok row_3.1,
    row_4.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 4 table_ok row_4.1,
    row_5.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 5 table_ok row_5.1,
    row_6.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 6 table_ok row_6.1,
    row_7.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 7 table_ok row_7.1,
    row_8.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 8 table_ok row_8.1,
    row_9.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 9 table_ok row_9.1,
    row_10.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 10 table_ok row_10.1,
    row_11.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 11 table_ok row_11.1,
    row_12.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 12 table_ok row_12.1,
    row_13.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 13 table_ok row_13.1,
    row_14.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 14 table_ok row_14.1,
    row_15.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 15 table_ok row_15.1,
    row_16.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 16 table_ok row_16.1,
    row_17.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 17 table_ok row_17.1,
    row_18.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 18 table_ok row_18.1,
    row_19.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 19 table_ok row_19.1,
    row_20.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 20 table_ok row_20.1,
    row_21.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 21 table_ok row_21.1,
    row_22.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 22 table_ok row_22.1,
    row_23.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 23 table_ok row_23.1,
    row_24.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 24 table_ok row_24.1,
    row_25.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 25 table_ok row_25.1,
    row_26.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 26 table_ok row_26.1,
    row_27.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 27 table_ok row_27.1,
    row_28.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 28 table_ok row_28.1,
    row_29.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 29 table_ok row_29.1,
    row_30.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 30 table_ok row_30.1,
    row_31.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 31 table_ok row_31.1,
    row_32.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 32 table_ok row_32.1,
    row_33.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 33 table_ok row_33.1,
    row_34.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 34 table_ok row_34.1,
    row_35.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 35 table_ok row_35.1,
    row_36.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 36 table_ok row_36.1,
    row_37.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 37 table_ok row_37.1,
    row_38.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 38 table_ok row_38.1,
    row_39.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 39 table_ok row_39.1,
    row_40.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 40 table_ok row_40.1,
    row_41.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 41 table_ok row_41.1,
    row_42.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 42 table_ok row_42.1,
    row_43.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 43 table_ok row_43.1,
    row_44.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 44 table_ok row_44.1,
    row_45.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 45 table_ok row_45.1,
    row_46.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 46 table_ok row_46.1,
    row_47.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 47 table_ok row_47.1,
    row_48.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 48 table_ok row_48.1,
    row_49.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 49 table_ok row_49.1,
    row_50.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 50 table_ok row_50.1,
    row_51.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 51 table_ok row_51.1,
    row_52.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 52 table_ok row_52.1,
    row_53.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 53 table_ok row_53.1,
    row_54.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 54 table_ok row_54.1,
    row_55.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 55 table_ok row_55.1,
    row_56.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 56 table_ok row_56.1,
    row_57.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 57 table_ok row_57.1,
    row_58.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 58 table_ok row_58.1,
    row_59.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 59 table_ok row_59.1,
    row_60.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 60 table_ok row_60.1,
    row_61.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 61 table_ok row_61.1,
    row_62.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 62 table_ok row_62.1,
    row_63.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 63 table_ok row_63.1,
    row_64.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 64 table_ok row_64.1,
    row_65.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 65 table_ok row_65.1,
    row_66.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 66 table_ok row_66.1,
    row_67.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 67 table_ok row_67.1,
    row_68.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 68 table_ok row_68.1,
    row_69.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 69 table_ok row_69.1,
    row_70.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 70 table_ok row_70.1,
    row_71.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 71 table_ok row_71.1,
    row_72.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 72 table_ok row_72.1,
    row_73.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 73 table_ok row_73.1,
    row_74.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 74 table_ok row_74.1,
    row_75.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 75 table_ok row_75.1,
    row_76.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 76 table_ok row_76.1,
    row_77.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 77 table_ok row_77.1,
    row_78.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 78 table_ok row_78.1,
    row_79.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 79 table_ok row_79.1,
    row_80.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 80 table_ok row_80.1,
    row_81.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 81 table_ok row_81.1,
    row_82.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 82 table_ok row_82.1,
    row_83.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 83 table_ok row_83.1,
    row_84.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 84 table_ok row_84.1,
    row_85.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 85 table_ok row_85.1,
    row_86.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 86 table_ok row_86.1,
    row_87.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 87 table_ok row_87.1,
    row_88.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 88 table_ok row_88.1,
    row_89.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 89 table_ok row_89.1,
    row_90.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 90 table_ok row_90.1,
    row_91.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 91 table_ok row_91.1,
    row_92.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 92 table_ok row_92.1,
    row_93.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 93 table_ok row_93.1,
    row_94.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 94 table_ok row_94.1,
    row_95.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 95 table_ok row_95.1,
    row_96.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 96 table_ok row_96.1,
    row_97.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 97 table_ok row_97.1,
    row_98.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 98 table_ok row_98.1,
    row_99.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 99 table_ok row_99.1,
    row_100.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 100 table_ok row_100.1,
    row_101.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 101 table_ok row_101.1,
    row_102.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 102 table_ok row_102.1,
    row_103.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 103 table_ok row_103.1,
    row_104.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 104 table_ok row_104.1,
    row_105.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 105 table_ok row_105.1,
    row_106.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 106 table_ok row_106.1,
    row_107.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 107 table_ok row_107.1,
    row_108.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 108 table_ok row_108.1,
    row_109.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 109 table_ok row_109.1,
    row_110.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 110 table_ok row_110.1,
    row_111.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 111 table_ok row_111.1,
    row_112.2, rowCount_eq_fastRowCount E1 E2 W2 12 113 112 table_ok row_112.1]
  rfl

end LeanCheckedNetwork.FaultFixed12
