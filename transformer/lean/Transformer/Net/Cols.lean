import Transformer.BoundsLib
import Transformer.Net.Weights

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Column sums of `G`

The Mathlib-side `Tables.Bounded chosenBounds` needs, for every column `k`, `sum_i |G i k| <= 8774 * 2025 = 17767350`
(`chosenBounds.G` in `mathlib/Transformer/Logits.lean`); `tablesOk` gives only the per-entry bound, which times 512 is too
weak. `colAbsSum G k` adds the absolute values of entry `k` of every row. One kernel check per column.
This is a statement about the core list table `tab.G`; its link to the Mathlib tables is not proved here.
-/

namespace Transformer.Net

theorem ok_col_0 : colAbsSum G 0 ≤ 17767350 := by decide +kernel

theorem ok_col_1 : colAbsSum G 1 ≤ 17767350 := by decide +kernel

theorem ok_col_2 : colAbsSum G 2 ≤ 17767350 := by decide +kernel

theorem ok_col_3 : colAbsSum G 3 ≤ 17767350 := by decide +kernel

theorem ok_col_4 : colAbsSum G 4 ≤ 17767350 := by decide +kernel

theorem ok_col_5 : colAbsSum G 5 ≤ 17767350 := by decide +kernel

theorem ok_col_6 : colAbsSum G 6 ≤ 17767350 := by decide +kernel

theorem ok_col_7 : colAbsSum G 7 ≤ 17767350 := by decide +kernel

theorem ok_col_8 : colAbsSum G 8 ≤ 17767350 := by decide +kernel

theorem ok_col_9 : colAbsSum G 9 ≤ 17767350 := by decide +kernel

theorem ok_col_10 : colAbsSum G 10 ≤ 17767350 := by decide +kernel

theorem ok_col_11 : colAbsSum G 11 ≤ 17767350 := by decide +kernel

theorem ok_col_12 : colAbsSum G 12 ≤ 17767350 := by decide +kernel

theorem ok_col_13 : colAbsSum G 13 ≤ 17767350 := by decide +kernel

theorem ok_col_14 : colAbsSum G 14 ≤ 17767350 := by decide +kernel

theorem ok_col_15 : colAbsSum G 15 ≤ 17767350 := by decide +kernel

theorem ok_col_16 : colAbsSum G 16 ≤ 17767350 := by decide +kernel

theorem ok_col_17 : colAbsSum G 17 ≤ 17767350 := by decide +kernel

theorem ok_col_18 : colAbsSum G 18 ≤ 17767350 := by decide +kernel

theorem ok_col_19 : colAbsSum G 19 ≤ 17767350 := by decide +kernel

theorem ok_col_20 : colAbsSum G 20 ≤ 17767350 := by decide +kernel

theorem ok_col_21 : colAbsSum G 21 ≤ 17767350 := by decide +kernel

theorem ok_col_22 : colAbsSum G 22 ≤ 17767350 := by decide +kernel

theorem ok_col_23 : colAbsSum G 23 ≤ 17767350 := by decide +kernel

theorem ok_col_24 : colAbsSum G 24 ≤ 17767350 := by decide +kernel

theorem ok_col_25 : colAbsSum G 25 ≤ 17767350 := by decide +kernel

theorem ok_col_26 : colAbsSum G 26 ≤ 17767350 := by decide +kernel

theorem ok_col_27 : colAbsSum G 27 ≤ 17767350 := by decide +kernel

theorem ok_col_28 : colAbsSum G 28 ≤ 17767350 := by decide +kernel

theorem ok_col_29 : colAbsSum G 29 ≤ 17767350 := by decide +kernel

theorem ok_col_30 : colAbsSum G 30 ≤ 17767350 := by decide +kernel

theorem ok_col_31 : colAbsSum G 31 ≤ 17767350 := by decide +kernel

theorem ok_col_32 : colAbsSum G 32 ≤ 17767350 := by decide +kernel

theorem ok_col_33 : colAbsSum G 33 ≤ 17767350 := by decide +kernel

theorem ok_col_34 : colAbsSum G 34 ≤ 17767350 := by decide +kernel

theorem ok_col_35 : colAbsSum G 35 ≤ 17767350 := by decide +kernel

theorem ok_col_36 : colAbsSum G 36 ≤ 17767350 := by decide +kernel

theorem ok_col_37 : colAbsSum G 37 ≤ 17767350 := by decide +kernel

theorem ok_col_38 : colAbsSum G 38 ≤ 17767350 := by decide +kernel

theorem ok_col_39 : colAbsSum G 39 ≤ 17767350 := by decide +kernel

theorem ok_col_40 : colAbsSum G 40 ≤ 17767350 := by decide +kernel

theorem ok_col_41 : colAbsSum G 41 ≤ 17767350 := by decide +kernel

theorem ok_col_42 : colAbsSum G 42 ≤ 17767350 := by decide +kernel

theorem ok_col_43 : colAbsSum G 43 ≤ 17767350 := by decide +kernel

theorem ok_col_44 : colAbsSum G 44 ≤ 17767350 := by decide +kernel

theorem ok_col_45 : colAbsSum G 45 ≤ 17767350 := by decide +kernel

theorem ok_col_46 : colAbsSum G 46 ≤ 17767350 := by decide +kernel

theorem ok_col_47 : colAbsSum G 47 ≤ 17767350 := by decide +kernel

theorem ok_col_48 : colAbsSum G 48 ≤ 17767350 := by decide +kernel

theorem ok_col_49 : colAbsSum G 49 ≤ 17767350 := by decide +kernel

theorem ok_col_50 : colAbsSum G 50 ≤ 17767350 := by decide +kernel

theorem ok_col_51 : colAbsSum G 51 ≤ 17767350 := by decide +kernel

theorem ok_col_52 : colAbsSum G 52 ≤ 17767350 := by decide +kernel

theorem ok_col_53 : colAbsSum G 53 ≤ 17767350 := by decide +kernel

theorem ok_col_54 : colAbsSum G 54 ≤ 17767350 := by decide +kernel

theorem ok_col_55 : colAbsSum G 55 ≤ 17767350 := by decide +kernel

theorem ok_col_56 : colAbsSum G 56 ≤ 17767350 := by decide +kernel

theorem ok_col_57 : colAbsSum G 57 ≤ 17767350 := by decide +kernel

theorem ok_col_58 : colAbsSum G 58 ≤ 17767350 := by decide +kernel

theorem ok_col_59 : colAbsSum G 59 ≤ 17767350 := by decide +kernel

theorem ok_col_60 : colAbsSum G 60 ≤ 17767350 := by decide +kernel

theorem ok_col_61 : colAbsSum G 61 ≤ 17767350 := by decide +kernel

theorem ok_col_62 : colAbsSum G 62 ≤ 17767350 := by decide +kernel

theorem ok_col_63 : colAbsSum G 63 ≤ 17767350 := by decide +kernel

theorem ok_col_64 : colAbsSum G 64 ≤ 17767350 := by decide +kernel

theorem ok_col_65 : colAbsSum G 65 ≤ 17767350 := by decide +kernel

theorem ok_col_66 : colAbsSum G 66 ≤ 17767350 := by decide +kernel

theorem ok_col_67 : colAbsSum G 67 ≤ 17767350 := by decide +kernel

theorem ok_col_68 : colAbsSum G 68 ≤ 17767350 := by decide +kernel

theorem ok_col_69 : colAbsSum G 69 ≤ 17767350 := by decide +kernel

theorem ok_col_70 : colAbsSum G 70 ≤ 17767350 := by decide +kernel

theorem ok_col_71 : colAbsSum G 71 ≤ 17767350 := by decide +kernel

theorem ok_col_72 : colAbsSum G 72 ≤ 17767350 := by decide +kernel

theorem ok_col_73 : colAbsSum G 73 ≤ 17767350 := by decide +kernel

theorem ok_col_74 : colAbsSum G 74 ≤ 17767350 := by decide +kernel

theorem ok_col_75 : colAbsSum G 75 ≤ 17767350 := by decide +kernel

theorem ok_col_76 : colAbsSum G 76 ≤ 17767350 := by decide +kernel

theorem ok_col_77 : colAbsSum G 77 ≤ 17767350 := by decide +kernel

theorem ok_col_78 : colAbsSum G 78 ≤ 17767350 := by decide +kernel

theorem ok_col_79 : colAbsSum G 79 ≤ 17767350 := by decide +kernel

theorem ok_col_80 : colAbsSum G 80 ≤ 17767350 := by decide +kernel

theorem ok_col_81 : colAbsSum G 81 ≤ 17767350 := by decide +kernel

theorem ok_col_82 : colAbsSum G 82 ≤ 17767350 := by decide +kernel

theorem ok_col_83 : colAbsSum G 83 ≤ 17767350 := by decide +kernel

theorem ok_col_84 : colAbsSum G 84 ≤ 17767350 := by decide +kernel

theorem ok_col_85 : colAbsSum G 85 ≤ 17767350 := by decide +kernel

theorem ok_col_86 : colAbsSum G 86 ≤ 17767350 := by decide +kernel

theorem ok_col_87 : colAbsSum G 87 ≤ 17767350 := by decide +kernel

theorem ok_col_88 : colAbsSum G 88 ≤ 17767350 := by decide +kernel

theorem ok_col_89 : colAbsSum G 89 ≤ 17767350 := by decide +kernel

theorem ok_col_90 : colAbsSum G 90 ≤ 17767350 := by decide +kernel

theorem ok_col_91 : colAbsSum G 91 ≤ 17767350 := by decide +kernel

theorem ok_col_92 : colAbsSum G 92 ≤ 17767350 := by decide +kernel

theorem ok_col_93 : colAbsSum G 93 ≤ 17767350 := by decide +kernel

theorem ok_col_94 : colAbsSum G 94 ≤ 17767350 := by decide +kernel

theorem ok_col_95 : colAbsSum G 95 ≤ 17767350 := by decide +kernel

theorem ok_col_96 : colAbsSum G 96 ≤ 17767350 := by decide +kernel

theorem ok_col_97 : colAbsSum G 97 ≤ 17767350 := by decide +kernel

theorem ok_col_98 : colAbsSum G 98 ≤ 17767350 := by decide +kernel

theorem ok_col_99 : colAbsSum G 99 ≤ 17767350 := by decide +kernel

theorem ok_col_100 : colAbsSum G 100 ≤ 17767350 := by decide +kernel

theorem ok_col_101 : colAbsSum G 101 ≤ 17767350 := by decide +kernel

theorem ok_col_102 : colAbsSum G 102 ≤ 17767350 := by decide +kernel

theorem ok_col_103 : colAbsSum G 103 ≤ 17767350 := by decide +kernel

theorem ok_col_104 : colAbsSum G 104 ≤ 17767350 := by decide +kernel

theorem ok_col_105 : colAbsSum G 105 ≤ 17767350 := by decide +kernel

theorem ok_col_106 : colAbsSum G 106 ≤ 17767350 := by decide +kernel

theorem ok_col_107 : colAbsSum G 107 ≤ 17767350 := by decide +kernel

theorem ok_col_108 : colAbsSum G 108 ≤ 17767350 := by decide +kernel

theorem ok_col_109 : colAbsSum G 109 ≤ 17767350 := by decide +kernel

theorem ok_col_110 : colAbsSum G 110 ≤ 17767350 := by decide +kernel

theorem ok_col_111 : colAbsSum G 111 ≤ 17767350 := by decide +kernel

theorem ok_col_112 : colAbsSum G 112 ≤ 17767350 := by decide +kernel

theorem G_length : tab.G.length = 512 := by decide +kernel

theorem colSums_ok : ∀ k, k < 113 → colAbsSum tab.G k ≤ 17767350 := by
  intro k hk
  match k, hk with
  | 0, _ => exact ok_col_0
  | 1, _ => exact ok_col_1
  | 2, _ => exact ok_col_2
  | 3, _ => exact ok_col_3
  | 4, _ => exact ok_col_4
  | 5, _ => exact ok_col_5
  | 6, _ => exact ok_col_6
  | 7, _ => exact ok_col_7
  | 8, _ => exact ok_col_8
  | 9, _ => exact ok_col_9
  | 10, _ => exact ok_col_10
  | 11, _ => exact ok_col_11
  | 12, _ => exact ok_col_12
  | 13, _ => exact ok_col_13
  | 14, _ => exact ok_col_14
  | 15, _ => exact ok_col_15
  | 16, _ => exact ok_col_16
  | 17, _ => exact ok_col_17
  | 18, _ => exact ok_col_18
  | 19, _ => exact ok_col_19
  | 20, _ => exact ok_col_20
  | 21, _ => exact ok_col_21
  | 22, _ => exact ok_col_22
  | 23, _ => exact ok_col_23
  | 24, _ => exact ok_col_24
  | 25, _ => exact ok_col_25
  | 26, _ => exact ok_col_26
  | 27, _ => exact ok_col_27
  | 28, _ => exact ok_col_28
  | 29, _ => exact ok_col_29
  | 30, _ => exact ok_col_30
  | 31, _ => exact ok_col_31
  | 32, _ => exact ok_col_32
  | 33, _ => exact ok_col_33
  | 34, _ => exact ok_col_34
  | 35, _ => exact ok_col_35
  | 36, _ => exact ok_col_36
  | 37, _ => exact ok_col_37
  | 38, _ => exact ok_col_38
  | 39, _ => exact ok_col_39
  | 40, _ => exact ok_col_40
  | 41, _ => exact ok_col_41
  | 42, _ => exact ok_col_42
  | 43, _ => exact ok_col_43
  | 44, _ => exact ok_col_44
  | 45, _ => exact ok_col_45
  | 46, _ => exact ok_col_46
  | 47, _ => exact ok_col_47
  | 48, _ => exact ok_col_48
  | 49, _ => exact ok_col_49
  | 50, _ => exact ok_col_50
  | 51, _ => exact ok_col_51
  | 52, _ => exact ok_col_52
  | 53, _ => exact ok_col_53
  | 54, _ => exact ok_col_54
  | 55, _ => exact ok_col_55
  | 56, _ => exact ok_col_56
  | 57, _ => exact ok_col_57
  | 58, _ => exact ok_col_58
  | 59, _ => exact ok_col_59
  | 60, _ => exact ok_col_60
  | 61, _ => exact ok_col_61
  | 62, _ => exact ok_col_62
  | 63, _ => exact ok_col_63
  | 64, _ => exact ok_col_64
  | 65, _ => exact ok_col_65
  | 66, _ => exact ok_col_66
  | 67, _ => exact ok_col_67
  | 68, _ => exact ok_col_68
  | 69, _ => exact ok_col_69
  | 70, _ => exact ok_col_70
  | 71, _ => exact ok_col_71
  | 72, _ => exact ok_col_72
  | 73, _ => exact ok_col_73
  | 74, _ => exact ok_col_74
  | 75, _ => exact ok_col_75
  | 76, _ => exact ok_col_76
  | 77, _ => exact ok_col_77
  | 78, _ => exact ok_col_78
  | 79, _ => exact ok_col_79
  | 80, _ => exact ok_col_80
  | 81, _ => exact ok_col_81
  | 82, _ => exact ok_col_82
  | 83, _ => exact ok_col_83
  | 84, _ => exact ok_col_84
  | 85, _ => exact ok_col_85
  | 86, _ => exact ok_col_86
  | 87, _ => exact ok_col_87
  | 88, _ => exact ok_col_88
  | 89, _ => exact ok_col_89
  | 90, _ => exact ok_col_90
  | 91, _ => exact ok_col_91
  | 92, _ => exact ok_col_92
  | 93, _ => exact ok_col_93
  | 94, _ => exact ok_col_94
  | 95, _ => exact ok_col_95
  | 96, _ => exact ok_col_96
  | 97, _ => exact ok_col_97
  | 98, _ => exact ok_col_98
  | 99, _ => exact ok_col_99
  | 100, _ => exact ok_col_100
  | 101, _ => exact ok_col_101
  | 102, _ => exact ok_col_102
  | 103, _ => exact ok_col_103
  | 104, _ => exact ok_col_104
  | 105, _ => exact ok_col_105
  | 106, _ => exact ok_col_106
  | 107, _ => exact ok_col_107
  | 108, _ => exact ok_col_108
  | 109, _ => exact ok_col_109
  | 110, _ => exact ok_col_110
  | 111, _ => exact ok_col_111
  | 112, _ => exact ok_col_112
  | n + 113, h => exact absurd h (by omega)

end Transformer.Net
