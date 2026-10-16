import PhaseGridInstances.P113Full.Rows00
import PhaseGridInstances.P113Full.Rows01
import PhaseGridInstances.P113Full.Rows02
import PhaseGridInstances.P113Full.Rows03
import PhaseGridInstances.P113Full.Rows04
import PhaseGridInstances.P113Full.Rows05
import PhaseGridInstances.P113Full.Rows06
import PhaseGridInstances.P113Full.Rows07
import PhaseGridInstances.P113Full.Rows08
import PhaseGridInstances.P113Full.Rows09
import PhaseGridInstances.P113Full.Rows10
import PhaseGridInstances.P113Full.Rows11
import PhaseGridInstances.P113Full.Rows12
import PhaseGridInstances.P113Full.Rows13
import PhaseGridInstances.P113Full.Rows14
import PhaseGridInstances.P113Full.Rows15

/-!
# The phase-grid network at p = 113, frequencies 1 to 56, scale M = 25: right on every input

The network answers `(a + b) % 113` for all 12769 pairs `(a, b)`.
-/

namespace PhaseGridInstances.P113Full

theorem adds_mod_113 : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_0
  | 1, _ => exact row_1
  | 2, _ => exact row_2
  | 3, _ => exact row_3
  | 4, _ => exact row_4
  | 5, _ => exact row_5
  | 6, _ => exact row_6
  | 7, _ => exact row_7
  | 8, _ => exact row_8
  | 9, _ => exact row_9
  | 10, _ => exact row_10
  | 11, _ => exact row_11
  | 12, _ => exact row_12
  | 13, _ => exact row_13
  | 14, _ => exact row_14
  | 15, _ => exact row_15
  | 16, _ => exact row_16
  | 17, _ => exact row_17
  | 18, _ => exact row_18
  | 19, _ => exact row_19
  | 20, _ => exact row_20
  | 21, _ => exact row_21
  | 22, _ => exact row_22
  | 23, _ => exact row_23
  | 24, _ => exact row_24
  | 25, _ => exact row_25
  | 26, _ => exact row_26
  | 27, _ => exact row_27
  | 28, _ => exact row_28
  | 29, _ => exact row_29
  | 30, _ => exact row_30
  | 31, _ => exact row_31
  | 32, _ => exact row_32
  | 33, _ => exact row_33
  | 34, _ => exact row_34
  | 35, _ => exact row_35
  | 36, _ => exact row_36
  | 37, _ => exact row_37
  | 38, _ => exact row_38
  | 39, _ => exact row_39
  | 40, _ => exact row_40
  | 41, _ => exact row_41
  | 42, _ => exact row_42
  | 43, _ => exact row_43
  | 44, _ => exact row_44
  | 45, _ => exact row_45
  | 46, _ => exact row_46
  | 47, _ => exact row_47
  | 48, _ => exact row_48
  | 49, _ => exact row_49
  | 50, _ => exact row_50
  | 51, _ => exact row_51
  | 52, _ => exact row_52
  | 53, _ => exact row_53
  | 54, _ => exact row_54
  | 55, _ => exact row_55
  | 56, _ => exact row_56
  | 57, _ => exact row_57
  | 58, _ => exact row_58
  | 59, _ => exact row_59
  | 60, _ => exact row_60
  | 61, _ => exact row_61
  | 62, _ => exact row_62
  | 63, _ => exact row_63
  | 64, _ => exact row_64
  | 65, _ => exact row_65
  | 66, _ => exact row_66
  | 67, _ => exact row_67
  | 68, _ => exact row_68
  | 69, _ => exact row_69
  | 70, _ => exact row_70
  | 71, _ => exact row_71
  | 72, _ => exact row_72
  | 73, _ => exact row_73
  | 74, _ => exact row_74
  | 75, _ => exact row_75
  | 76, _ => exact row_76
  | 77, _ => exact row_77
  | 78, _ => exact row_78
  | 79, _ => exact row_79
  | 80, _ => exact row_80
  | 81, _ => exact row_81
  | 82, _ => exact row_82
  | 83, _ => exact row_83
  | 84, _ => exact row_84
  | 85, _ => exact row_85
  | 86, _ => exact row_86
  | 87, _ => exact row_87
  | 88, _ => exact row_88
  | 89, _ => exact row_89
  | 90, _ => exact row_90
  | 91, _ => exact row_91
  | 92, _ => exact row_92
  | 93, _ => exact row_93
  | 94, _ => exact row_94
  | 95, _ => exact row_95
  | 96, _ => exact row_96
  | 97, _ => exact row_97
  | 98, _ => exact row_98
  | 99, _ => exact row_99
  | 100, _ => exact row_100
  | 101, _ => exact row_101
  | 102, _ => exact row_102
  | 103, _ => exact row_103
  | 104, _ => exact row_104
  | 105, _ => exact row_105
  | 106, _ => exact row_106
  | 107, _ => exact row_107
  | 108, _ => exact row_108
  | 109, _ => exact row_109
  | 110, _ => exact row_110
  | 111, _ => exact row_111
  | 112, _ => exact row_112
  | n + 113, h => exact absurd h (by omega)

end PhaseGridInstances.P113Full
