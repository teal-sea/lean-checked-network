import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows00
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows01
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows02
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows03
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows04
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows05
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows06
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows07
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows08
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows09
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows10
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows11
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows12
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows13
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows14
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows15
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows16
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows17
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows18
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows19
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows20
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows21
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows22
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows23
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows24
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows25
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows26
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows27
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows28
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows29
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows30
import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Rows31

/-!
# The one-wave reduction: each neuron reduced to its dominant wave, no bias neurons: wrong on exactly 0 of 9409 pairs

For every pair `(a, b)` with `a, b < 97`, the network answers `(a + b) % 97` if and only if
`(a, b)` is not in `wrongPairs`, a list of 0 pairs.
-/

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias

theorem rows : ∀ a, a < 97 → ∀ b, b < 97 → (answer a b = (a + b) % 97 ↔ b ∉ wrongRows.getD a []) := by
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
  | n + 97, h => exact absurd h (by omega)

theorem answer_iff_not_wrong : ∀ a, a < 97 → ∀ b, b < 97 →
    (answer a b = (a + b) % 97 ↔ (a, b) ∉ wrongPairs) := by
  intro a ha b hb
  rw [wrongPairs_eq, mem_rowsToPairs]
  simp only [Nat.zero_le, true_and, Nat.sub_zero]
  exact rows a ha b hb

/-- The list is empty, so the network is right on every input: `(a + b) % 97` for all 9409 pairs. -/
theorem adds_mod_97 : ∀ a, a < 97 → ∀ b, b < 97 → answer a b = (a + b) % 97 := by
  intro a ha b hb
  exact (answer_iff_not_wrong a ha b hb).mpr (by simp [wrongPairs])

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias
