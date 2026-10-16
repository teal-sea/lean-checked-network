import Transformer.Net.Rows00
import Transformer.Net.Rows01
import Transformer.Net.Rows02
import Transformer.Net.Rows03
import Transformer.Net.Rows04
import Transformer.Net.Rows05
import Transformer.Net.Rows06
import Transformer.Net.Rows07
import Transformer.Net.Rows08
import Transformer.Net.Rows09
import Transformer.Net.Rows10
import Transformer.Net.Rows11
import Transformer.Net.Rows12
import Transformer.Net.Rows13
import Transformer.Net.Rows14
import Transformer.Net.Rows15
import Transformer.Net.Rows16
import Transformer.Net.Rows17
import Transformer.Net.Rows18
import Transformer.Net.Rows19
import Transformer.Net.Rows20
import Transformer.Net.Rows21
import Transformer.Net.Rows22
import Transformer.Net.Rows23
import Transformer.Net.Rows24
import Transformer.Net.Rows25
import Transformer.Net.Rows26
import Transformer.Net.Rows27
import Transformer.Net.Rows28
import Transformer.Net.Rows29
import Transformer.Net.Rows30
import Transformer.Net.Rows31
import Transformer.Net.Rows32
import Transformer.Net.Rows33
import Transformer.Net.Rows34
import Transformer.Net.Rows35
import Transformer.Net.Rows36
import Transformer.Net.Rows37
import Transformer.Net.Rows38
import Transformer.Net.Rows39
import Transformer.Net.Rows40
import Transformer.Net.Rows41
import Transformer.Net.Rows42
import Transformer.Net.Rows43
import Transformer.Net.Rows44
import Transformer.Net.Rows45
import Transformer.Net.Rows46
import Transformer.Net.Rows47
import Transformer.Net.Rows48
import Transformer.Net.Rows49
import Transformer.Net.Rows50
import Transformer.Net.Rows51
import Transformer.Net.Rows52
import Transformer.Net.Rows53
import Transformer.Net.Rows54
import Transformer.Net.Rows55
import Transformer.Net.Rows56
import Transformer.Net.Rows57
import Transformer.Net.Rows58
import Transformer.Net.Rows59
import Transformer.Net.Rows60
import Transformer.Net.Rows61
import Transformer.Net.Rows62
import Transformer.Net.Rows63
import Transformer.Net.Rows64
import Transformer.Net.Rows65
import Transformer.Net.Rows66
import Transformer.Net.Rows67
import Transformer.Net.Rows68
import Transformer.Net.Rows69
import Transformer.Net.Rows70
import Transformer.Net.Rows71
import Transformer.Net.Rows72
import Transformer.Net.Rows73
import Transformer.Net.Rows74
import Transformer.Net.Rows75
import Transformer.Net.Rows76
import Transformer.Net.Rows77
import Transformer.Net.Rows78
import Transformer.Net.Rows79
import Transformer.Net.Rows80
import Transformer.Net.Rows81
import Transformer.Net.Rows82
import Transformer.Net.Rows83
import Transformer.Net.Rows84
import Transformer.Net.Rows85
import Transformer.Net.Rows86
import Transformer.Net.Rows87
import Transformer.Net.Rows88
import Transformer.Net.Rows89
import Transformer.Net.Rows90
import Transformer.Net.Rows91
import Transformer.Net.Rows92
import Transformer.Net.Rows93
import Transformer.Net.Rows94
import Transformer.Net.Rows95
import Transformer.Net.Rows96
import Transformer.Net.Rows97
import Transformer.Net.Rows98
import Transformer.Net.Rows99
import Transformer.Net.Rows100
import Transformer.Net.Rows101
import Transformer.Net.Rows102
import Transformer.Net.Rows103
import Transformer.Net.Rows104
import Transformer.Net.Rows105
import Transformer.Net.Rows106
import Transformer.Net.Rows107
import Transformer.Net.Rows108
import Transformer.Net.Rows109
import Transformer.Net.Rows110
import Transformer.Net.Rows111
import Transformer.Net.Rows112
import Transformer.Equiv

/-!
# The quantised transformer: right on every input, with margin

`adds_mod_113`: the model answers `(a + b) % 113` for all 12,769 pairs `(a, b)`.
`margin_ok`: on every pair the right logit exceeds the best wrong one by more than `2E`
(`E2 = 2E`, the constant of Theorem B2 in DESIGN.md).
-/

namespace Transformer.Net

open Transformer

theorem row_0 : ∀ b, b < 113 → answer 0 b = (0 + b) % 113 ∧ margin 0 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 0 b (by omega) hb tables_ok (fast_0 b hb)
theorem row_1 : ∀ b, b < 113 → answer 1 b = (1 + b) % 113 ∧ margin 1 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 1 b (by omega) hb tables_ok (fast_1 b hb)
theorem row_2 : ∀ b, b < 113 → answer 2 b = (2 + b) % 113 ∧ margin 2 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 2 b (by omega) hb tables_ok (fast_2 b hb)
theorem row_3 : ∀ b, b < 113 → answer 3 b = (3 + b) % 113 ∧ margin 3 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 3 b (by omega) hb tables_ok (fast_3 b hb)
theorem row_4 : ∀ b, b < 113 → answer 4 b = (4 + b) % 113 ∧ margin 4 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 4 b (by omega) hb tables_ok (fast_4 b hb)
theorem row_5 : ∀ b, b < 113 → answer 5 b = (5 + b) % 113 ∧ margin 5 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 5 b (by omega) hb tables_ok (fast_5 b hb)
theorem row_6 : ∀ b, b < 113 → answer 6 b = (6 + b) % 113 ∧ margin 6 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 6 b (by omega) hb tables_ok (fast_6 b hb)
theorem row_7 : ∀ b, b < 113 → answer 7 b = (7 + b) % 113 ∧ margin 7 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 7 b (by omega) hb tables_ok (fast_7 b hb)
theorem row_8 : ∀ b, b < 113 → answer 8 b = (8 + b) % 113 ∧ margin 8 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 8 b (by omega) hb tables_ok (fast_8 b hb)
theorem row_9 : ∀ b, b < 113 → answer 9 b = (9 + b) % 113 ∧ margin 9 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 9 b (by omega) hb tables_ok (fast_9 b hb)
theorem row_10 : ∀ b, b < 113 → answer 10 b = (10 + b) % 113 ∧ margin 10 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 10 b (by omega) hb tables_ok (fast_10 b hb)
theorem row_11 : ∀ b, b < 113 → answer 11 b = (11 + b) % 113 ∧ margin 11 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 11 b (by omega) hb tables_ok (fast_11 b hb)
theorem row_12 : ∀ b, b < 113 → answer 12 b = (12 + b) % 113 ∧ margin 12 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 12 b (by omega) hb tables_ok (fast_12 b hb)
theorem row_13 : ∀ b, b < 113 → answer 13 b = (13 + b) % 113 ∧ margin 13 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 13 b (by omega) hb tables_ok (fast_13 b hb)
theorem row_14 : ∀ b, b < 113 → answer 14 b = (14 + b) % 113 ∧ margin 14 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 14 b (by omega) hb tables_ok (fast_14 b hb)
theorem row_15 : ∀ b, b < 113 → answer 15 b = (15 + b) % 113 ∧ margin 15 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 15 b (by omega) hb tables_ok (fast_15 b hb)
theorem row_16 : ∀ b, b < 113 → answer 16 b = (16 + b) % 113 ∧ margin 16 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 16 b (by omega) hb tables_ok (fast_16 b hb)
theorem row_17 : ∀ b, b < 113 → answer 17 b = (17 + b) % 113 ∧ margin 17 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 17 b (by omega) hb tables_ok (fast_17 b hb)
theorem row_18 : ∀ b, b < 113 → answer 18 b = (18 + b) % 113 ∧ margin 18 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 18 b (by omega) hb tables_ok (fast_18 b hb)
theorem row_19 : ∀ b, b < 113 → answer 19 b = (19 + b) % 113 ∧ margin 19 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 19 b (by omega) hb tables_ok (fast_19 b hb)
theorem row_20 : ∀ b, b < 113 → answer 20 b = (20 + b) % 113 ∧ margin 20 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 20 b (by omega) hb tables_ok (fast_20 b hb)
theorem row_21 : ∀ b, b < 113 → answer 21 b = (21 + b) % 113 ∧ margin 21 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 21 b (by omega) hb tables_ok (fast_21 b hb)
theorem row_22 : ∀ b, b < 113 → answer 22 b = (22 + b) % 113 ∧ margin 22 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 22 b (by omega) hb tables_ok (fast_22 b hb)
theorem row_23 : ∀ b, b < 113 → answer 23 b = (23 + b) % 113 ∧ margin 23 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 23 b (by omega) hb tables_ok (fast_23 b hb)
theorem row_24 : ∀ b, b < 113 → answer 24 b = (24 + b) % 113 ∧ margin 24 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 24 b (by omega) hb tables_ok (fast_24 b hb)
theorem row_25 : ∀ b, b < 113 → answer 25 b = (25 + b) % 113 ∧ margin 25 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 25 b (by omega) hb tables_ok (fast_25 b hb)
theorem row_26 : ∀ b, b < 113 → answer 26 b = (26 + b) % 113 ∧ margin 26 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 26 b (by omega) hb tables_ok (fast_26 b hb)
theorem row_27 : ∀ b, b < 113 → answer 27 b = (27 + b) % 113 ∧ margin 27 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 27 b (by omega) hb tables_ok (fast_27 b hb)
theorem row_28 : ∀ b, b < 113 → answer 28 b = (28 + b) % 113 ∧ margin 28 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 28 b (by omega) hb tables_ok (fast_28 b hb)
theorem row_29 : ∀ b, b < 113 → answer 29 b = (29 + b) % 113 ∧ margin 29 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 29 b (by omega) hb tables_ok (fast_29 b hb)
theorem row_30 : ∀ b, b < 113 → answer 30 b = (30 + b) % 113 ∧ margin 30 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 30 b (by omega) hb tables_ok (fast_30 b hb)
theorem row_31 : ∀ b, b < 113 → answer 31 b = (31 + b) % 113 ∧ margin 31 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 31 b (by omega) hb tables_ok (fast_31 b hb)
theorem row_32 : ∀ b, b < 113 → answer 32 b = (32 + b) % 113 ∧ margin 32 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 32 b (by omega) hb tables_ok (fast_32 b hb)
theorem row_33 : ∀ b, b < 113 → answer 33 b = (33 + b) % 113 ∧ margin 33 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 33 b (by omega) hb tables_ok (fast_33 b hb)
theorem row_34 : ∀ b, b < 113 → answer 34 b = (34 + b) % 113 ∧ margin 34 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 34 b (by omega) hb tables_ok (fast_34 b hb)
theorem row_35 : ∀ b, b < 113 → answer 35 b = (35 + b) % 113 ∧ margin 35 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 35 b (by omega) hb tables_ok (fast_35 b hb)
theorem row_36 : ∀ b, b < 113 → answer 36 b = (36 + b) % 113 ∧ margin 36 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 36 b (by omega) hb tables_ok (fast_36 b hb)
theorem row_37 : ∀ b, b < 113 → answer 37 b = (37 + b) % 113 ∧ margin 37 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 37 b (by omega) hb tables_ok (fast_37 b hb)
theorem row_38 : ∀ b, b < 113 → answer 38 b = (38 + b) % 113 ∧ margin 38 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 38 b (by omega) hb tables_ok (fast_38 b hb)
theorem row_39 : ∀ b, b < 113 → answer 39 b = (39 + b) % 113 ∧ margin 39 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 39 b (by omega) hb tables_ok (fast_39 b hb)
theorem row_40 : ∀ b, b < 113 → answer 40 b = (40 + b) % 113 ∧ margin 40 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 40 b (by omega) hb tables_ok (fast_40 b hb)
theorem row_41 : ∀ b, b < 113 → answer 41 b = (41 + b) % 113 ∧ margin 41 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 41 b (by omega) hb tables_ok (fast_41 b hb)
theorem row_42 : ∀ b, b < 113 → answer 42 b = (42 + b) % 113 ∧ margin 42 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 42 b (by omega) hb tables_ok (fast_42 b hb)
theorem row_43 : ∀ b, b < 113 → answer 43 b = (43 + b) % 113 ∧ margin 43 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 43 b (by omega) hb tables_ok (fast_43 b hb)
theorem row_44 : ∀ b, b < 113 → answer 44 b = (44 + b) % 113 ∧ margin 44 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 44 b (by omega) hb tables_ok (fast_44 b hb)
theorem row_45 : ∀ b, b < 113 → answer 45 b = (45 + b) % 113 ∧ margin 45 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 45 b (by omega) hb tables_ok (fast_45 b hb)
theorem row_46 : ∀ b, b < 113 → answer 46 b = (46 + b) % 113 ∧ margin 46 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 46 b (by omega) hb tables_ok (fast_46 b hb)
theorem row_47 : ∀ b, b < 113 → answer 47 b = (47 + b) % 113 ∧ margin 47 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 47 b (by omega) hb tables_ok (fast_47 b hb)
theorem row_48 : ∀ b, b < 113 → answer 48 b = (48 + b) % 113 ∧ margin 48 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 48 b (by omega) hb tables_ok (fast_48 b hb)
theorem row_49 : ∀ b, b < 113 → answer 49 b = (49 + b) % 113 ∧ margin 49 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 49 b (by omega) hb tables_ok (fast_49 b hb)
theorem row_50 : ∀ b, b < 113 → answer 50 b = (50 + b) % 113 ∧ margin 50 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 50 b (by omega) hb tables_ok (fast_50 b hb)
theorem row_51 : ∀ b, b < 113 → answer 51 b = (51 + b) % 113 ∧ margin 51 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 51 b (by omega) hb tables_ok (fast_51 b hb)
theorem row_52 : ∀ b, b < 113 → answer 52 b = (52 + b) % 113 ∧ margin 52 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 52 b (by omega) hb tables_ok (fast_52 b hb)
theorem row_53 : ∀ b, b < 113 → answer 53 b = (53 + b) % 113 ∧ margin 53 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 53 b (by omega) hb tables_ok (fast_53 b hb)
theorem row_54 : ∀ b, b < 113 → answer 54 b = (54 + b) % 113 ∧ margin 54 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 54 b (by omega) hb tables_ok (fast_54 b hb)
theorem row_55 : ∀ b, b < 113 → answer 55 b = (55 + b) % 113 ∧ margin 55 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 55 b (by omega) hb tables_ok (fast_55 b hb)
theorem row_56 : ∀ b, b < 113 → answer 56 b = (56 + b) % 113 ∧ margin 56 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 56 b (by omega) hb tables_ok (fast_56 b hb)
theorem row_57 : ∀ b, b < 113 → answer 57 b = (57 + b) % 113 ∧ margin 57 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 57 b (by omega) hb tables_ok (fast_57 b hb)
theorem row_58 : ∀ b, b < 113 → answer 58 b = (58 + b) % 113 ∧ margin 58 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 58 b (by omega) hb tables_ok (fast_58 b hb)
theorem row_59 : ∀ b, b < 113 → answer 59 b = (59 + b) % 113 ∧ margin 59 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 59 b (by omega) hb tables_ok (fast_59 b hb)
theorem row_60 : ∀ b, b < 113 → answer 60 b = (60 + b) % 113 ∧ margin 60 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 60 b (by omega) hb tables_ok (fast_60 b hb)
theorem row_61 : ∀ b, b < 113 → answer 61 b = (61 + b) % 113 ∧ margin 61 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 61 b (by omega) hb tables_ok (fast_61 b hb)
theorem row_62 : ∀ b, b < 113 → answer 62 b = (62 + b) % 113 ∧ margin 62 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 62 b (by omega) hb tables_ok (fast_62 b hb)
theorem row_63 : ∀ b, b < 113 → answer 63 b = (63 + b) % 113 ∧ margin 63 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 63 b (by omega) hb tables_ok (fast_63 b hb)
theorem row_64 : ∀ b, b < 113 → answer 64 b = (64 + b) % 113 ∧ margin 64 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 64 b (by omega) hb tables_ok (fast_64 b hb)
theorem row_65 : ∀ b, b < 113 → answer 65 b = (65 + b) % 113 ∧ margin 65 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 65 b (by omega) hb tables_ok (fast_65 b hb)
theorem row_66 : ∀ b, b < 113 → answer 66 b = (66 + b) % 113 ∧ margin 66 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 66 b (by omega) hb tables_ok (fast_66 b hb)
theorem row_67 : ∀ b, b < 113 → answer 67 b = (67 + b) % 113 ∧ margin 67 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 67 b (by omega) hb tables_ok (fast_67 b hb)
theorem row_68 : ∀ b, b < 113 → answer 68 b = (68 + b) % 113 ∧ margin 68 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 68 b (by omega) hb tables_ok (fast_68 b hb)
theorem row_69 : ∀ b, b < 113 → answer 69 b = (69 + b) % 113 ∧ margin 69 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 69 b (by omega) hb tables_ok (fast_69 b hb)
theorem row_70 : ∀ b, b < 113 → answer 70 b = (70 + b) % 113 ∧ margin 70 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 70 b (by omega) hb tables_ok (fast_70 b hb)
theorem row_71 : ∀ b, b < 113 → answer 71 b = (71 + b) % 113 ∧ margin 71 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 71 b (by omega) hb tables_ok (fast_71 b hb)
theorem row_72 : ∀ b, b < 113 → answer 72 b = (72 + b) % 113 ∧ margin 72 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 72 b (by omega) hb tables_ok (fast_72 b hb)
theorem row_73 : ∀ b, b < 113 → answer 73 b = (73 + b) % 113 ∧ margin 73 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 73 b (by omega) hb tables_ok (fast_73 b hb)
theorem row_74 : ∀ b, b < 113 → answer 74 b = (74 + b) % 113 ∧ margin 74 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 74 b (by omega) hb tables_ok (fast_74 b hb)
theorem row_75 : ∀ b, b < 113 → answer 75 b = (75 + b) % 113 ∧ margin 75 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 75 b (by omega) hb tables_ok (fast_75 b hb)
theorem row_76 : ∀ b, b < 113 → answer 76 b = (76 + b) % 113 ∧ margin 76 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 76 b (by omega) hb tables_ok (fast_76 b hb)
theorem row_77 : ∀ b, b < 113 → answer 77 b = (77 + b) % 113 ∧ margin 77 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 77 b (by omega) hb tables_ok (fast_77 b hb)
theorem row_78 : ∀ b, b < 113 → answer 78 b = (78 + b) % 113 ∧ margin 78 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 78 b (by omega) hb tables_ok (fast_78 b hb)
theorem row_79 : ∀ b, b < 113 → answer 79 b = (79 + b) % 113 ∧ margin 79 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 79 b (by omega) hb tables_ok (fast_79 b hb)
theorem row_80 : ∀ b, b < 113 → answer 80 b = (80 + b) % 113 ∧ margin 80 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 80 b (by omega) hb tables_ok (fast_80 b hb)
theorem row_81 : ∀ b, b < 113 → answer 81 b = (81 + b) % 113 ∧ margin 81 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 81 b (by omega) hb tables_ok (fast_81 b hb)
theorem row_82 : ∀ b, b < 113 → answer 82 b = (82 + b) % 113 ∧ margin 82 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 82 b (by omega) hb tables_ok (fast_82 b hb)
theorem row_83 : ∀ b, b < 113 → answer 83 b = (83 + b) % 113 ∧ margin 83 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 83 b (by omega) hb tables_ok (fast_83 b hb)
theorem row_84 : ∀ b, b < 113 → answer 84 b = (84 + b) % 113 ∧ margin 84 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 84 b (by omega) hb tables_ok (fast_84 b hb)
theorem row_85 : ∀ b, b < 113 → answer 85 b = (85 + b) % 113 ∧ margin 85 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 85 b (by omega) hb tables_ok (fast_85 b hb)
theorem row_86 : ∀ b, b < 113 → answer 86 b = (86 + b) % 113 ∧ margin 86 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 86 b (by omega) hb tables_ok (fast_86 b hb)
theorem row_87 : ∀ b, b < 113 → answer 87 b = (87 + b) % 113 ∧ margin 87 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 87 b (by omega) hb tables_ok (fast_87 b hb)
theorem row_88 : ∀ b, b < 113 → answer 88 b = (88 + b) % 113 ∧ margin 88 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 88 b (by omega) hb tables_ok (fast_88 b hb)
theorem row_89 : ∀ b, b < 113 → answer 89 b = (89 + b) % 113 ∧ margin 89 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 89 b (by omega) hb tables_ok (fast_89 b hb)
theorem row_90 : ∀ b, b < 113 → answer 90 b = (90 + b) % 113 ∧ margin 90 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 90 b (by omega) hb tables_ok (fast_90 b hb)
theorem row_91 : ∀ b, b < 113 → answer 91 b = (91 + b) % 113 ∧ margin 91 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 91 b (by omega) hb tables_ok (fast_91 b hb)
theorem row_92 : ∀ b, b < 113 → answer 92 b = (92 + b) % 113 ∧ margin 92 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 92 b (by omega) hb tables_ok (fast_92 b hb)
theorem row_93 : ∀ b, b < 113 → answer 93 b = (93 + b) % 113 ∧ margin 93 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 93 b (by omega) hb tables_ok (fast_93 b hb)
theorem row_94 : ∀ b, b < 113 → answer 94 b = (94 + b) % 113 ∧ margin 94 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 94 b (by omega) hb tables_ok (fast_94 b hb)
theorem row_95 : ∀ b, b < 113 → answer 95 b = (95 + b) % 113 ∧ margin 95 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 95 b (by omega) hb tables_ok (fast_95 b hb)
theorem row_96 : ∀ b, b < 113 → answer 96 b = (96 + b) % 113 ∧ margin 96 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 96 b (by omega) hb tables_ok (fast_96 b hb)
theorem row_97 : ∀ b, b < 113 → answer 97 b = (97 + b) % 113 ∧ margin 97 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 97 b (by omega) hb tables_ok (fast_97 b hb)
theorem row_98 : ∀ b, b < 113 → answer 98 b = (98 + b) % 113 ∧ margin 98 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 98 b (by omega) hb tables_ok (fast_98 b hb)
theorem row_99 : ∀ b, b < 113 → answer 99 b = (99 + b) % 113 ∧ margin 99 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 99 b (by omega) hb tables_ok (fast_99 b hb)
theorem row_100 : ∀ b, b < 113 → answer 100 b = (100 + b) % 113 ∧ margin 100 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 100 b (by omega) hb tables_ok (fast_100 b hb)
theorem row_101 : ∀ b, b < 113 → answer 101 b = (101 + b) % 113 ∧ margin 101 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 101 b (by omega) hb tables_ok (fast_101 b hb)
theorem row_102 : ∀ b, b < 113 → answer 102 b = (102 + b) % 113 ∧ margin 102 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 102 b (by omega) hb tables_ok (fast_102 b hb)
theorem row_103 : ∀ b, b < 113 → answer 103 b = (103 + b) % 113 ∧ margin 103 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 103 b (by omega) hb tables_ok (fast_103 b hb)
theorem row_104 : ∀ b, b < 113 → answer 104 b = (104 + b) % 113 ∧ margin 104 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 104 b (by omega) hb tables_ok (fast_104 b hb)
theorem row_105 : ∀ b, b < 113 → answer 105 b = (105 + b) % 113 ∧ margin 105 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 105 b (by omega) hb tables_ok (fast_105 b hb)
theorem row_106 : ∀ b, b < 113 → answer 106 b = (106 + b) % 113 ∧ margin 106 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 106 b (by omega) hb tables_ok (fast_106 b hb)
theorem row_107 : ∀ b, b < 113 → answer 107 b = (107 + b) % 113 ∧ margin 107 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 107 b (by omega) hb tables_ok (fast_107 b hb)
theorem row_108 : ∀ b, b < 113 → answer 108 b = (108 + b) % 113 ∧ margin 108 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 108 b (by omega) hb tables_ok (fast_108 b hb)
theorem row_109 : ∀ b, b < 113 → answer 109 b = (109 + b) % 113 ∧ margin 109 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 109 b (by omega) hb tables_ok (fast_109 b hb)
theorem row_110 : ∀ b, b < 113 → answer 110 b = (110 + b) % 113 ∧ margin 110 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 110 b (by omega) hb tables_ok (fast_110 b hb)
theorem row_111 : ∀ b, b < 113 → answer 111 b = (111 + b) % 113 ∧ margin 111 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 111 b (by omega) hb tables_ok (fast_111 b hb)
theorem row_112 : ∀ b, b < 113 → answer 112 b = (112 + b) % 113 ∧ margin 112 b > E2 := fun b hb =>
  fastCheck_correct cfg tab bnd E2 112 b (by omega) hb tables_ok (fast_112 b hb)

theorem both : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 ∧ margin a b > E2 := by
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

theorem adds_mod_113 : ∀ a, a < 113 → ∀ b, b < 113 → answer a b = (a + b) % 113 :=
  fun a ha b hb => (both a ha b hb).1

theorem margin_ok : ∀ a, a < 113 → ∀ b, b < 113 → margin a b > E2 :=
  fun a ha b hb => (both a ha b hb).2

end Transformer.Net
