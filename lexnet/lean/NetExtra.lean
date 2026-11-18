import lean.Pilot
import lean.Units
namespace Lexnet
open Units
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def hashStep (wc code W d h1 h2 : Int) : Int × Int × Int :=
  let f0_12 := min 14 (max (0 : Int) (14 + ((-15) * W) + (1 * d)))
  let f0_13 := min 1 (max (0 : Int) (8 + ((-15) * W) + (1 * d)))
  let f0_14 := min 1 (max (0 : Int) ((-7) + (15 * W) + ((-1) * d)))
  let f0_15 := min 1 (max (0 : Int) ((-13) + (15 * W) + ((-1) * d)))
  let f1_14 := max (0 : Int) ((-1688849860263936) + (562949953421312 * f0_13) + (562949953421312 * wc) + (562949953421312 * W) + (1 * h1))
  let f1_15 := max (0 : Int) ((-562949953421312) + (562949953421312 * f0_13) + (1 * code))
  let f1_16 := max (0 : Int) (0 + ((-562949953421312) * f0_13) + (1 * h1))
  let f1_17 := max (0 : Int) ((-1125899906842624) + (562949953421312 * f0_14) + ((-562949953421312) * f0_15) + (562949953421312 * wc) + (1 * h2))
  let f1_18 := max (0 : Int) ((-562949953421312) + (562949953421312 * f0_14) + ((-562949953421312) * f0_15) + (1 * code))
  let f1_19 := max (0 : Int) ((-562949953421312) + ((-562949953421312) * f0_14) + (562949953421312 * f0_15) + (562949953421312 * W) + (1 * h2))
  let f2_0 := max (0 : Int) (0 + (64 * f1_14) + (1 * f1_15) + (1 * f1_16))
  let f2_1 := max (0 : Int) (0 + (64 * f1_17) + (1 * f1_18) + (1 * f1_19))
  (f0_12, f2_0, f2_1)
theorem hash_link (x : Features) (h : FState) :
    ((forward x h).1.d, (forward x h).1.h1, (forward x h).1.h2) = hashStep (x.flags.getD 2 0) x.code h.W h.d h.h1 h.h2 := by rfl
def wnStep (x : List Int) (h : AState) (hW hN : Int) : Int × Int :=
  let f0_0 := min 1 (max (0 : Int) (0 + (1 * (h.getD 0 0)) + ((-1) * (h.getD 8 0))))
  let f0_1 := min 1 (max (0 : Int) (0 + ((-1) * (x.getD 5 0)) + (1 * (h.getD 1 0))))
  let f0_2 := min 1 (max (0 : Int) (0 + ((-1) * (x.getD 5 0)) + (1 * (h.getD 2 0)) + ((-1) * (h.getD 9 0))))
  let f0_3 := min 1 (max (0 : Int) (0 + ((-1) * (x.getD 5 0)) + (1 * (h.getD 3 0)) + ((-1) * (h.getD 10 0))))
  let f0_9 := min 1 (max (0 : Int) ((-1) + (1 * (x.getD 2 0)) + (1 * hW)))
  let f0_10 := min 1 (max (0 : Int) (0 + (1 * (x.getD 0 0)) + ((-1) * hN)))
  let f0_11 := min 1 (max (0 : Int) (0 + (1 * (x.getD 1 0)) + (1 * hN)))
  let f1_12 := min 1 (max (0 : Int) (0 + ((-2) * f0_0) + ((-2) * f0_1) + ((-2) * f0_2) + ((-2) * f0_3) + (1 * f0_9) + (1 * f0_10)))
  let f1_13 := min 1 (max (0 : Int) ((-1) + ((-2) * f0_0) + ((-2) * f0_1) + ((-2) * f0_2) + ((-2) * f0_3) + ((-1) * f0_9) + ((-1) * f0_10) + (1 * f0_11) + (1 * (x.getD 3 0))))
  (f1_12, f1_13)
theorem wn_link (x : Features) (h : FState) :
    ((forward x h).1.W, (forward x h).1.N) = wnStep x.flags h.auto h.W h.N := by rfl
def openStep (x : List Int) (h : AState) : Int :=
  let f0_5 := min 1 (max (0 : Int) ((-1) + (1 * (x.getD 10 0)) + (1 * (h.getD 6 0))))
  let f0_6 := min 1 (max (0 : Int) ((-1) + (1 * (x.getD 9 0)) + (1 * (h.getD 6 0))))
  let f1_2 := min 1 (max (0 : Int) (0 + (1 * f0_5) + (1 * f0_6)))
  f1_2
theorem open_link (x : Features) (h : FState) :
    (forward x h).2.getD 10 0 = openStep x.flags h.auto := by rfl
def flagsOf (f2_0 f2_1 : Int) : Int × Int × Int :=
  let f3_0 := min 1 (max (0 : Int) ((-349454) + (1 * f2_0)))
  let f3_1 := min 1 (max (0 : Int) (349456 + ((-1) * f2_0)))
  let f3_2 := min 1 (max (0 : Int) ((-38293578) + (1 * f2_0)))
  let f3_3 := min 1 (max (0 : Int) (38293580 + ((-1) * f2_0)))
  let f3_4 := min 1 (max (0 : Int) ((-791748) + (1 * f2_0)))
  let f3_5 := min 1 (max (0 : Int) (791750 + ((-1) * f2_0)))
  let f3_6 := min 1 (max (0 : Int) ((-54322387) + (1 * f2_0)))
  let f3_7 := min 1 (max (0 : Int) (54322389 + ((-1) * f2_0)))
  let f3_8 := min 1 (max (0 : Int) ((-14240302032196) + (1 * f2_0)))
  let f3_9 := min 1 (max (0 : Int) (14240302032198 + ((-1) * f2_0)))
  let f3_10 := min 1 (max (0 : Int) ((-280347628307) + (1 * f2_0)))
  let f3_11 := min 1 (max (0 : Int) (280347628309 + ((-1) * f2_0)))
  let f3_12 := min 1 (max (0 : Int) ((-270) + (1 * f2_0)))
  let f3_13 := min 1 (max (0 : Int) (272 + ((-1) * f2_0)))
  let f3_14 := min 1 (max (0 : Int) ((-1361092) + (1 * f2_0)))
  let f3_15 := min 1 (max (0 : Int) (1361094 + ((-1) * f2_0)))
  let f3_16 := min 1 (max (0 : Int) ((-1369420) + (1 * f2_0)))
  let f3_17 := min 1 (max (0 : Int) (1369422 + ((-1) * f2_0)))
  let f3_18 := min 1 (max (0 : Int) ((-5776626829) + (1 * f2_0)))
  let f3_19 := min 1 (max (0 : Int) (5776626831 + ((-1) * f2_0)))
  let f3_20 := min 1 (max (0 : Int) ((-25553) + (1 * f2_0)))
  let f3_21 := min 1 (max (0 : Int) (25555 + ((-1) * f2_0)))
  let f3_22 := min 1 (max (0 : Int) ((-1897742) + (1 * f2_0)))
  let f3_23 := min 1 (max (0 : Int) (1897744 + ((-1) * f2_0)))
  let f3_24 := min 1 (max (0 : Int) ((-581) + (1 * f2_0)))
  let f3_25 := min 1 (max (0 : Int) (583 + ((-1) * f2_0)))
  let f3_26 := min 1 (max (0 : Int) ((-9901740932) + (1 * f2_0)))
  let f3_27 := min 1 (max (0 : Int) (9901740934 + ((-1) * f2_0)))
  let f3_28 := min 1 (max (0 : Int) ((-79516106834257) + (1 * f2_0)))
  let f3_29 := min 1 (max (0 : Int) (79516106834259 + ((-1) * f2_0)))
  let f3_30 := min 1 (max (0 : Int) ((-79529175978195) + (1 * f2_0)))
  let f3_31 := min 1 (max (0 : Int) (79529175978197 + ((-1) * f2_0)))
  let f3_32 := min 1 (max (0 : Int) ((-19416568973) + (1 * f2_0)))
  let f3_33 := min 1 (max (0 : Int) (19416568975 + ((-1) * f2_0)))
  let f3_34 := min 1 (max (0 : Int) ((-20558926789) + (1 * f2_0)))
  let f3_35 := min 1 (max (0 : Int) (20558926791 + ((-1) * f2_0)))
  let f3_36 := min 1 (max (0 : Int) ((-20736983618) + (1 * f2_0)))
  let f3_37 := min 1 (max (0 : Int) (20736983620 + ((-1) * f2_0)))
  let f3_38 := min 1 (max (0 : Int) ((-20741443795) + (1 * f2_0)))
  let f3_39 := min 1 (max (0 : Int) (20741443797 + ((-1) * f2_0)))
  let f3_40 := min 1 (max (0 : Int) ((-20789412039) + (1 * f2_0)))
  let f3_41 := min 1 (max (0 : Int) (20789412041 + ((-1) * f2_0)))
  let f3_42 := min 1 (max (0 : Int) ((-1401502843205) + (1 * f2_0)))
  let f3_43 := min 1 (max (0 : Int) (1401502843207 + ((-1) * f2_0)))
  let f3_44 := min 1 (max (0 : Int) ((-356029389) + (1 * f2_0)))
  let f3_45 := min 1 (max (0 : Int) (356029391 + ((-1) * f2_0)))
  let f3_46 := min 1 (max (0 : Int) ((-97800722354948) + (1 * f2_0)))
  let f3_47 := min 1 (max (0 : Int) (97800722354950 + ((-1) * f2_0)))
  let f3_48 := min 1 (max (0 : Int) ((-388010756) + (1 * f2_0)))
  let f3_49 := min 1 (max (0 : Int) (388010758 + ((-1) * f2_0)))
  let f3_50 := min 1 (max (0 : Int) ((-278945393860690) + (1 * f2_0)))
  let f3_51 := min 1 (max (0 : Int) (278945393860692 + ((-1) * f2_0)))
  let f3_52 := min 1 (max (0 : Int) ((-278945393861573) + (1 * f2_0)))
  let f3_53 := min 1 (max (0 : Int) (278945393861575 + ((-1) * f2_0)))
  let f3_54 := min 1 (max (0 : Int) ((-4358657593922) + (1 * f2_0)))
  let f3_55 := min 1 (max (0 : Int) (4358657593924 + ((-1) * f2_0)))
  let f3_56 := min 1 (max (0 : Int) ((-279350277907010) + (1 * f2_0)))
  let f3_57 := min 1 (max (0 : Int) (279350277907012 + ((-1) * f2_0)))
  let f3_58 := min 1 (max (0 : Int) ((-279842118780241) + (1 * f2_0)))
  let f3_59 := min 1 (max (0 : Int) (279842118780243 + ((-1) * f2_0)))
  let f3_60 := min 1 (max (0 : Int) ((-13) + (1 * f2_1)))
  let f3_61 := min 1 (max (0 : Int) (15 + ((-1) * f2_1)))
  let f3_62 := min 1 (max (0 : Int) ((-280190803546366) + (1 * f2_0)))
  let f3_63 := min 1 (max (0 : Int) (280190803546368 + ((-1) * f2_0)))
  let f3_64 := min 1 (max (0 : Int) ((-1397511315) + (1 * f2_1)))
  let f3_65 := min 1 (max (0 : Int) (1397511317 + ((-1) * f2_1)))
  let f3_66 := min 1 (max (0 : Int) ((-280246919369022) + (1 * f2_0)))
  let f3_67 := min 1 (max (0 : Int) (280246919369024 + ((-1) * f2_0)))
  let f3_68 := min 1 (max (0 : Int) ((-205271115) + (1 * f2_1)))
  let f3_69 := min 1 (max (0 : Int) (205271117 + ((-1) * f2_1)))
  let f3_70 := min 1 (max (0 : Int) ((-81757266002) + (1 * f2_0)))
  let f3_71 := min 1 (max (0 : Int) (81757266004 + ((-1) * f2_0)))
  let f3_72 := min 1 (max (0 : Int) ((-81757266885) + (1 * f2_0)))
  let f3_73 := min 1 (max (0 : Int) (81757266887 + ((-1) * f2_0)))
  let f3_74 := min 1 (max (0 : Int) ((-14240288101903) + (1 * f2_0)))
  let f3_75 := min 1 (max (0 : Int) (14240288101905 + ((-1) * f2_0)))
  let f3_76 := min 1 (max (0 : Int) ((-17) + (1 * f2_1)))
  let f3_77 := min 1 (max (0 : Int) (19 + ((-1) * f2_1)))
  let f3_78 := min 1 (max (0 : Int) ((-84938684907456) + (1 * f2_0)))
  let f3_79 := min 1 (max (0 : Int) (84938684907458 + ((-1) * f2_0)))
  let f3_80 := min 1 (max (0 : Int) ((-323769491) + (1 * f2_1)))
  let f3_81 := min 1 (max (0 : Int) (323769493 + ((-1) * f2_1)))
  let f3_82 := min 1 (max (0 : Int) ((-88530097557451) + (1 * f2_0)))
  let f3_83 := min 1 (max (0 : Int) (88530097557453 + ((-1) * f2_0)))
  let f3_84 := min 1 (max (0 : Int) ((-3944523) + (1 * f2_1)))
  let f3_85 := min 1 (max (0 : Int) (3944525 + ((-1) * f2_1)))
  let f3_86 := min 1 (max (0 : Int) ((-21898482629) + (1 * f2_0)))
  let f3_87 := min 1 (max (0 : Int) (21898482631 + ((-1) * f2_0)))
  let f3_88 := min 1 (max (0 : Int) ((-819281) + (1 * f2_0)))
  let f3_89 := min 1 (max (0 : Int) (819283 + ((-1) * f2_0)))
  let f3_90 := min 1 (max (0 : Int) ((-4552139524) + (1 * f2_0)))
  let f3_91 := min 1 (max (0 : Int) (4552139526 + ((-1) * f2_0)))
  let f3_92 := min 1 (max (0 : Int) ((-103870547) + (1 * f2_0)))
  let f3_93 := min 1 (max (0 : Int) (103870549 + ((-1) * f2_0)))
  let f3_94 := min 1 (max (0 : Int) ((-37779) + (1 * f2_0)))
  let f3_95 := min 1 (max (0 : Int) (37781 + ((-1) * f2_0)))
  let f3_96 := min 1 (max (0 : Int) ((-3208070) + (1 * f2_0)))
  let f3_97 := min 1 (max (0 : Int) (3208072 + ((-1) * f2_0)))
  let f3_98 := min 1 (max (0 : Int) ((-320926867) + (1 * f2_0)))
  let f3_99 := min 1 (max (0 : Int) (320926869 + ((-1) * f2_0)))
  let f3_100 := min 1 (max (0 : Int) ((-20553982275) + (1 * f2_0)))
  let f3_101 := min 1 (max (0 : Int) (20553982277 + ((-1) * f2_0)))
  let f3_102 := min 1 (max (0 : Int) ((-93341603389763) + (1 * f2_0)))
  let f3_103 := min 1 (max (0 : Int) (93341603389765 + ((-1) * f2_0)))
  let f3_104 := min 1 (max (0 : Int) ((-5829187) + (1 * f2_0)))
  let f3_105 := min 1 (max (0 : Int) (5829189 + ((-1) * f2_0)))
  let f3_106 := min 1 (max (0 : Int) ((-586699) + (1 * f2_0)))
  let f3_107 := min 1 (max (0 : Int) (586701 + ((-1) * f2_0)))
  let f3_108 := min 1 (max (0 : Int) ((-1064367051) + (1 * f2_0)))
  let f3_109 := min 1 (max (0 : Int) (1064367053 + ((-1) * f2_0)))
  let f3_110 := min 1 (max (0 : Int) ((-279086123499863) + (1 * f2_0)))
  let f3_111 := min 1 (max (0 : Int) (279086123499865 + ((-1) * f2_0)))
  let f3_112 := min 1 (max (0 : Int) ((-20558929875) + (1 * f2_0)))
  let f3_113 := min 1 (max (0 : Int) (20558929877 + ((-1) * f2_0)))
  let f3_114 := min 1 (max (0 : Int) ((-1326228987859) + (1 * f2_0)))
  let f3_115 := min 1 (max (0 : Int) (1326228987861 + ((-1) * f2_0)))
  let f3_116 := min 1 (max (0 : Int) ((-71762530558398) + (1 * f2_0)))
  let f3_117 := min 1 (max (0 : Int) (71762530558400 + ((-1) * f2_0)))
  let f3_118 := min 1 (max (0 : Int) ((-19) + (1 * f2_1)))
  let f3_119 := min 1 (max (0 : Int) (21 + ((-1) * f2_1)))
  let f3_120 := min 1 (max (0 : Int) ((-40566239866835) + (1 * f2_0)))
  let f3_121 := min 1 (max (0 : Int) (40566239866837 + ((-1) * f2_0)))
  let f3_122 := min 1 (max (0 : Int) ((-92992824231102) + (1 * f2_0)))
  let f3_123 := min 1 (max (0 : Int) (92992824231104 + ((-1) * f2_0)))
  let f3_124 := min 1 (max (0 : Int) ((-1583903748051) + (1 * f2_0)))
  let f3_125 := min 1 (max (0 : Int) (1583903748053 + ((-1) * f2_0)))
  let f3_126 := min 1 (max (0 : Int) ((-21629263827) + (1 * f2_0)))
  let f3_127 := min 1 (max (0 : Int) (21629263829 + ((-1) * f2_0)))
  let f3_128 := min 1 (max (0 : Int) ((-253259731) + (1 * f2_0)))
  let f3_129 := min 1 (max (0 : Int) (253259733 + ((-1) * f2_0)))
  let f3_130 := min 1 (max (0 : Int) ((-270815187) + (1 * f2_0)))
  let f3_131 := min 1 (max (0 : Int) (270815189 + ((-1) * f2_0)))
  let f3_132 := min 1 (max (0 : Int) ((-9904054227) + (1 * f2_0)))
  let f3_133 := min 1 (max (0 : Int) (9904054229 + ((-1) * f2_0)))
  let f3_134 := min 1 (max (0 : Int) ((-633857621971) + (1 * f2_0)))
  let f3_135 := min 1 (max (0 : Int) (633857621973 + ((-1) * f2_0)))
  let f3_136 := min 1 (max (0 : Int) ((-633858129875) + (1 * f2_0)))
  let f3_137 := min 1 (max (0 : Int) (633858129877 + ((-1) * f2_0)))
  let f3_138 := min 1 (max (0 : Int) ((-633858924499) + (1 * f2_0)))
  let f3_139 := min 1 (max (0 : Int) (633858924501 + ((-1) * f2_0)))
  let f3_140 := min 1 (max (0 : Int) ((-1453013065683) + (1 * f2_0)))
  let f3_141 := min 1 (max (0 : Int) (1453013065685 + ((-1) * f2_0)))
  let f3_142 := min 1 (max (0 : Int) ((-92992834355155) + (1 * f2_0)))
  let f3_143 := min 1 (max (0 : Int) (92992834355157 + ((-1) * f2_0)))
  let f3_144 := min 1 (max (0 : Int) ((-92992834863059) + (1 * f2_0)))
  let f3_145 := min 1 (max (0 : Int) (92992834863061 + ((-1) * f2_0)))
  let f3_146 := min 1 (max (0 : Int) ((-92992835657683) + (1 * f2_0)))
  let f3_147 := min 1 (max (0 : Int) (92992835657685 + ((-1) * f2_0)))
  let f3_148 := min 1 (max (0 : Int) ((-8534430) + (1 * f2_0)))
  let f3_149 := min 1 (max (0 : Int) (8534432 + ((-1) * f2_0)))
  let f3_150 := min 1 (max (0 : Int) ((-1513962378451) + (1 * f2_0)))
  let f3_151 := min 1 (max (0 : Int) (1513962378453 + ((-1) * f2_0)))
  let f3_152 := min 1 (max (0 : Int) ((-10680741) + (1 * f2_0)))
  let f3_153 := min 1 (max (0 : Int) (10680743 + ((-1) * f2_0)))
  let f3_154 := min 1 (max (0 : Int) ((-984825791761) + (1 * f2_0)))
  let f3_155 := min 1 (max (0 : Int) (984825791763 + ((-1) * f2_0)))
  let f3_156 := min 1 (max (0 : Int) ((-5317956) + (1 * f2_0)))
  let f3_157 := min 1 (max (0 : Int) (5317958 + ((-1) * f2_0)))
  let f3_158 := min 1 (max (0 : Int) ((-100975812) + (1 * f2_0)))
  let f3_159 := min 1 (max (0 : Int) (100975814 + ((-1) * f2_0)))
  let f3_160 := min 1 (max (0 : Int) ((-129631) + (1 * f2_0)))
  let f3_161 := min 1 (max (0 : Int) (129633 + ((-1) * f2_0)))
  let f4_0 := min 1 (max (0 : Int) ((-32) + (1 * f3_0) + (1 * f3_1) + (1 * f3_2) + (1 * f3_3) + (1 * f3_4) + (1 * f3_5) + (1 * f3_6) + (1 * f3_7) + (1 * f3_8) + (1 * f3_9) + (1 * f3_10) + (1 * f3_11) + (1 * f3_12) + (1 * f3_13) + (1 * f3_14) + (1 * f3_15) + (1 * f3_16) + (1 * f3_17) + (1 * f3_18) + (1 * f3_19) + (1 * f3_20) + (1 * f3_21) + (1 * f3_22) + (1 * f3_23) + (1 * f3_24) + (1 * f3_25) + (1 * f3_26) + (1 * f3_27) + (1 * f3_28) + (1 * f3_29) + (1 * f3_30) + (1 * f3_31) + (1 * f3_32) + (1 * f3_33) + (1 * f3_34) + (1 * f3_35) + (1 * f3_36) + (1 * f3_37) + (1 * f3_38) + (1 * f3_39) + (1 * f3_40) + (1 * f3_41) + (1 * f3_42) + (1 * f3_43) + (1 * f3_44) + (1 * f3_45) + (1 * f3_46) + (1 * f3_47) + (1 * f3_48) + (1 * f3_49) + (1 * f3_50) + (1 * f3_51) + (1 * f3_52) + (1 * f3_53) + (1 * f3_54) + (1 * f3_55) + (1 * f3_56) + (1 * f3_57) + (1 * f3_70) + (1 * f3_71) + (1 * f3_72) + (1 * f3_73) + (1 * f3_86) + (1 * f3_87) + ((-1) * f2_1)))
  let f4_1 := min 1 (max (0 : Int) ((-3) + (1 * f3_58) + (1 * f3_59) + (1 * f3_60) + (1 * f3_61)))
  let f4_2 := min 1 (max (0 : Int) ((-3) + (1 * f3_62) + (1 * f3_63) + (1 * f3_64) + (1 * f3_65)))
  let f4_3 := min 1 (max (0 : Int) ((-3) + (1 * f3_66) + (1 * f3_67) + (1 * f3_68) + (1 * f3_69)))
  let f4_4 := min 1 (max (0 : Int) ((-3) + (1 * f3_74) + (1 * f3_75) + (1 * f3_76) + (1 * f3_77)))
  let f4_5 := min 1 (max (0 : Int) ((-3) + (1 * f3_78) + (1 * f3_79) + (1 * f3_80) + (1 * f3_81)))
  let f4_6 := min 1 (max (0 : Int) ((-3) + (1 * f3_82) + (1 * f3_83) + (1 * f3_84) + (1 * f3_85)))
  let f4_7 := min 1 (max (0 : Int) ((-29) + (1 * f3_88) + (1 * f3_89) + (1 * f3_90) + (1 * f3_91) + (1 * f3_92) + (1 * f3_93) + (1 * f3_94) + (1 * f3_95) + (1 * f3_96) + (1 * f3_97) + (1 * f3_98) + (1 * f3_99) + (1 * f3_100) + (1 * f3_101) + (1 * f3_102) + (1 * f3_103) + (1 * f3_104) + (1 * f3_105) + (1 * f3_106) + (1 * f3_107) + (1 * f3_108) + (1 * f3_109) + (1 * f3_110) + (1 * f3_111) + (1 * f3_112) + (1 * f3_113) + (1 * f3_114) + (1 * f3_115) + (1 * f3_120) + (1 * f3_121) + (1 * f3_124) + (1 * f3_125) + (1 * f3_126) + (1 * f3_127) + (1 * f3_128) + (1 * f3_129) + (1 * f3_130) + (1 * f3_131) + (1 * f3_132) + (1 * f3_133) + (1 * f3_134) + (1 * f3_135) + (1 * f3_136) + (1 * f3_137) + (1 * f3_138) + (1 * f3_139) + (1 * f3_140) + (1 * f3_141) + (1 * f3_142) + (1 * f3_143) + (1 * f3_144) + (1 * f3_145) + (1 * f3_146) + (1 * f3_147) + (1 * f3_148) + (1 * f3_149) + (1 * f3_150) + (1 * f3_151) + ((-1) * f2_1)))
  let f4_8 := min 1 (max (0 : Int) ((-3) + (1 * f3_116) + (1 * f3_117) + (1 * f3_118) + (1 * f3_119)))
  let f4_9 := min 1 (max (0 : Int) ((-3) + (1 * f3_118) + (1 * f3_119) + (1 * f3_122) + (1 * f3_123)))
  let f4_10 := min 1 (max (0 : Int) ((-5) + (1 * f3_152) + (1 * f3_153) + (1 * f3_154) + (1 * f3_155) + (1 * f3_156) + (1 * f3_157) + (1 * f3_158) + (1 * f3_159) + (1 * f3_160) + (1 * f3_161) + ((-1) * f2_1)))
  let f5_0 := min 1 (max (0 : Int) (0 + (1 * f4_0) + (1 * f4_1) + (1 * f4_2) + (1 * f4_3) + (1 * f4_4) + (1 * f4_5) + (1 * f4_6)))
  let f5_1 := min 1 (max (0 : Int) (0 + (1 * f4_7) + (1 * f4_8) + (1 * f4_9)))
  let f5_2 := min 1 (max (0 : Int) (0 + (1 * f4_10)))
  (f5_0, f5_1, f5_2)
def tab0 : List Int := [349455, 38293579, 791749, 54322388, 14240302032197, 280347628308, 271, 1361093, 1369421, 5776626830, 25554, 1897743, 582, 9901740933, 79516106834258, 79529175978196, 19416568974, 20558926790, 20736983619, 20741443796, 20789412040, 1401502843206, 356029390, 97800722354949, 388010757, 278945393860691, 278945393861574, 4358657593923, 279350277907011, 81757266003, 81757266886, 21898482630]
def tab7 : List Int := [819282, 4552139525, 103870548, 37780, 3208071, 320926868, 20553982276, 93341603389764, 5829188, 586700, 1064367052, 279086123499864, 20558929876, 1326228987860, 40566239866836, 1583903748052, 21629263828, 253259732, 270815188, 9904054228, 633857621972, 633858129876, 633858924500, 1453013065684, 92992834355156, 92992834863060, 92992835657684, 8534431, 1513962378452]
def tab10 : List Int := [10680742, 984825791762, 5317957, 100975813, 129632]
def grp0Rows (A B : Int) : List Int := [rowA tab0 A B, rowAB 279842118780242 14 A B, rowAB 280190803546367 1397511316 A B, rowAB 280246919369023 205271116 A B, rowAB 14240288101904 18 A B, rowAB 84938684907457 323769492 A B, rowAB 88530097557452 3944524 A B]
def grp1Rows (A B : Int) : List Int := [rowA tab7 A B, rowAB 71762530558399 20 A B, rowBA 20 92992824231103 B A]
def grp2Rows (A B : Int) : List Int := [rowA tab10 A B]
def flagsS (f2_0 f2_1 : Int) : Int × Int × Int :=
  let g0 := clip1 (lin 0 ((grp0Rows f2_0 f2_1).map fun r => (1, r)))
  let g1 := clip1 (lin 0 ((grp1Rows f2_0 f2_1).map fun r => (1, r)))
  let g2 := clip1 (lin 0 ((grp2Rows f2_0 f2_1).map fun r => (1, r)))
  (g0, g1, g2)
theorem flags_link (A B : Int) : flagsOf A B = flagsS A B := by rfl
def kwP : List (Int × Int) := [(279842118780242, 14), (280190803546367, 1397511316), (280246919369023, 205271116), (14240288101904, 18), (84938684907457, 323769492), (88530097557452, 3944524)]
def tyP : List (Int × Int) := [(71762530558399, 20), (92992824231103, 20)]
theorem kw_char (A B : Int) (hB : 0 ≤ B) : (flagsOf A B).1 = 1 ↔ ((A ∈ tab0 ∧ B = 0) ∨ (A, B) ∈ kwP) := by
  rw [flags_link]
  show clip1 (lin 0 ((grp0Rows A B).map fun r => (1, r))) = 1 ↔ _
  have e0 := rowA_iff tab0 (by decide) A B hB
  have z0 := rowA_01 tab0 A B
  have e1 := rowAB_iff 279842118780242 14 A B
  have z1 := rowAB_01 279842118780242 14 A B
  have e2 := rowAB_iff 280190803546367 1397511316 A B
  have z2 := rowAB_01 280190803546367 1397511316 A B
  have e3 := rowAB_iff 280246919369023 205271116 A B
  have z3 := rowAB_01 280246919369023 205271116 A B
  have e4 := rowAB_iff 14240288101904 18 A B
  have z4 := rowAB_01 14240288101904 18 A B
  have e5 := rowAB_iff 84938684907457 323769492 A B
  have z5 := rowAB_01 84938684907457 323769492 A B
  have e6 := rowAB_iff 88530097557452 3944524 A B
  have z6 := rowAB_01 88530097557452 3944524 A B
  rw [grp_iff _ (by simp only [grp0Rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨z0, z1, z2, z3, z4, z5, z6⟩)]
  simp only [grp0Rows, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, e0, e1, e2, e3, e4, e5, e6, kwP, Prod.mk.injEq]
theorem ty_char (A B : Int) (hB : 0 ≤ B) : (flagsOf A B).2.1 = 1 ↔ ((A ∈ tab7 ∧ B = 0) ∨ (A, B) ∈ tyP) := by
  rw [flags_link]
  show clip1 (lin 0 ((grp1Rows A B).map fun r => (1, r))) = 1 ↔ _
  have e0 := rowA_iff tab7 (by decide) A B hB
  have z0 := rowA_01 tab7 A B
  have e8 := rowAB_iff 71762530558399 20 A B
  have z8 := rowAB_01 71762530558399 20 A B
  have e9 := rowBA_iff 20 92992824231103 B A
  have z9 := rowBA_01 20 92992824231103 B A
  rw [grp_iff _ (by simp only [grp1Rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨z0, z8, z9⟩)]
  simp only [grp1Rows, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, e0, e8, e9, tyP, Prod.mk.injEq]
theorem const_char (A B : Int) (hB : 0 ≤ B) : (flagsOf A B).2.2 = 1 ↔ (A ∈ tab10 ∧ B = 0) := by
  rw [flags_link]
  show clip1 (lin 0 ((grp2Rows A B).map fun r => (1, r))) = 1 ↔ _
  have e0 := rowA_iff tab10 (by decide) A B hB
  have z0 := rowA_01 tab10 A B
  rw [grp_iff _ (by simp only [grp2Rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact z0)]
  simp only [grp2Rows, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, e0]
end Lexnet
