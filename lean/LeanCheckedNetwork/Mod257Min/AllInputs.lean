import LeanCheckedNetwork.Mod257Min.Rows00
import LeanCheckedNetwork.Mod257Min.Rows01
import LeanCheckedNetwork.Mod257Min.Rows02
import LeanCheckedNetwork.Mod257Min.Rows03
import LeanCheckedNetwork.Mod257Min.Rows04
import LeanCheckedNetwork.Mod257Min.Rows05
import LeanCheckedNetwork.Mod257Min.Rows06
import LeanCheckedNetwork.Mod257Min.Rows07
import LeanCheckedNetwork.Mod257Min.Rows08
import LeanCheckedNetwork.Mod257Min.Rows09
import LeanCheckedNetwork.Mod257Min.Rows10
import LeanCheckedNetwork.Mod257Min.Rows11
import LeanCheckedNetwork.Mod257Min.Rows12
import LeanCheckedNetwork.Mod257Min.Rows13
import LeanCheckedNetwork.Mod257Min.Rows14
import LeanCheckedNetwork.Mod257Min.Rows15

/-!
# Mod257Min: right on every input

The network answers `(a + b) % 257` for all 66049 pairs `(a, b)`.
-/

namespace LeanCheckedNetwork.Mod257Min

theorem adds_mod_257 : ∀ a, a < 257 → ∀ b, b < 257 → answer a b = (a + b) % 257 := by
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
  | 113, _ => exact row_113
  | 114, _ => exact row_114
  | 115, _ => exact row_115
  | 116, _ => exact row_116
  | 117, _ => exact row_117
  | 118, _ => exact row_118
  | 119, _ => exact row_119
  | 120, _ => exact row_120
  | 121, _ => exact row_121
  | 122, _ => exact row_122
  | 123, _ => exact row_123
  | 124, _ => exact row_124
  | 125, _ => exact row_125
  | 126, _ => exact row_126
  | 127, _ => exact row_127
  | 128, _ => exact row_128
  | 129, _ => exact row_129
  | 130, _ => exact row_130
  | 131, _ => exact row_131
  | 132, _ => exact row_132
  | 133, _ => exact row_133
  | 134, _ => exact row_134
  | 135, _ => exact row_135
  | 136, _ => exact row_136
  | 137, _ => exact row_137
  | 138, _ => exact row_138
  | 139, _ => exact row_139
  | 140, _ => exact row_140
  | 141, _ => exact row_141
  | 142, _ => exact row_142
  | 143, _ => exact row_143
  | 144, _ => exact row_144
  | 145, _ => exact row_145
  | 146, _ => exact row_146
  | 147, _ => exact row_147
  | 148, _ => exact row_148
  | 149, _ => exact row_149
  | 150, _ => exact row_150
  | 151, _ => exact row_151
  | 152, _ => exact row_152
  | 153, _ => exact row_153
  | 154, _ => exact row_154
  | 155, _ => exact row_155
  | 156, _ => exact row_156
  | 157, _ => exact row_157
  | 158, _ => exact row_158
  | 159, _ => exact row_159
  | 160, _ => exact row_160
  | 161, _ => exact row_161
  | 162, _ => exact row_162
  | 163, _ => exact row_163
  | 164, _ => exact row_164
  | 165, _ => exact row_165
  | 166, _ => exact row_166
  | 167, _ => exact row_167
  | 168, _ => exact row_168
  | 169, _ => exact row_169
  | 170, _ => exact row_170
  | 171, _ => exact row_171
  | 172, _ => exact row_172
  | 173, _ => exact row_173
  | 174, _ => exact row_174
  | 175, _ => exact row_175
  | 176, _ => exact row_176
  | 177, _ => exact row_177
  | 178, _ => exact row_178
  | 179, _ => exact row_179
  | 180, _ => exact row_180
  | 181, _ => exact row_181
  | 182, _ => exact row_182
  | 183, _ => exact row_183
  | 184, _ => exact row_184
  | 185, _ => exact row_185
  | 186, _ => exact row_186
  | 187, _ => exact row_187
  | 188, _ => exact row_188
  | 189, _ => exact row_189
  | 190, _ => exact row_190
  | 191, _ => exact row_191
  | 192, _ => exact row_192
  | 193, _ => exact row_193
  | 194, _ => exact row_194
  | 195, _ => exact row_195
  | 196, _ => exact row_196
  | 197, _ => exact row_197
  | 198, _ => exact row_198
  | 199, _ => exact row_199
  | 200, _ => exact row_200
  | 201, _ => exact row_201
  | 202, _ => exact row_202
  | 203, _ => exact row_203
  | 204, _ => exact row_204
  | 205, _ => exact row_205
  | 206, _ => exact row_206
  | 207, _ => exact row_207
  | 208, _ => exact row_208
  | 209, _ => exact row_209
  | 210, _ => exact row_210
  | 211, _ => exact row_211
  | 212, _ => exact row_212
  | 213, _ => exact row_213
  | 214, _ => exact row_214
  | 215, _ => exact row_215
  | 216, _ => exact row_216
  | 217, _ => exact row_217
  | 218, _ => exact row_218
  | 219, _ => exact row_219
  | 220, _ => exact row_220
  | 221, _ => exact row_221
  | 222, _ => exact row_222
  | 223, _ => exact row_223
  | 224, _ => exact row_224
  | 225, _ => exact row_225
  | 226, _ => exact row_226
  | 227, _ => exact row_227
  | 228, _ => exact row_228
  | 229, _ => exact row_229
  | 230, _ => exact row_230
  | 231, _ => exact row_231
  | 232, _ => exact row_232
  | 233, _ => exact row_233
  | 234, _ => exact row_234
  | 235, _ => exact row_235
  | 236, _ => exact row_236
  | 237, _ => exact row_237
  | 238, _ => exact row_238
  | 239, _ => exact row_239
  | 240, _ => exact row_240
  | 241, _ => exact row_241
  | 242, _ => exact row_242
  | 243, _ => exact row_243
  | 244, _ => exact row_244
  | 245, _ => exact row_245
  | 246, _ => exact row_246
  | 247, _ => exact row_247
  | 248, _ => exact row_248
  | 249, _ => exact row_249
  | 250, _ => exact row_250
  | 251, _ => exact row_251
  | 252, _ => exact row_252
  | 253, _ => exact row_253
  | 254, _ => exact row_254
  | 255, _ => exact row_255
  | 256, _ => exact row_256
  | n + 257, h => exact absurd h (by omega)

end LeanCheckedNetwork.Mod257Min
