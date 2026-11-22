import Ski.D2Base
import Ski.D2K.S372
/-! Generated.  Reassembles the S-law chunks: `slawChunk k = true` for all k < 2984. -/
namespace D2
theorem slawG_0 (k : Nat) (h1 : 0 ≤ k) (h2 : k < 160) : slawChunk k = true := by
  if h0 : k < 8 then exact slawC_0 k (by omega) h0 else
  if h1 : k < 16 then exact slawC_1 k (by omega) h1 else
  if h2 : k < 24 then exact slawC_2 k (by omega) h2 else
  if h3 : k < 32 then exact slawC_3 k (by omega) h3 else
  if h4 : k < 40 then exact slawC_4 k (by omega) h4 else
  if h5 : k < 48 then exact slawC_5 k (by omega) h5 else
  if h6 : k < 56 then exact slawC_6 k (by omega) h6 else
  if h7 : k < 64 then exact slawC_7 k (by omega) h7 else
  if h8 : k < 72 then exact slawC_8 k (by omega) h8 else
  if h9 : k < 80 then exact slawC_9 k (by omega) h9 else
  if h10 : k < 88 then exact slawC_10 k (by omega) h10 else
  if h11 : k < 96 then exact slawC_11 k (by omega) h11 else
  if h12 : k < 104 then exact slawC_12 k (by omega) h12 else
  if h13 : k < 112 then exact slawC_13 k (by omega) h13 else
  if h14 : k < 120 then exact slawC_14 k (by omega) h14 else
  if h15 : k < 128 then exact slawC_15 k (by omega) h15 else
  if h16 : k < 136 then exact slawC_16 k (by omega) h16 else
  if h17 : k < 144 then exact slawC_17 k (by omega) h17 else
  if h18 : k < 152 then exact slawC_18 k (by omega) h18 else
  if h19 : k < 160 then exact slawC_19 k (by omega) h19 else
  omega
theorem slawG_1 (k : Nat) (h1 : 160 ≤ k) (h2 : k < 320) : slawChunk k = true := by
  if h20 : k < 168 then exact slawC_20 k (by omega) h20 else
  if h21 : k < 176 then exact slawC_21 k (by omega) h21 else
  if h22 : k < 184 then exact slawC_22 k (by omega) h22 else
  if h23 : k < 192 then exact slawC_23 k (by omega) h23 else
  if h24 : k < 200 then exact slawC_24 k (by omega) h24 else
  if h25 : k < 208 then exact slawC_25 k (by omega) h25 else
  if h26 : k < 216 then exact slawC_26 k (by omega) h26 else
  if h27 : k < 224 then exact slawC_27 k (by omega) h27 else
  if h28 : k < 232 then exact slawC_28 k (by omega) h28 else
  if h29 : k < 240 then exact slawC_29 k (by omega) h29 else
  if h30 : k < 248 then exact slawC_30 k (by omega) h30 else
  if h31 : k < 256 then exact slawC_31 k (by omega) h31 else
  if h32 : k < 264 then exact slawC_32 k (by omega) h32 else
  if h33 : k < 272 then exact slawC_33 k (by omega) h33 else
  if h34 : k < 280 then exact slawC_34 k (by omega) h34 else
  if h35 : k < 288 then exact slawC_35 k (by omega) h35 else
  if h36 : k < 296 then exact slawC_36 k (by omega) h36 else
  if h37 : k < 304 then exact slawC_37 k (by omega) h37 else
  if h38 : k < 312 then exact slawC_38 k (by omega) h38 else
  if h39 : k < 320 then exact slawC_39 k (by omega) h39 else
  omega
theorem slawG_2 (k : Nat) (h1 : 320 ≤ k) (h2 : k < 480) : slawChunk k = true := by
  if h40 : k < 328 then exact slawC_40 k (by omega) h40 else
  if h41 : k < 336 then exact slawC_41 k (by omega) h41 else
  if h42 : k < 344 then exact slawC_42 k (by omega) h42 else
  if h43 : k < 352 then exact slawC_43 k (by omega) h43 else
  if h44 : k < 360 then exact slawC_44 k (by omega) h44 else
  if h45 : k < 368 then exact slawC_45 k (by omega) h45 else
  if h46 : k < 376 then exact slawC_46 k (by omega) h46 else
  if h47 : k < 384 then exact slawC_47 k (by omega) h47 else
  if h48 : k < 392 then exact slawC_48 k (by omega) h48 else
  if h49 : k < 400 then exact slawC_49 k (by omega) h49 else
  if h50 : k < 408 then exact slawC_50 k (by omega) h50 else
  if h51 : k < 416 then exact slawC_51 k (by omega) h51 else
  if h52 : k < 424 then exact slawC_52 k (by omega) h52 else
  if h53 : k < 432 then exact slawC_53 k (by omega) h53 else
  if h54 : k < 440 then exact slawC_54 k (by omega) h54 else
  if h55 : k < 448 then exact slawC_55 k (by omega) h55 else
  if h56 : k < 456 then exact slawC_56 k (by omega) h56 else
  if h57 : k < 464 then exact slawC_57 k (by omega) h57 else
  if h58 : k < 472 then exact slawC_58 k (by omega) h58 else
  if h59 : k < 480 then exact slawC_59 k (by omega) h59 else
  omega
theorem slawG_3 (k : Nat) (h1 : 480 ≤ k) (h2 : k < 640) : slawChunk k = true := by
  if h60 : k < 488 then exact slawC_60 k (by omega) h60 else
  if h61 : k < 496 then exact slawC_61 k (by omega) h61 else
  if h62 : k < 504 then exact slawC_62 k (by omega) h62 else
  if h63 : k < 512 then exact slawC_63 k (by omega) h63 else
  if h64 : k < 520 then exact slawC_64 k (by omega) h64 else
  if h65 : k < 528 then exact slawC_65 k (by omega) h65 else
  if h66 : k < 536 then exact slawC_66 k (by omega) h66 else
  if h67 : k < 544 then exact slawC_67 k (by omega) h67 else
  if h68 : k < 552 then exact slawC_68 k (by omega) h68 else
  if h69 : k < 560 then exact slawC_69 k (by omega) h69 else
  if h70 : k < 568 then exact slawC_70 k (by omega) h70 else
  if h71 : k < 576 then exact slawC_71 k (by omega) h71 else
  if h72 : k < 584 then exact slawC_72 k (by omega) h72 else
  if h73 : k < 592 then exact slawC_73 k (by omega) h73 else
  if h74 : k < 600 then exact slawC_74 k (by omega) h74 else
  if h75 : k < 608 then exact slawC_75 k (by omega) h75 else
  if h76 : k < 616 then exact slawC_76 k (by omega) h76 else
  if h77 : k < 624 then exact slawC_77 k (by omega) h77 else
  if h78 : k < 632 then exact slawC_78 k (by omega) h78 else
  if h79 : k < 640 then exact slawC_79 k (by omega) h79 else
  omega
theorem slawG_4 (k : Nat) (h1 : 640 ≤ k) (h2 : k < 800) : slawChunk k = true := by
  if h80 : k < 648 then exact slawC_80 k (by omega) h80 else
  if h81 : k < 656 then exact slawC_81 k (by omega) h81 else
  if h82 : k < 664 then exact slawC_82 k (by omega) h82 else
  if h83 : k < 672 then exact slawC_83 k (by omega) h83 else
  if h84 : k < 680 then exact slawC_84 k (by omega) h84 else
  if h85 : k < 688 then exact slawC_85 k (by omega) h85 else
  if h86 : k < 696 then exact slawC_86 k (by omega) h86 else
  if h87 : k < 704 then exact slawC_87 k (by omega) h87 else
  if h88 : k < 712 then exact slawC_88 k (by omega) h88 else
  if h89 : k < 720 then exact slawC_89 k (by omega) h89 else
  if h90 : k < 728 then exact slawC_90 k (by omega) h90 else
  if h91 : k < 736 then exact slawC_91 k (by omega) h91 else
  if h92 : k < 744 then exact slawC_92 k (by omega) h92 else
  if h93 : k < 752 then exact slawC_93 k (by omega) h93 else
  if h94 : k < 760 then exact slawC_94 k (by omega) h94 else
  if h95 : k < 768 then exact slawC_95 k (by omega) h95 else
  if h96 : k < 776 then exact slawC_96 k (by omega) h96 else
  if h97 : k < 784 then exact slawC_97 k (by omega) h97 else
  if h98 : k < 792 then exact slawC_98 k (by omega) h98 else
  if h99 : k < 800 then exact slawC_99 k (by omega) h99 else
  omega
theorem slawG_5 (k : Nat) (h1 : 800 ≤ k) (h2 : k < 960) : slawChunk k = true := by
  if h100 : k < 808 then exact slawC_100 k (by omega) h100 else
  if h101 : k < 816 then exact slawC_101 k (by omega) h101 else
  if h102 : k < 824 then exact slawC_102 k (by omega) h102 else
  if h103 : k < 832 then exact slawC_103 k (by omega) h103 else
  if h104 : k < 840 then exact slawC_104 k (by omega) h104 else
  if h105 : k < 848 then exact slawC_105 k (by omega) h105 else
  if h106 : k < 856 then exact slawC_106 k (by omega) h106 else
  if h107 : k < 864 then exact slawC_107 k (by omega) h107 else
  if h108 : k < 872 then exact slawC_108 k (by omega) h108 else
  if h109 : k < 880 then exact slawC_109 k (by omega) h109 else
  if h110 : k < 888 then exact slawC_110 k (by omega) h110 else
  if h111 : k < 896 then exact slawC_111 k (by omega) h111 else
  if h112 : k < 904 then exact slawC_112 k (by omega) h112 else
  if h113 : k < 912 then exact slawC_113 k (by omega) h113 else
  if h114 : k < 920 then exact slawC_114 k (by omega) h114 else
  if h115 : k < 928 then exact slawC_115 k (by omega) h115 else
  if h116 : k < 936 then exact slawC_116 k (by omega) h116 else
  if h117 : k < 944 then exact slawC_117 k (by omega) h117 else
  if h118 : k < 952 then exact slawC_118 k (by omega) h118 else
  if h119 : k < 960 then exact slawC_119 k (by omega) h119 else
  omega
theorem slawG_6 (k : Nat) (h1 : 960 ≤ k) (h2 : k < 1120) : slawChunk k = true := by
  if h120 : k < 968 then exact slawC_120 k (by omega) h120 else
  if h121 : k < 976 then exact slawC_121 k (by omega) h121 else
  if h122 : k < 984 then exact slawC_122 k (by omega) h122 else
  if h123 : k < 992 then exact slawC_123 k (by omega) h123 else
  if h124 : k < 1000 then exact slawC_124 k (by omega) h124 else
  if h125 : k < 1008 then exact slawC_125 k (by omega) h125 else
  if h126 : k < 1016 then exact slawC_126 k (by omega) h126 else
  if h127 : k < 1024 then exact slawC_127 k (by omega) h127 else
  if h128 : k < 1032 then exact slawC_128 k (by omega) h128 else
  if h129 : k < 1040 then exact slawC_129 k (by omega) h129 else
  if h130 : k < 1048 then exact slawC_130 k (by omega) h130 else
  if h131 : k < 1056 then exact slawC_131 k (by omega) h131 else
  if h132 : k < 1064 then exact slawC_132 k (by omega) h132 else
  if h133 : k < 1072 then exact slawC_133 k (by omega) h133 else
  if h134 : k < 1080 then exact slawC_134 k (by omega) h134 else
  if h135 : k < 1088 then exact slawC_135 k (by omega) h135 else
  if h136 : k < 1096 then exact slawC_136 k (by omega) h136 else
  if h137 : k < 1104 then exact slawC_137 k (by omega) h137 else
  if h138 : k < 1112 then exact slawC_138 k (by omega) h138 else
  if h139 : k < 1120 then exact slawC_139 k (by omega) h139 else
  omega
theorem slawG_7 (k : Nat) (h1 : 1120 ≤ k) (h2 : k < 1280) : slawChunk k = true := by
  if h140 : k < 1128 then exact slawC_140 k (by omega) h140 else
  if h141 : k < 1136 then exact slawC_141 k (by omega) h141 else
  if h142 : k < 1144 then exact slawC_142 k (by omega) h142 else
  if h143 : k < 1152 then exact slawC_143 k (by omega) h143 else
  if h144 : k < 1160 then exact slawC_144 k (by omega) h144 else
  if h145 : k < 1168 then exact slawC_145 k (by omega) h145 else
  if h146 : k < 1176 then exact slawC_146 k (by omega) h146 else
  if h147 : k < 1184 then exact slawC_147 k (by omega) h147 else
  if h148 : k < 1192 then exact slawC_148 k (by omega) h148 else
  if h149 : k < 1200 then exact slawC_149 k (by omega) h149 else
  if h150 : k < 1208 then exact slawC_150 k (by omega) h150 else
  if h151 : k < 1216 then exact slawC_151 k (by omega) h151 else
  if h152 : k < 1224 then exact slawC_152 k (by omega) h152 else
  if h153 : k < 1232 then exact slawC_153 k (by omega) h153 else
  if h154 : k < 1240 then exact slawC_154 k (by omega) h154 else
  if h155 : k < 1248 then exact slawC_155 k (by omega) h155 else
  if h156 : k < 1256 then exact slawC_156 k (by omega) h156 else
  if h157 : k < 1264 then exact slawC_157 k (by omega) h157 else
  if h158 : k < 1272 then exact slawC_158 k (by omega) h158 else
  if h159 : k < 1280 then exact slawC_159 k (by omega) h159 else
  omega
theorem slawG_8 (k : Nat) (h1 : 1280 ≤ k) (h2 : k < 1440) : slawChunk k = true := by
  if h160 : k < 1288 then exact slawC_160 k (by omega) h160 else
  if h161 : k < 1296 then exact slawC_161 k (by omega) h161 else
  if h162 : k < 1304 then exact slawC_162 k (by omega) h162 else
  if h163 : k < 1312 then exact slawC_163 k (by omega) h163 else
  if h164 : k < 1320 then exact slawC_164 k (by omega) h164 else
  if h165 : k < 1328 then exact slawC_165 k (by omega) h165 else
  if h166 : k < 1336 then exact slawC_166 k (by omega) h166 else
  if h167 : k < 1344 then exact slawC_167 k (by omega) h167 else
  if h168 : k < 1352 then exact slawC_168 k (by omega) h168 else
  if h169 : k < 1360 then exact slawC_169 k (by omega) h169 else
  if h170 : k < 1368 then exact slawC_170 k (by omega) h170 else
  if h171 : k < 1376 then exact slawC_171 k (by omega) h171 else
  if h172 : k < 1384 then exact slawC_172 k (by omega) h172 else
  if h173 : k < 1392 then exact slawC_173 k (by omega) h173 else
  if h174 : k < 1400 then exact slawC_174 k (by omega) h174 else
  if h175 : k < 1408 then exact slawC_175 k (by omega) h175 else
  if h176 : k < 1416 then exact slawC_176 k (by omega) h176 else
  if h177 : k < 1424 then exact slawC_177 k (by omega) h177 else
  if h178 : k < 1432 then exact slawC_178 k (by omega) h178 else
  if h179 : k < 1440 then exact slawC_179 k (by omega) h179 else
  omega
theorem slawG_9 (k : Nat) (h1 : 1440 ≤ k) (h2 : k < 1600) : slawChunk k = true := by
  if h180 : k < 1448 then exact slawC_180 k (by omega) h180 else
  if h181 : k < 1456 then exact slawC_181 k (by omega) h181 else
  if h182 : k < 1464 then exact slawC_182 k (by omega) h182 else
  if h183 : k < 1472 then exact slawC_183 k (by omega) h183 else
  if h184 : k < 1480 then exact slawC_184 k (by omega) h184 else
  if h185 : k < 1488 then exact slawC_185 k (by omega) h185 else
  if h186 : k < 1496 then exact slawC_186 k (by omega) h186 else
  if h187 : k < 1504 then exact slawC_187 k (by omega) h187 else
  if h188 : k < 1512 then exact slawC_188 k (by omega) h188 else
  if h189 : k < 1520 then exact slawC_189 k (by omega) h189 else
  if h190 : k < 1528 then exact slawC_190 k (by omega) h190 else
  if h191 : k < 1536 then exact slawC_191 k (by omega) h191 else
  if h192 : k < 1544 then exact slawC_192 k (by omega) h192 else
  if h193 : k < 1552 then exact slawC_193 k (by omega) h193 else
  if h194 : k < 1560 then exact slawC_194 k (by omega) h194 else
  if h195 : k < 1568 then exact slawC_195 k (by omega) h195 else
  if h196 : k < 1576 then exact slawC_196 k (by omega) h196 else
  if h197 : k < 1584 then exact slawC_197 k (by omega) h197 else
  if h198 : k < 1592 then exact slawC_198 k (by omega) h198 else
  if h199 : k < 1600 then exact slawC_199 k (by omega) h199 else
  omega
theorem slawG_10 (k : Nat) (h1 : 1600 ≤ k) (h2 : k < 1760) : slawChunk k = true := by
  if h200 : k < 1608 then exact slawC_200 k (by omega) h200 else
  if h201 : k < 1616 then exact slawC_201 k (by omega) h201 else
  if h202 : k < 1624 then exact slawC_202 k (by omega) h202 else
  if h203 : k < 1632 then exact slawC_203 k (by omega) h203 else
  if h204 : k < 1640 then exact slawC_204 k (by omega) h204 else
  if h205 : k < 1648 then exact slawC_205 k (by omega) h205 else
  if h206 : k < 1656 then exact slawC_206 k (by omega) h206 else
  if h207 : k < 1664 then exact slawC_207 k (by omega) h207 else
  if h208 : k < 1672 then exact slawC_208 k (by omega) h208 else
  if h209 : k < 1680 then exact slawC_209 k (by omega) h209 else
  if h210 : k < 1688 then exact slawC_210 k (by omega) h210 else
  if h211 : k < 1696 then exact slawC_211 k (by omega) h211 else
  if h212 : k < 1704 then exact slawC_212 k (by omega) h212 else
  if h213 : k < 1712 then exact slawC_213 k (by omega) h213 else
  if h214 : k < 1720 then exact slawC_214 k (by omega) h214 else
  if h215 : k < 1728 then exact slawC_215 k (by omega) h215 else
  if h216 : k < 1736 then exact slawC_216 k (by omega) h216 else
  if h217 : k < 1744 then exact slawC_217 k (by omega) h217 else
  if h218 : k < 1752 then exact slawC_218 k (by omega) h218 else
  if h219 : k < 1760 then exact slawC_219 k (by omega) h219 else
  omega
theorem slawG_11 (k : Nat) (h1 : 1760 ≤ k) (h2 : k < 1920) : slawChunk k = true := by
  if h220 : k < 1768 then exact slawC_220 k (by omega) h220 else
  if h221 : k < 1776 then exact slawC_221 k (by omega) h221 else
  if h222 : k < 1784 then exact slawC_222 k (by omega) h222 else
  if h223 : k < 1792 then exact slawC_223 k (by omega) h223 else
  if h224 : k < 1800 then exact slawC_224 k (by omega) h224 else
  if h225 : k < 1808 then exact slawC_225 k (by omega) h225 else
  if h226 : k < 1816 then exact slawC_226 k (by omega) h226 else
  if h227 : k < 1824 then exact slawC_227 k (by omega) h227 else
  if h228 : k < 1832 then exact slawC_228 k (by omega) h228 else
  if h229 : k < 1840 then exact slawC_229 k (by omega) h229 else
  if h230 : k < 1848 then exact slawC_230 k (by omega) h230 else
  if h231 : k < 1856 then exact slawC_231 k (by omega) h231 else
  if h232 : k < 1864 then exact slawC_232 k (by omega) h232 else
  if h233 : k < 1872 then exact slawC_233 k (by omega) h233 else
  if h234 : k < 1880 then exact slawC_234 k (by omega) h234 else
  if h235 : k < 1888 then exact slawC_235 k (by omega) h235 else
  if h236 : k < 1896 then exact slawC_236 k (by omega) h236 else
  if h237 : k < 1904 then exact slawC_237 k (by omega) h237 else
  if h238 : k < 1912 then exact slawC_238 k (by omega) h238 else
  if h239 : k < 1920 then exact slawC_239 k (by omega) h239 else
  omega
theorem slawG_12 (k : Nat) (h1 : 1920 ≤ k) (h2 : k < 2080) : slawChunk k = true := by
  if h240 : k < 1928 then exact slawC_240 k (by omega) h240 else
  if h241 : k < 1936 then exact slawC_241 k (by omega) h241 else
  if h242 : k < 1944 then exact slawC_242 k (by omega) h242 else
  if h243 : k < 1952 then exact slawC_243 k (by omega) h243 else
  if h244 : k < 1960 then exact slawC_244 k (by omega) h244 else
  if h245 : k < 1968 then exact slawC_245 k (by omega) h245 else
  if h246 : k < 1976 then exact slawC_246 k (by omega) h246 else
  if h247 : k < 1984 then exact slawC_247 k (by omega) h247 else
  if h248 : k < 1992 then exact slawC_248 k (by omega) h248 else
  if h249 : k < 2000 then exact slawC_249 k (by omega) h249 else
  if h250 : k < 2008 then exact slawC_250 k (by omega) h250 else
  if h251 : k < 2016 then exact slawC_251 k (by omega) h251 else
  if h252 : k < 2024 then exact slawC_252 k (by omega) h252 else
  if h253 : k < 2032 then exact slawC_253 k (by omega) h253 else
  if h254 : k < 2040 then exact slawC_254 k (by omega) h254 else
  if h255 : k < 2048 then exact slawC_255 k (by omega) h255 else
  if h256 : k < 2056 then exact slawC_256 k (by omega) h256 else
  if h257 : k < 2064 then exact slawC_257 k (by omega) h257 else
  if h258 : k < 2072 then exact slawC_258 k (by omega) h258 else
  if h259 : k < 2080 then exact slawC_259 k (by omega) h259 else
  omega
theorem slawG_13 (k : Nat) (h1 : 2080 ≤ k) (h2 : k < 2240) : slawChunk k = true := by
  if h260 : k < 2088 then exact slawC_260 k (by omega) h260 else
  if h261 : k < 2096 then exact slawC_261 k (by omega) h261 else
  if h262 : k < 2104 then exact slawC_262 k (by omega) h262 else
  if h263 : k < 2112 then exact slawC_263 k (by omega) h263 else
  if h264 : k < 2120 then exact slawC_264 k (by omega) h264 else
  if h265 : k < 2128 then exact slawC_265 k (by omega) h265 else
  if h266 : k < 2136 then exact slawC_266 k (by omega) h266 else
  if h267 : k < 2144 then exact slawC_267 k (by omega) h267 else
  if h268 : k < 2152 then exact slawC_268 k (by omega) h268 else
  if h269 : k < 2160 then exact slawC_269 k (by omega) h269 else
  if h270 : k < 2168 then exact slawC_270 k (by omega) h270 else
  if h271 : k < 2176 then exact slawC_271 k (by omega) h271 else
  if h272 : k < 2184 then exact slawC_272 k (by omega) h272 else
  if h273 : k < 2192 then exact slawC_273 k (by omega) h273 else
  if h274 : k < 2200 then exact slawC_274 k (by omega) h274 else
  if h275 : k < 2208 then exact slawC_275 k (by omega) h275 else
  if h276 : k < 2216 then exact slawC_276 k (by omega) h276 else
  if h277 : k < 2224 then exact slawC_277 k (by omega) h277 else
  if h278 : k < 2232 then exact slawC_278 k (by omega) h278 else
  if h279 : k < 2240 then exact slawC_279 k (by omega) h279 else
  omega
theorem slawG_14 (k : Nat) (h1 : 2240 ≤ k) (h2 : k < 2400) : slawChunk k = true := by
  if h280 : k < 2248 then exact slawC_280 k (by omega) h280 else
  if h281 : k < 2256 then exact slawC_281 k (by omega) h281 else
  if h282 : k < 2264 then exact slawC_282 k (by omega) h282 else
  if h283 : k < 2272 then exact slawC_283 k (by omega) h283 else
  if h284 : k < 2280 then exact slawC_284 k (by omega) h284 else
  if h285 : k < 2288 then exact slawC_285 k (by omega) h285 else
  if h286 : k < 2296 then exact slawC_286 k (by omega) h286 else
  if h287 : k < 2304 then exact slawC_287 k (by omega) h287 else
  if h288 : k < 2312 then exact slawC_288 k (by omega) h288 else
  if h289 : k < 2320 then exact slawC_289 k (by omega) h289 else
  if h290 : k < 2328 then exact slawC_290 k (by omega) h290 else
  if h291 : k < 2336 then exact slawC_291 k (by omega) h291 else
  if h292 : k < 2344 then exact slawC_292 k (by omega) h292 else
  if h293 : k < 2352 then exact slawC_293 k (by omega) h293 else
  if h294 : k < 2360 then exact slawC_294 k (by omega) h294 else
  if h295 : k < 2368 then exact slawC_295 k (by omega) h295 else
  if h296 : k < 2376 then exact slawC_296 k (by omega) h296 else
  if h297 : k < 2384 then exact slawC_297 k (by omega) h297 else
  if h298 : k < 2392 then exact slawC_298 k (by omega) h298 else
  if h299 : k < 2400 then exact slawC_299 k (by omega) h299 else
  omega
theorem slawG_15 (k : Nat) (h1 : 2400 ≤ k) (h2 : k < 2560) : slawChunk k = true := by
  if h300 : k < 2408 then exact slawC_300 k (by omega) h300 else
  if h301 : k < 2416 then exact slawC_301 k (by omega) h301 else
  if h302 : k < 2424 then exact slawC_302 k (by omega) h302 else
  if h303 : k < 2432 then exact slawC_303 k (by omega) h303 else
  if h304 : k < 2440 then exact slawC_304 k (by omega) h304 else
  if h305 : k < 2448 then exact slawC_305 k (by omega) h305 else
  if h306 : k < 2456 then exact slawC_306 k (by omega) h306 else
  if h307 : k < 2464 then exact slawC_307 k (by omega) h307 else
  if h308 : k < 2472 then exact slawC_308 k (by omega) h308 else
  if h309 : k < 2480 then exact slawC_309 k (by omega) h309 else
  if h310 : k < 2488 then exact slawC_310 k (by omega) h310 else
  if h311 : k < 2496 then exact slawC_311 k (by omega) h311 else
  if h312 : k < 2504 then exact slawC_312 k (by omega) h312 else
  if h313 : k < 2512 then exact slawC_313 k (by omega) h313 else
  if h314 : k < 2520 then exact slawC_314 k (by omega) h314 else
  if h315 : k < 2528 then exact slawC_315 k (by omega) h315 else
  if h316 : k < 2536 then exact slawC_316 k (by omega) h316 else
  if h317 : k < 2544 then exact slawC_317 k (by omega) h317 else
  if h318 : k < 2552 then exact slawC_318 k (by omega) h318 else
  if h319 : k < 2560 then exact slawC_319 k (by omega) h319 else
  omega
theorem slawG_16 (k : Nat) (h1 : 2560 ≤ k) (h2 : k < 2720) : slawChunk k = true := by
  if h320 : k < 2568 then exact slawC_320 k (by omega) h320 else
  if h321 : k < 2576 then exact slawC_321 k (by omega) h321 else
  if h322 : k < 2584 then exact slawC_322 k (by omega) h322 else
  if h323 : k < 2592 then exact slawC_323 k (by omega) h323 else
  if h324 : k < 2600 then exact slawC_324 k (by omega) h324 else
  if h325 : k < 2608 then exact slawC_325 k (by omega) h325 else
  if h326 : k < 2616 then exact slawC_326 k (by omega) h326 else
  if h327 : k < 2624 then exact slawC_327 k (by omega) h327 else
  if h328 : k < 2632 then exact slawC_328 k (by omega) h328 else
  if h329 : k < 2640 then exact slawC_329 k (by omega) h329 else
  if h330 : k < 2648 then exact slawC_330 k (by omega) h330 else
  if h331 : k < 2656 then exact slawC_331 k (by omega) h331 else
  if h332 : k < 2664 then exact slawC_332 k (by omega) h332 else
  if h333 : k < 2672 then exact slawC_333 k (by omega) h333 else
  if h334 : k < 2680 then exact slawC_334 k (by omega) h334 else
  if h335 : k < 2688 then exact slawC_335 k (by omega) h335 else
  if h336 : k < 2696 then exact slawC_336 k (by omega) h336 else
  if h337 : k < 2704 then exact slawC_337 k (by omega) h337 else
  if h338 : k < 2712 then exact slawC_338 k (by omega) h338 else
  if h339 : k < 2720 then exact slawC_339 k (by omega) h339 else
  omega
theorem slawG_17 (k : Nat) (h1 : 2720 ≤ k) (h2 : k < 2880) : slawChunk k = true := by
  if h340 : k < 2728 then exact slawC_340 k (by omega) h340 else
  if h341 : k < 2736 then exact slawC_341 k (by omega) h341 else
  if h342 : k < 2744 then exact slawC_342 k (by omega) h342 else
  if h343 : k < 2752 then exact slawC_343 k (by omega) h343 else
  if h344 : k < 2760 then exact slawC_344 k (by omega) h344 else
  if h345 : k < 2768 then exact slawC_345 k (by omega) h345 else
  if h346 : k < 2776 then exact slawC_346 k (by omega) h346 else
  if h347 : k < 2784 then exact slawC_347 k (by omega) h347 else
  if h348 : k < 2792 then exact slawC_348 k (by omega) h348 else
  if h349 : k < 2800 then exact slawC_349 k (by omega) h349 else
  if h350 : k < 2808 then exact slawC_350 k (by omega) h350 else
  if h351 : k < 2816 then exact slawC_351 k (by omega) h351 else
  if h352 : k < 2824 then exact slawC_352 k (by omega) h352 else
  if h353 : k < 2832 then exact slawC_353 k (by omega) h353 else
  if h354 : k < 2840 then exact slawC_354 k (by omega) h354 else
  if h355 : k < 2848 then exact slawC_355 k (by omega) h355 else
  if h356 : k < 2856 then exact slawC_356 k (by omega) h356 else
  if h357 : k < 2864 then exact slawC_357 k (by omega) h357 else
  if h358 : k < 2872 then exact slawC_358 k (by omega) h358 else
  if h359 : k < 2880 then exact slawC_359 k (by omega) h359 else
  omega
theorem slawG_18 (k : Nat) (h1 : 2880 ≤ k) (h2 : k < 2984) : slawChunk k = true := by
  if h360 : k < 2888 then exact slawC_360 k (by omega) h360 else
  if h361 : k < 2896 then exact slawC_361 k (by omega) h361 else
  if h362 : k < 2904 then exact slawC_362 k (by omega) h362 else
  if h363 : k < 2912 then exact slawC_363 k (by omega) h363 else
  if h364 : k < 2920 then exact slawC_364 k (by omega) h364 else
  if h365 : k < 2928 then exact slawC_365 k (by omega) h365 else
  if h366 : k < 2936 then exact slawC_366 k (by omega) h366 else
  if h367 : k < 2944 then exact slawC_367 k (by omega) h367 else
  if h368 : k < 2952 then exact slawC_368 k (by omega) h368 else
  if h369 : k < 2960 then exact slawC_369 k (by omega) h369 else
  if h370 : k < 2968 then exact slawC_370 k (by omega) h370 else
  if h371 : k < 2976 then exact slawC_371 k (by omega) h371 else
  if h372 : k < 2984 then exact slawC_372 k (by omega) h372 else
  omega
theorem slawChunk_all (k : Nat) (h : k < 2984) : slawChunk k = true := by
  if h0 : k < 160 then exact slawG_0 k (by omega) h0 else
  if h1 : k < 320 then exact slawG_1 k (by omega) h1 else
  if h2 : k < 480 then exact slawG_2 k (by omega) h2 else
  if h3 : k < 640 then exact slawG_3 k (by omega) h3 else
  if h4 : k < 800 then exact slawG_4 k (by omega) h4 else
  if h5 : k < 960 then exact slawG_5 k (by omega) h5 else
  if h6 : k < 1120 then exact slawG_6 k (by omega) h6 else
  if h7 : k < 1280 then exact slawG_7 k (by omega) h7 else
  if h8 : k < 1440 then exact slawG_8 k (by omega) h8 else
  if h9 : k < 1600 then exact slawG_9 k (by omega) h9 else
  if h10 : k < 1760 then exact slawG_10 k (by omega) h10 else
  if h11 : k < 1920 then exact slawG_11 k (by omega) h11 else
  if h12 : k < 2080 then exact slawG_12 k (by omega) h12 else
  if h13 : k < 2240 then exact slawG_13 k (by omega) h13 else
  if h14 : k < 2400 then exact slawG_14 k (by omega) h14 else
  if h15 : k < 2560 then exact slawG_15 k (by omega) h15 else
  if h16 : k < 2720 then exact slawG_16 k (by omega) h16 else
  if h17 : k < 2880 then exact slawG_17 k (by omega) h17 else
  if h18 : k < 2984 then exact slawG_18 k (by omega) h18 else
  omega
end D2
