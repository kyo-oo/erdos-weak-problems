import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 5).
theorem fz_dcr_130_1 : dedupAux fz_CH_130_1 fz_A_130_1 = fz_S_131 := by decide +kernel
theorem fz_dd_130 : dedupAux fz_L_130 [] = fz_S_131 := fz_dcr_130_1
theorem fz_dcr_131_1 : dedupAux fz_CH_131_1 fz_A_131_1 = fz_S_132 := by decide +kernel
theorem fz_dd_131 : dedupAux fz_L_131 [] = fz_S_132 := fz_dcr_131_1
theorem fz_dcr_132_1 : dedupAux fz_CH_132_1 fz_A_132_1 = fz_S_133 := by decide +kernel
theorem fz_dd_132 : dedupAux fz_L_132 [] = fz_S_133 := fz_dcr_132_1
theorem fz_dcr_133_1 : dedupAux fz_CH_133_1 fz_A_133_1 = fz_S_134 := by decide +kernel
theorem fz_dd_133 : dedupAux fz_L_133 [] = fz_S_134 := fz_dcr_133_1
theorem fz_dcr_134_1 : dedupAux fz_CH_134_1 fz_A_134_1 = fz_S_135 := by decide +kernel
theorem fz_dd_134 : dedupAux fz_L_134 [] = fz_S_135 := fz_dcr_134_1
theorem fz_dcr_135_1 : dedupAux fz_CH_135_1 fz_A_135_1 = fz_S_136 := by decide +kernel
theorem fz_dd_135 : dedupAux fz_L_135 [] = fz_S_136 := fz_dcr_135_1
theorem fz_dcr_136_1 : dedupAux fz_CH_136_1 fz_A_136_1 = fz_S_137 := by decide +kernel
theorem fz_dd_136 : dedupAux fz_L_136 [] = fz_S_137 := fz_dcr_136_1
theorem fz_dcr_137_1 : dedupAux fz_CH_137_1 fz_A_137_1 = fz_S_138 := by decide +kernel
theorem fz_dd_137 : dedupAux fz_L_137 [] = fz_S_138 := fz_dcr_137_1
theorem fz_dcr_138_1 : dedupAux fz_CH_138_1 fz_A_138_1 = fz_S_139 := by decide +kernel
theorem fz_dd_138 : dedupAux fz_L_138 [] = fz_S_139 := fz_dcr_138_1
theorem fz_dcr_139_1 : dedupAux fz_CH_139_1 fz_A_139_1 = fz_S_140 := by decide +kernel
theorem fz_dd_139 : dedupAux fz_L_139 [] = fz_S_140 := fz_dcr_139_1
theorem fz_dcr_140_1 : dedupAux fz_CH_140_1 fz_A_140_1 = fz_S_141 := by decide +kernel
theorem fz_dd_140 : dedupAux fz_L_140 [] = fz_S_141 := fz_dcr_140_1
theorem fz_dcr_141_1 : dedupAux fz_CH_141_1 fz_A_141_1 = fz_S_142 := by decide +kernel
theorem fz_dd_141 : dedupAux fz_L_141 [] = fz_S_142 := fz_dcr_141_1
theorem fz_dcr_142_1 : dedupAux fz_CH_142_1 fz_A_142_1 = fz_S_143 := by decide +kernel
theorem fz_dd_142 : dedupAux fz_L_142 [] = fz_S_143 := fz_dcr_142_1
theorem fz_dcr_143_1 : dedupAux fz_CH_143_1 fz_A_143_1 = fz_S_144 := by decide +kernel
theorem fz_dd_143 : dedupAux fz_L_143 [] = fz_S_144 := fz_dcr_143_1
theorem fz_dcr_144_1 : dedupAux fz_CH_144_1 fz_A_144_1 = fz_S_145 := by decide +kernel
theorem fz_dd_144 : dedupAux fz_L_144 [] = fz_S_145 := fz_dcr_144_1
theorem fz_dcr_145_1 : dedupAux fz_CH_145_1 fz_A_145_1 = fz_S_146 := by decide +kernel
theorem fz_dd_145 : dedupAux fz_L_145 [] = fz_S_146 := fz_dcr_145_1
theorem fz_dcr_146_1 : dedupAux fz_CH_146_1 fz_A_146_1 = fz_S_147 := by decide +kernel
theorem fz_dd_146 : dedupAux fz_L_146 [] = fz_S_147 := fz_dcr_146_1
theorem fz_dcr_147_1 : dedupAux fz_CH_147_1 fz_A_147_1 = fz_S_148 := by decide +kernel
theorem fz_dd_147 : dedupAux fz_L_147 [] = fz_S_148 := fz_dcr_147_1
theorem fz_dcr_148_1 : dedupAux fz_CH_148_1 fz_A_148_1 = fz_S_149 := by decide +kernel
theorem fz_dd_148 : dedupAux fz_L_148 [] = fz_S_149 := fz_dcr_148_1
theorem fz_dcr_149_1 : dedupAux fz_CH_149_1 fz_A_149_1 = fz_S_150 := by decide +kernel
theorem fz_dd_149 : dedupAux fz_L_149 [] = fz_S_150 := fz_dcr_149_1
theorem fz_dcr_150_1 : dedupAux fz_CH_150_1 fz_A_150_1 = fz_S_151 := by decide +kernel
theorem fz_dd_150 : dedupAux fz_L_150 [] = fz_S_151 := fz_dcr_150_1
theorem fz_dcr_151_1 : dedupAux fz_CH_151_1 fz_A_151_1 = fz_S_152 := by decide +kernel
theorem fz_dd_151 : dedupAux fz_L_151 [] = fz_S_152 := fz_dcr_151_1
theorem fz_dcr_152_1 : dedupAux fz_CH_152_1 fz_A_152_1 = fz_S_153 := by decide +kernel
theorem fz_dd_152 : dedupAux fz_L_152 [] = fz_S_153 := fz_dcr_152_1
theorem fz_dcr_153_1 : dedupAux fz_CH_153_1 fz_A_153_1 = fz_S_154 := by decide +kernel
theorem fz_dd_153 : dedupAux fz_L_153 [] = fz_S_154 := fz_dcr_153_1
theorem fz_dcr_154_1 : dedupAux fz_CH_154_1 fz_A_154_1 = fz_S_155 := by decide +kernel
theorem fz_dd_154 : dedupAux fz_L_154 [] = fz_S_155 := fz_dcr_154_1
