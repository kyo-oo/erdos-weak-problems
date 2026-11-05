import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 7).
theorem fz_dcr_180_1 : dedupAux fz_CH_180_1 fz_A_180_1 = fz_S_181 := by decide +kernel
theorem fz_dd_180 : dedupAux fz_L_180 [] = fz_S_181 := fz_dcr_180_1
theorem fz_dcr_181_1 : dedupAux fz_CH_181_1 fz_A_181_1 = fz_S_182 := by decide +kernel
theorem fz_dd_181 : dedupAux fz_L_181 [] = fz_S_182 := fz_dcr_181_1
theorem fz_dcr_182_1 : dedupAux fz_CH_182_1 fz_A_182_1 = fz_S_183 := by decide +kernel
theorem fz_dd_182 : dedupAux fz_L_182 [] = fz_S_183 := fz_dcr_182_1
theorem fz_dcr_183_1 : dedupAux fz_CH_183_1 fz_A_183_1 = fz_S_184 := by decide +kernel
theorem fz_dd_183 : dedupAux fz_L_183 [] = fz_S_184 := fz_dcr_183_1
theorem fz_dcr_184_1 : dedupAux fz_CH_184_1 fz_A_184_1 = fz_S_185 := by decide +kernel
theorem fz_dd_184 : dedupAux fz_L_184 [] = fz_S_185 := fz_dcr_184_1
theorem fz_dcr_185_1 : dedupAux fz_CH_185_1 fz_A_185_1 = fz_S_186 := by decide +kernel
theorem fz_dd_185 : dedupAux fz_L_185 [] = fz_S_186 := fz_dcr_185_1
theorem fz_dcr_186_1 : dedupAux fz_CH_186_1 fz_A_186_1 = fz_S_187 := by decide +kernel
theorem fz_dd_186 : dedupAux fz_L_186 [] = fz_S_187 := fz_dcr_186_1
theorem fz_dcr_187_1 : dedupAux fz_CH_187_1 fz_A_187_1 = fz_S_188 := by decide +kernel
theorem fz_dd_187 : dedupAux fz_L_187 [] = fz_S_188 := fz_dcr_187_1
theorem fz_dcr_189_1 : dedupAux fz_CH_189_1 fz_A_189_1 = fz_S_190 := by decide +kernel
theorem fz_dd_189 : dedupAux fz_L_189 [] = fz_S_190 := fz_dcr_189_1
theorem fz_dcr_190_1 : dedupAux fz_CH_190_1 fz_A_190_1 = fz_S_191 := by decide +kernel
theorem fz_dd_190 : dedupAux fz_L_190 [] = fz_S_191 := fz_dcr_190_1
theorem fz_dcr_191_1 : dedupAux fz_CH_191_1 fz_A_191_1 = fz_S_192 := by decide +kernel
theorem fz_dd_191 : dedupAux fz_L_191 [] = fz_S_192 := fz_dcr_191_1
theorem fz_dcr_192_1 : dedupAux fz_CH_192_1 fz_A_192_1 = fz_S_193 := by decide +kernel
theorem fz_dd_192 : dedupAux fz_L_192 [] = fz_S_193 := fz_dcr_192_1
theorem fz_dcr_193_1 : dedupAux fz_CH_193_1 fz_A_193_1 = fz_S_194 := by decide +kernel
theorem fz_dd_193 : dedupAux fz_L_193 [] = fz_S_194 := fz_dcr_193_1
theorem fz_dcr_194_1 : dedupAux fz_CH_194_1 fz_A_194_1 = fz_S_195 := by decide +kernel
theorem fz_dd_194 : dedupAux fz_L_194 [] = fz_S_195 := fz_dcr_194_1
theorem fz_dcr_195_1 : dedupAux fz_CH_195_1 fz_A_195_1 = fz_S_196 := by decide +kernel
theorem fz_dd_195 : dedupAux fz_L_195 [] = fz_S_196 := fz_dcr_195_1
theorem fz_dcr_196_1 : dedupAux fz_CH_196_1 fz_A_196_1 = fz_S_197 := by decide +kernel
theorem fz_dd_196 : dedupAux fz_L_196 [] = fz_S_197 := fz_dcr_196_1
theorem fz_dcr_197_1 : dedupAux fz_CH_197_1 fz_A_197_1 = fz_S_198 := by decide +kernel
theorem fz_dd_197 : dedupAux fz_L_197 [] = fz_S_198 := fz_dcr_197_1
theorem fz_dcr_198_1 : dedupAux fz_CH_198_1 fz_A_198_1 = fz_S_199 := by decide +kernel
theorem fz_dd_198 : dedupAux fz_L_198 [] = fz_S_199 := fz_dcr_198_1
theorem fz_dcr_199_1 : dedupAux fz_CH_199_1 fz_A_199_1 = fz_S_200 := by decide +kernel
theorem fz_dd_199 : dedupAux fz_L_199 [] = fz_S_200 := fz_dcr_199_1
theorem fz_dcr_200_1 : dedupAux fz_CH_200_1 fz_A_200_1 = fz_S_201 := by decide +kernel
theorem fz_dd_200 : dedupAux fz_L_200 [] = fz_S_201 := fz_dcr_200_1
theorem fz_dcr_201_1 : dedupAux fz_CH_201_1 fz_A_201_1 = fz_S_202 := by decide +kernel
theorem fz_dd_201 : dedupAux fz_L_201 [] = fz_S_202 := fz_dcr_201_1
theorem fz_dcr_202_1 : dedupAux fz_CH_202_1 fz_A_202_1 = fz_S_203 := by decide +kernel
theorem fz_dd_202 : dedupAux fz_L_202 [] = fz_S_203 := fz_dcr_202_1
theorem fz_dcr_203_1 : dedupAux fz_CH_203_1 fz_A_203_1 = fz_S_204 := by decide +kernel
theorem fz_dd_203 : dedupAux fz_L_203 [] = fz_S_204 := fz_dcr_203_1
theorem fz_dcr_204_1 : dedupAux fz_CH_204_1 fz_A_204_1 = fz_S_205 := by decide +kernel
theorem fz_dd_204 : dedupAux fz_L_204 [] = fz_S_205 := fz_dcr_204_1
theorem fz_dcr_205_1 : dedupAux fz_CH_205_1 fz_A_205_1 = fz_S_206 := by decide +kernel
theorem fz_dd_205 : dedupAux fz_L_205 [] = fz_S_206 := fz_dcr_205_1
