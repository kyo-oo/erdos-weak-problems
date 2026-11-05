import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 8).
theorem fz_dcr_206_1 : dedupAux fz_CH_206_1 fz_A_206_1 = fz_S_207 := by decide +kernel
theorem fz_dd_206 : dedupAux fz_L_206 [] = fz_S_207 := fz_dcr_206_1
theorem fz_dcr_207_1 : dedupAux fz_CH_207_1 fz_A_207_1 = fz_S_208 := by decide +kernel
theorem fz_dd_207 : dedupAux fz_L_207 [] = fz_S_208 := fz_dcr_207_1
theorem fz_dcr_208_1 : dedupAux fz_CH_208_1 fz_A_208_1 = fz_S_209 := by decide +kernel
theorem fz_dd_208 : dedupAux fz_L_208 [] = fz_S_209 := fz_dcr_208_1
theorem fz_dcr_209_1 : dedupAux fz_CH_209_1 fz_A_209_1 = fz_S_210 := by decide +kernel
theorem fz_dd_209 : dedupAux fz_L_209 [] = fz_S_210 := fz_dcr_209_1
theorem fz_dcr_210_1 : dedupAux fz_CH_210_1 fz_A_210_1 = fz_S_211 := by decide +kernel
theorem fz_dd_210 : dedupAux fz_L_210 [] = fz_S_211 := fz_dcr_210_1
theorem fz_dcr_211_1 : dedupAux fz_CH_211_1 fz_A_211_1 = fz_S_212 := by decide +kernel
theorem fz_dd_211 : dedupAux fz_L_211 [] = fz_S_212 := fz_dcr_211_1
theorem fz_dcr_212_1 : dedupAux fz_CH_212_1 fz_A_212_1 = fz_S_213 := by decide +kernel
theorem fz_dd_212 : dedupAux fz_L_212 [] = fz_S_213 := fz_dcr_212_1
theorem fz_dcr_213_1 : dedupAux fz_CH_213_1 fz_A_213_1 = fz_S_214 := by decide +kernel
theorem fz_dd_213 : dedupAux fz_L_213 [] = fz_S_214 := fz_dcr_213_1
theorem fz_dcr_214_1 : dedupAux fz_CH_214_1 fz_A_214_1 = fz_S_215 := by decide +kernel
theorem fz_dd_214 : dedupAux fz_L_214 [] = fz_S_215 := fz_dcr_214_1
theorem fz_dcr_215_1 : dedupAux fz_CH_215_1 fz_A_215_1 = fz_S_216 := by decide +kernel
theorem fz_dd_215 : dedupAux fz_L_215 [] = fz_S_216 := fz_dcr_215_1
theorem fz_dcr_216_1 : dedupAux fz_CH_216_1 fz_A_216_1 = fz_S_217 := by decide +kernel
theorem fz_dd_216 : dedupAux fz_L_216 [] = fz_S_217 := fz_dcr_216_1
theorem fz_dcr_217_1 : dedupAux fz_CH_217_1 fz_A_217_1 = fz_S_218 := by decide +kernel
theorem fz_dd_217 : dedupAux fz_L_217 [] = fz_S_218 := fz_dcr_217_1
theorem fz_dcr_218_1 : dedupAux fz_CH_218_1 fz_A_218_1 = fz_S_219 := by decide +kernel
theorem fz_dd_218 : dedupAux fz_L_218 [] = fz_S_219 := fz_dcr_218_1
theorem fz_dcr_219_1 : dedupAux fz_CH_219_1 fz_A_219_1 = fz_S_220 := by decide +kernel
theorem fz_dd_219 : dedupAux fz_L_219 [] = fz_S_220 := fz_dcr_219_1
theorem fz_dcr_220_1 : dedupAux fz_CH_220_1 fz_A_220_1 = fz_S_221 := by decide +kernel
theorem fz_dd_220 : dedupAux fz_L_220 [] = fz_S_221 := fz_dcr_220_1
theorem fz_dcr_221_1 : dedupAux fz_CH_221_1 fz_A_221_1 = fz_S_222 := by decide +kernel
theorem fz_dd_221 : dedupAux fz_L_221 [] = fz_S_222 := fz_dcr_221_1
theorem fz_dcr_222_1 : dedupAux fz_CH_222_1 fz_A_222_1 = fz_S_223 := by decide +kernel
theorem fz_dd_222 : dedupAux fz_L_222 [] = fz_S_223 := fz_dcr_222_1
theorem fz_dcr_223_1 : dedupAux fz_CH_223_1 fz_A_223_1 = fz_S_224 := by decide +kernel
theorem fz_dd_223 : dedupAux fz_L_223 [] = fz_S_224 := fz_dcr_223_1
theorem fz_dcr_224_1 : dedupAux fz_CH_224_1 fz_A_224_1 = fz_S_225 := by decide +kernel
theorem fz_dd_224 : dedupAux fz_L_224 [] = fz_S_225 := fz_dcr_224_1
theorem fz_dcr_225_1 : dedupAux fz_CH_225_1 fz_A_225_1 = fz_S_226 := by decide +kernel
theorem fz_dd_225 : dedupAux fz_L_225 [] = fz_S_226 := fz_dcr_225_1
theorem fz_dcr_226_1 : dedupAux fz_CH_226_1 fz_A_226_1 = fz_S_227 := by decide +kernel
theorem fz_dd_226 : dedupAux fz_L_226 [] = fz_S_227 := fz_dcr_226_1
theorem fz_dcr_227_1 : dedupAux fz_CH_227_1 fz_A_227_1 = fz_S_228 := by decide +kernel
theorem fz_dd_227 : dedupAux fz_L_227 [] = fz_S_228 := fz_dcr_227_1
theorem fz_dcr_228_1 : dedupAux fz_CH_228_1 fz_A_228_1 = fz_S_229 := by decide +kernel
theorem fz_dd_228 : dedupAux fz_L_228 [] = fz_S_229 := fz_dcr_228_1
theorem fz_dcr_229_1 : dedupAux fz_CH_229_1 fz_A_229_1 = fz_S_230 := by decide +kernel
theorem fz_dd_229 : dedupAux fz_L_229 [] = fz_S_230 := fz_dcr_229_1
theorem fz_dcr_230_1 : dedupAux fz_CH_230_1 fz_A_230_1 = fz_S_231 := by decide +kernel
theorem fz_dd_230 : dedupAux fz_L_230 [] = fz_S_231 := fz_dcr_230_1
