import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2
import F22Chain

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- multi-chunk round 252 (2 chunks).
theorem fz_dcr_252_1 : dedupAux fz_CH_252_1 fz_A_252_1 = fz_A_252_2 := by decide +kernel
theorem fz_dcr_252_2 : dedupAux fz_CH_252_2 fz_A_252_2 = fz_S_253 := by decide +kernel
theorem fz_dd_252 : dedupAux fz_L_252 [] = fz_S_253 := by
  show dedupAux (fz_CH_252_1 ++ fz_CH_252_2) fz_A_252_1 = fz_S_253
  rw [fz_ddA, fz_dcr_252_1, fz_dcr_252_2]
