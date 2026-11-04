import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2
import F22Chain

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- multi-chunk round 123 (3 chunks).
theorem fz_dcr_123_1 : dedupAux fz_CH_123_1 fz_A_123_1 = fz_A_123_2 := by decide +kernel
theorem fz_dcr_123_2 : dedupAux fz_CH_123_2 fz_A_123_2 = fz_A_123_3 := by decide +kernel
theorem fz_dcr_123_3 : dedupAux fz_CH_123_3 fz_A_123_3 = fz_S_124 := by decide +kernel
theorem fz_dd_123 : dedupAux fz_L_123 [] = fz_S_124 := by
  show dedupAux (fz_CH_123_1 ++ (fz_CH_123_2 ++ fz_CH_123_3)) fz_A_123_1 = fz_S_124
  rw [fz_ddA, fz_dcr_123_1, fz_ddA, fz_dcr_123_2, fz_dcr_123_3]
