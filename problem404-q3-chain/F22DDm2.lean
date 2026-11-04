import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2
import F22Chain

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- multi-chunk round 122 (3 chunks).
theorem fz_dcr_122_1 : dedupAux fz_CH_122_1 fz_A_122_1 = fz_A_122_2 := by decide +kernel
theorem fz_dcr_122_2 : dedupAux fz_CH_122_2 fz_A_122_2 = fz_A_122_3 := by decide +kernel
theorem fz_dcr_122_3 : dedupAux fz_CH_122_3 fz_A_122_3 = fz_S_123 := by decide +kernel
theorem fz_dd_122 : dedupAux fz_L_122 [] = fz_S_123 := by
  show dedupAux (fz_CH_122_1 ++ (fz_CH_122_2 ++ fz_CH_122_3)) fz_A_122_1 = fz_S_123
  rw [fz_ddA, fz_dcr_122_1, fz_ddA, fz_dcr_122_2, fz_dcr_122_3]
