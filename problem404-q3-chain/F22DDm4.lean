import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2
import F22Chain

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- multi-chunk round 124 (9 chunks).
theorem fz_dcr_124_1 : dedupAux fz_CH_124_1 fz_A_124_1 = fz_A_124_2 := by decide +kernel
theorem fz_dcr_124_2 : dedupAux fz_CH_124_2 fz_A_124_2 = fz_A_124_3 := by decide +kernel
theorem fz_dcr_124_3 : dedupAux fz_CH_124_3 fz_A_124_3 = fz_A_124_4 := by decide +kernel
theorem fz_dcr_124_4 : dedupAux fz_CH_124_4 fz_A_124_4 = fz_A_124_5 := by decide +kernel
theorem fz_dcr_124_5 : dedupAux fz_CH_124_5 fz_A_124_5 = fz_A_124_6 := by decide +kernel
theorem fz_dcr_124_6 : dedupAux fz_CH_124_6 fz_A_124_6 = fz_A_124_7 := by decide +kernel
theorem fz_dcr_124_7 : dedupAux fz_CH_124_7 fz_A_124_7 = fz_A_124_8 := by decide +kernel
theorem fz_dcr_124_8 : dedupAux fz_CH_124_8 fz_A_124_8 = fz_A_124_9 := by decide +kernel
theorem fz_dcr_124_9 : dedupAux fz_CH_124_9 fz_A_124_9 = fz_S_125 := by decide +kernel
theorem fz_dd_124 : dedupAux fz_L_124 [] = fz_S_125 := by
  show dedupAux (fz_CH_124_1 ++ (fz_CH_124_2 ++ (fz_CH_124_3 ++ (fz_CH_124_4 ++ (fz_CH_124_5 ++ (fz_CH_124_6 ++ (fz_CH_124_7 ++ (fz_CH_124_8 ++ fz_CH_124_9)))))))) fz_A_124_1 = fz_S_125
  rw [fz_ddA, fz_dcr_124_1, fz_ddA, fz_dcr_124_2, fz_ddA, fz_dcr_124_3, fz_ddA, fz_dcr_124_4, fz_ddA, fz_dcr_124_5, fz_ddA, fz_dcr_124_6, fz_ddA, fz_dcr_124_7, fz_ddA, fz_dcr_124_8, fz_dcr_124_9]
