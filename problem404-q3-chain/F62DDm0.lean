import ExactF62
import F62DataS
import F62DataC
import F62DataD1
import F62DataD2
import F62Chain

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- multi-chunk round 120 (2 chunks).
theorem fz_dcr_120_1 : dedupAux fz_CH_120_1 fz_A_120_1 = fz_A_120_2 := by decide +kernel
theorem fz_dcr_120_2 : dedupAux fz_CH_120_2 fz_A_120_2 = fz_S_121 := by decide +kernel
theorem fz_dd_120 : dedupAux fz_L_120 [] = fz_S_121 := by
  show dedupAux (fz_CH_120_1 ++ fz_CH_120_2) fz_A_120_1 = fz_S_121
  rw [fz_ddA, fz_dcr_120_1, fz_dcr_120_2]
