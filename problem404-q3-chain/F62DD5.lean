import ExactF62
import F62DataS
import F62DataC
import F62DataD1
import F62DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 5).
theorem fz_dcr_126_1 : dedupAux fz_CH_126_1 fz_A_126_1 = fz_S_127 := by decide +kernel
theorem fz_dd_126 : dedupAux fz_L_126 [] = fz_S_127 := fz_dcr_126_1
theorem fz_dcr_127_1 : dedupAux fz_CH_127_1 fz_A_127_1 = fz_S_128 := by decide +kernel
theorem fz_dd_127 : dedupAux fz_L_127 [] = fz_S_128 := fz_dcr_127_1
theorem fz_dcr_128_1 : dedupAux fz_CH_128_1 fz_A_128_1 = fz_S_129 := by decide +kernel
theorem fz_dd_128 : dedupAux fz_L_128 [] = fz_S_129 := fz_dcr_128_1
