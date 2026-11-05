import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 0).
theorem fz_dcr_0_1 : dedupAux fz_CH_0_1 fz_A_0_1 = fz_S_1 := by decide +kernel
theorem fz_dd_0 : dedupAux fz_L_0 [] = fz_S_1 := fz_dcr_0_1
theorem fz_dcr_1_1 : dedupAux fz_CH_1_1 fz_A_1_1 = fz_S_2 := by decide +kernel
theorem fz_dd_1 : dedupAux fz_L_1 [] = fz_S_2 := fz_dcr_1_1
theorem fz_dcr_2_1 : dedupAux fz_CH_2_1 fz_A_2_1 = fz_S_3 := by decide +kernel
theorem fz_dd_2 : dedupAux fz_L_2 [] = fz_S_3 := fz_dcr_2_1
theorem fz_dcr_3_1 : dedupAux fz_CH_3_1 fz_A_3_1 = fz_S_4 := by decide +kernel
theorem fz_dd_3 : dedupAux fz_L_3 [] = fz_S_4 := fz_dcr_3_1
theorem fz_dcr_4_1 : dedupAux fz_CH_4_1 fz_A_4_1 = fz_S_5 := by decide +kernel
theorem fz_dd_4 : dedupAux fz_L_4 [] = fz_S_5 := fz_dcr_4_1
theorem fz_dcr_5_1 : dedupAux fz_CH_5_1 fz_A_5_1 = fz_S_6 := by decide +kernel
theorem fz_dd_5 : dedupAux fz_L_5 [] = fz_S_6 := fz_dcr_5_1
theorem fz_dcr_6_1 : dedupAux fz_CH_6_1 fz_A_6_1 = fz_S_7 := by decide +kernel
theorem fz_dd_6 : dedupAux fz_L_6 [] = fz_S_7 := fz_dcr_6_1
theorem fz_dcr_7_1 : dedupAux fz_CH_7_1 fz_A_7_1 = fz_S_8 := by decide +kernel
theorem fz_dd_7 : dedupAux fz_L_7 [] = fz_S_8 := fz_dcr_7_1
theorem fz_dcr_8_1 : dedupAux fz_CH_8_1 fz_A_8_1 = fz_S_9 := by decide +kernel
theorem fz_dd_8 : dedupAux fz_L_8 [] = fz_S_9 := fz_dcr_8_1
theorem fz_dcr_9_1 : dedupAux fz_CH_9_1 fz_A_9_1 = fz_S_10 := by decide +kernel
theorem fz_dd_9 : dedupAux fz_L_9 [] = fz_S_10 := fz_dcr_9_1
theorem fz_dcr_10_1 : dedupAux fz_CH_10_1 fz_A_10_1 = fz_S_11 := by decide +kernel
theorem fz_dd_10 : dedupAux fz_L_10 [] = fz_S_11 := fz_dcr_10_1
theorem fz_dcr_11_1 : dedupAux fz_CH_11_1 fz_A_11_1 = fz_S_12 := by decide +kernel
theorem fz_dd_11 : dedupAux fz_L_11 [] = fz_S_12 := fz_dcr_11_1
theorem fz_dcr_12_1 : dedupAux fz_CH_12_1 fz_A_12_1 = fz_S_13 := by decide +kernel
theorem fz_dd_12 : dedupAux fz_L_12 [] = fz_S_13 := fz_dcr_12_1
theorem fz_dcr_13_1 : dedupAux fz_CH_13_1 fz_A_13_1 = fz_S_14 := by decide +kernel
theorem fz_dd_13 : dedupAux fz_L_13 [] = fz_S_14 := fz_dcr_13_1
theorem fz_dcr_14_1 : dedupAux fz_CH_14_1 fz_A_14_1 = fz_S_15 := by decide +kernel
theorem fz_dd_14 : dedupAux fz_L_14 [] = fz_S_15 := fz_dcr_14_1
theorem fz_dcr_15_1 : dedupAux fz_CH_15_1 fz_A_15_1 = fz_S_16 := by decide +kernel
theorem fz_dd_15 : dedupAux fz_L_15 [] = fz_S_16 := fz_dcr_15_1
theorem fz_dcr_16_1 : dedupAux fz_CH_16_1 fz_A_16_1 = fz_S_17 := by decide +kernel
theorem fz_dd_16 : dedupAux fz_L_16 [] = fz_S_17 := fz_dcr_16_1
theorem fz_dcr_17_1 : dedupAux fz_CH_17_1 fz_A_17_1 = fz_S_18 := by decide +kernel
theorem fz_dd_17 : dedupAux fz_L_17 [] = fz_S_18 := fz_dcr_17_1
theorem fz_dcr_18_1 : dedupAux fz_CH_18_1 fz_A_18_1 = fz_S_19 := by decide +kernel
theorem fz_dd_18 : dedupAux fz_L_18 [] = fz_S_19 := fz_dcr_18_1
theorem fz_dcr_19_1 : dedupAux fz_CH_19_1 fz_A_19_1 = fz_S_20 := by decide +kernel
theorem fz_dd_19 : dedupAux fz_L_19 [] = fz_S_20 := fz_dcr_19_1
theorem fz_dcr_20_1 : dedupAux fz_CH_20_1 fz_A_20_1 = fz_S_21 := by decide +kernel
theorem fz_dd_20 : dedupAux fz_L_20 [] = fz_S_21 := fz_dcr_20_1
theorem fz_dcr_21_1 : dedupAux fz_CH_21_1 fz_A_21_1 = fz_S_22 := by decide +kernel
theorem fz_dd_21 : dedupAux fz_L_21 [] = fz_S_22 := fz_dcr_21_1
theorem fz_dcr_22_1 : dedupAux fz_CH_22_1 fz_A_22_1 = fz_S_23 := by decide +kernel
theorem fz_dd_22 : dedupAux fz_L_22 [] = fz_S_23 := fz_dcr_22_1
theorem fz_dcr_23_1 : dedupAux fz_CH_23_1 fz_A_23_1 = fz_S_24 := by decide +kernel
theorem fz_dd_23 : dedupAux fz_L_23 [] = fz_S_24 := fz_dcr_23_1
theorem fz_dcr_24_1 : dedupAux fz_CH_24_1 fz_A_24_1 = fz_S_25 := by decide +kernel
theorem fz_dd_24 : dedupAux fz_L_24 [] = fz_S_25 := fz_dcr_24_1
