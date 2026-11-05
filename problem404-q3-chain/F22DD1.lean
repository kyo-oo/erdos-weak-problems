import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 1).
theorem fz_dcr_25_1 : dedupAux fz_CH_25_1 fz_A_25_1 = fz_S_26 := by decide +kernel
theorem fz_dd_25 : dedupAux fz_L_25 [] = fz_S_26 := fz_dcr_25_1
theorem fz_dcr_26_1 : dedupAux fz_CH_26_1 fz_A_26_1 = fz_S_27 := by decide +kernel
theorem fz_dd_26 : dedupAux fz_L_26 [] = fz_S_27 := fz_dcr_26_1
theorem fz_dcr_27_1 : dedupAux fz_CH_27_1 fz_A_27_1 = fz_S_28 := by decide +kernel
theorem fz_dd_27 : dedupAux fz_L_27 [] = fz_S_28 := fz_dcr_27_1
theorem fz_dcr_28_1 : dedupAux fz_CH_28_1 fz_A_28_1 = fz_S_29 := by decide +kernel
theorem fz_dd_28 : dedupAux fz_L_28 [] = fz_S_29 := fz_dcr_28_1
theorem fz_dcr_29_1 : dedupAux fz_CH_29_1 fz_A_29_1 = fz_S_30 := by decide +kernel
theorem fz_dd_29 : dedupAux fz_L_29 [] = fz_S_30 := fz_dcr_29_1
theorem fz_dcr_30_1 : dedupAux fz_CH_30_1 fz_A_30_1 = fz_S_31 := by decide +kernel
theorem fz_dd_30 : dedupAux fz_L_30 [] = fz_S_31 := fz_dcr_30_1
theorem fz_dcr_31_1 : dedupAux fz_CH_31_1 fz_A_31_1 = fz_S_32 := by decide +kernel
theorem fz_dd_31 : dedupAux fz_L_31 [] = fz_S_32 := fz_dcr_31_1
theorem fz_dcr_32_1 : dedupAux fz_CH_32_1 fz_A_32_1 = fz_S_33 := by decide +kernel
theorem fz_dd_32 : dedupAux fz_L_32 [] = fz_S_33 := fz_dcr_32_1
theorem fz_dcr_33_1 : dedupAux fz_CH_33_1 fz_A_33_1 = fz_S_34 := by decide +kernel
theorem fz_dd_33 : dedupAux fz_L_33 [] = fz_S_34 := fz_dcr_33_1
theorem fz_dcr_34_1 : dedupAux fz_CH_34_1 fz_A_34_1 = fz_S_35 := by decide +kernel
theorem fz_dd_34 : dedupAux fz_L_34 [] = fz_S_35 := fz_dcr_34_1
theorem fz_dcr_35_1 : dedupAux fz_CH_35_1 fz_A_35_1 = fz_S_36 := by decide +kernel
theorem fz_dd_35 : dedupAux fz_L_35 [] = fz_S_36 := fz_dcr_35_1
theorem fz_dcr_36_1 : dedupAux fz_CH_36_1 fz_A_36_1 = fz_S_37 := by decide +kernel
theorem fz_dd_36 : dedupAux fz_L_36 [] = fz_S_37 := fz_dcr_36_1
theorem fz_dcr_37_1 : dedupAux fz_CH_37_1 fz_A_37_1 = fz_S_38 := by decide +kernel
theorem fz_dd_37 : dedupAux fz_L_37 [] = fz_S_38 := fz_dcr_37_1
theorem fz_dcr_38_1 : dedupAux fz_CH_38_1 fz_A_38_1 = fz_S_39 := by decide +kernel
theorem fz_dd_38 : dedupAux fz_L_38 [] = fz_S_39 := fz_dcr_38_1
theorem fz_dcr_39_1 : dedupAux fz_CH_39_1 fz_A_39_1 = fz_S_40 := by decide +kernel
theorem fz_dd_39 : dedupAux fz_L_39 [] = fz_S_40 := fz_dcr_39_1
theorem fz_dcr_40_1 : dedupAux fz_CH_40_1 fz_A_40_1 = fz_S_41 := by decide +kernel
theorem fz_dd_40 : dedupAux fz_L_40 [] = fz_S_41 := fz_dcr_40_1
theorem fz_dcr_41_1 : dedupAux fz_CH_41_1 fz_A_41_1 = fz_S_42 := by decide +kernel
theorem fz_dd_41 : dedupAux fz_L_41 [] = fz_S_42 := fz_dcr_41_1
theorem fz_dcr_42_1 : dedupAux fz_CH_42_1 fz_A_42_1 = fz_S_43 := by decide +kernel
theorem fz_dd_42 : dedupAux fz_L_42 [] = fz_S_43 := fz_dcr_42_1
theorem fz_dcr_43_1 : dedupAux fz_CH_43_1 fz_A_43_1 = fz_S_44 := by decide +kernel
theorem fz_dd_43 : dedupAux fz_L_43 [] = fz_S_44 := fz_dcr_43_1
theorem fz_dcr_44_1 : dedupAux fz_CH_44_1 fz_A_44_1 = fz_S_45 := by decide +kernel
theorem fz_dd_44 : dedupAux fz_L_44 [] = fz_S_45 := fz_dcr_44_1
theorem fz_dcr_45_1 : dedupAux fz_CH_45_1 fz_A_45_1 = fz_S_46 := by decide +kernel
theorem fz_dd_45 : dedupAux fz_L_45 [] = fz_S_46 := fz_dcr_45_1
theorem fz_dcr_46_1 : dedupAux fz_CH_46_1 fz_A_46_1 = fz_S_47 := by decide +kernel
theorem fz_dd_46 : dedupAux fz_L_46 [] = fz_S_47 := fz_dcr_46_1
theorem fz_dcr_47_1 : dedupAux fz_CH_47_1 fz_A_47_1 = fz_S_48 := by decide +kernel
theorem fz_dd_47 : dedupAux fz_L_47 [] = fz_S_48 := fz_dcr_47_1
theorem fz_dcr_48_1 : dedupAux fz_CH_48_1 fz_A_48_1 = fz_S_49 := by decide +kernel
theorem fz_dd_48 : dedupAux fz_L_48 [] = fz_S_49 := fz_dcr_48_1
theorem fz_dcr_49_1 : dedupAux fz_CH_49_1 fz_A_49_1 = fz_S_50 := by decide +kernel
theorem fz_dd_49 : dedupAux fz_L_49 [] = fz_S_50 := fz_dcr_49_1
