import ExactF62
import F62DataS
import F62DataC
import F62DataD1
import F62DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 2).
theorem fz_dcr_50_1 : dedupAux fz_CH_50_1 fz_A_50_1 = fz_S_51 := by decide +kernel
theorem fz_dd_50 : dedupAux fz_L_50 [] = fz_S_51 := fz_dcr_50_1
theorem fz_dcr_51_1 : dedupAux fz_CH_51_1 fz_A_51_1 = fz_S_52 := by decide +kernel
theorem fz_dd_51 : dedupAux fz_L_51 [] = fz_S_52 := fz_dcr_51_1
theorem fz_dcr_52_1 : dedupAux fz_CH_52_1 fz_A_52_1 = fz_S_53 := by decide +kernel
theorem fz_dd_52 : dedupAux fz_L_52 [] = fz_S_53 := fz_dcr_52_1
theorem fz_dcr_53_1 : dedupAux fz_CH_53_1 fz_A_53_1 = fz_S_54 := by decide +kernel
theorem fz_dd_53 : dedupAux fz_L_53 [] = fz_S_54 := fz_dcr_53_1
theorem fz_dcr_54_1 : dedupAux fz_CH_54_1 fz_A_54_1 = fz_S_55 := by decide +kernel
theorem fz_dd_54 : dedupAux fz_L_54 [] = fz_S_55 := fz_dcr_54_1
theorem fz_dcr_55_1 : dedupAux fz_CH_55_1 fz_A_55_1 = fz_S_56 := by decide +kernel
theorem fz_dd_55 : dedupAux fz_L_55 [] = fz_S_56 := fz_dcr_55_1
theorem fz_dcr_56_1 : dedupAux fz_CH_56_1 fz_A_56_1 = fz_S_57 := by decide +kernel
theorem fz_dd_56 : dedupAux fz_L_56 [] = fz_S_57 := fz_dcr_56_1
theorem fz_dcr_57_1 : dedupAux fz_CH_57_1 fz_A_57_1 = fz_S_58 := by decide +kernel
theorem fz_dd_57 : dedupAux fz_L_57 [] = fz_S_58 := fz_dcr_57_1
theorem fz_dcr_58_1 : dedupAux fz_CH_58_1 fz_A_58_1 = fz_S_59 := by decide +kernel
theorem fz_dd_58 : dedupAux fz_L_58 [] = fz_S_59 := fz_dcr_58_1
theorem fz_dcr_59_1 : dedupAux fz_CH_59_1 fz_A_59_1 = fz_S_60 := by decide +kernel
theorem fz_dd_59 : dedupAux fz_L_59 [] = fz_S_60 := fz_dcr_59_1
theorem fz_dcr_60_1 : dedupAux fz_CH_60_1 fz_A_60_1 = fz_S_61 := by decide +kernel
theorem fz_dd_60 : dedupAux fz_L_60 [] = fz_S_61 := fz_dcr_60_1
theorem fz_dcr_61_1 : dedupAux fz_CH_61_1 fz_A_61_1 = fz_S_62 := by decide +kernel
theorem fz_dd_61 : dedupAux fz_L_61 [] = fz_S_62 := fz_dcr_61_1
theorem fz_dcr_62_1 : dedupAux fz_CH_62_1 fz_A_62_1 = fz_S_63 := by decide +kernel
theorem fz_dd_62 : dedupAux fz_L_62 [] = fz_S_63 := fz_dcr_62_1
theorem fz_dcr_63_1 : dedupAux fz_CH_63_1 fz_A_63_1 = fz_S_64 := by decide +kernel
theorem fz_dd_63 : dedupAux fz_L_63 [] = fz_S_64 := fz_dcr_63_1
theorem fz_dcr_64_1 : dedupAux fz_CH_64_1 fz_A_64_1 = fz_S_65 := by decide +kernel
theorem fz_dd_64 : dedupAux fz_L_64 [] = fz_S_65 := fz_dcr_64_1
theorem fz_dcr_65_1 : dedupAux fz_CH_65_1 fz_A_65_1 = fz_S_66 := by decide +kernel
theorem fz_dd_65 : dedupAux fz_L_65 [] = fz_S_66 := fz_dcr_65_1
theorem fz_dcr_66_1 : dedupAux fz_CH_66_1 fz_A_66_1 = fz_S_67 := by decide +kernel
theorem fz_dd_66 : dedupAux fz_L_66 [] = fz_S_67 := fz_dcr_66_1
theorem fz_dcr_67_1 : dedupAux fz_CH_67_1 fz_A_67_1 = fz_S_68 := by decide +kernel
theorem fz_dd_67 : dedupAux fz_L_67 [] = fz_S_68 := fz_dcr_67_1
theorem fz_dcr_68_1 : dedupAux fz_CH_68_1 fz_A_68_1 = fz_S_69 := by decide +kernel
theorem fz_dd_68 : dedupAux fz_L_68 [] = fz_S_69 := fz_dcr_68_1
theorem fz_dcr_69_1 : dedupAux fz_CH_69_1 fz_A_69_1 = fz_S_70 := by decide +kernel
theorem fz_dd_69 : dedupAux fz_L_69 [] = fz_S_70 := fz_dcr_69_1
theorem fz_dcr_70_1 : dedupAux fz_CH_70_1 fz_A_70_1 = fz_S_71 := by decide +kernel
theorem fz_dd_70 : dedupAux fz_L_70 [] = fz_S_71 := fz_dcr_70_1
theorem fz_dcr_71_1 : dedupAux fz_CH_71_1 fz_A_71_1 = fz_S_72 := by decide +kernel
theorem fz_dd_71 : dedupAux fz_L_71 [] = fz_S_72 := fz_dcr_71_1
theorem fz_dcr_72_1 : dedupAux fz_CH_72_1 fz_A_72_1 = fz_S_73 := by decide +kernel
theorem fz_dd_72 : dedupAux fz_L_72 [] = fz_S_73 := fz_dcr_72_1
theorem fz_dcr_73_1 : dedupAux fz_CH_73_1 fz_A_73_1 = fz_S_74 := by decide +kernel
theorem fz_dd_73 : dedupAux fz_L_73 [] = fz_S_74 := fz_dcr_73_1
theorem fz_dcr_74_1 : dedupAux fz_CH_74_1 fz_A_74_1 = fz_S_75 := by decide +kernel
theorem fz_dd_74 : dedupAux fz_L_74 [] = fz_S_75 := fz_dcr_74_1
