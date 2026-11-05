import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 3).
theorem fz_dcr_75_1 : dedupAux fz_CH_75_1 fz_A_75_1 = fz_S_76 := by decide +kernel
theorem fz_dd_75 : dedupAux fz_L_75 [] = fz_S_76 := fz_dcr_75_1
theorem fz_dcr_76_1 : dedupAux fz_CH_76_1 fz_A_76_1 = fz_S_77 := by decide +kernel
theorem fz_dd_76 : dedupAux fz_L_76 [] = fz_S_77 := fz_dcr_76_1
theorem fz_dcr_77_1 : dedupAux fz_CH_77_1 fz_A_77_1 = fz_S_78 := by decide +kernel
theorem fz_dd_77 : dedupAux fz_L_77 [] = fz_S_78 := fz_dcr_77_1
theorem fz_dcr_78_1 : dedupAux fz_CH_78_1 fz_A_78_1 = fz_S_79 := by decide +kernel
theorem fz_dd_78 : dedupAux fz_L_78 [] = fz_S_79 := fz_dcr_78_1
theorem fz_dcr_79_1 : dedupAux fz_CH_79_1 fz_A_79_1 = fz_S_80 := by decide +kernel
theorem fz_dd_79 : dedupAux fz_L_79 [] = fz_S_80 := fz_dcr_79_1
theorem fz_dcr_80_1 : dedupAux fz_CH_80_1 fz_A_80_1 = fz_S_81 := by decide +kernel
theorem fz_dd_80 : dedupAux fz_L_80 [] = fz_S_81 := fz_dcr_80_1
theorem fz_dcr_81_1 : dedupAux fz_CH_81_1 fz_A_81_1 = fz_S_82 := by decide +kernel
theorem fz_dd_81 : dedupAux fz_L_81 [] = fz_S_82 := fz_dcr_81_1
theorem fz_dcr_82_1 : dedupAux fz_CH_82_1 fz_A_82_1 = fz_S_83 := by decide +kernel
theorem fz_dd_82 : dedupAux fz_L_82 [] = fz_S_83 := fz_dcr_82_1
theorem fz_dcr_83_1 : dedupAux fz_CH_83_1 fz_A_83_1 = fz_S_84 := by decide +kernel
theorem fz_dd_83 : dedupAux fz_L_83 [] = fz_S_84 := fz_dcr_83_1
theorem fz_dcr_84_1 : dedupAux fz_CH_84_1 fz_A_84_1 = fz_S_85 := by decide +kernel
theorem fz_dd_84 : dedupAux fz_L_84 [] = fz_S_85 := fz_dcr_84_1
theorem fz_dcr_85_1 : dedupAux fz_CH_85_1 fz_A_85_1 = fz_S_86 := by decide +kernel
theorem fz_dd_85 : dedupAux fz_L_85 [] = fz_S_86 := fz_dcr_85_1
theorem fz_dcr_86_1 : dedupAux fz_CH_86_1 fz_A_86_1 = fz_S_87 := by decide +kernel
theorem fz_dd_86 : dedupAux fz_L_86 [] = fz_S_87 := fz_dcr_86_1
theorem fz_dcr_87_1 : dedupAux fz_CH_87_1 fz_A_87_1 = fz_S_88 := by decide +kernel
theorem fz_dd_87 : dedupAux fz_L_87 [] = fz_S_88 := fz_dcr_87_1
theorem fz_dcr_88_1 : dedupAux fz_CH_88_1 fz_A_88_1 = fz_S_89 := by decide +kernel
theorem fz_dd_88 : dedupAux fz_L_88 [] = fz_S_89 := fz_dcr_88_1
theorem fz_dcr_89_1 : dedupAux fz_CH_89_1 fz_A_89_1 = fz_S_90 := by decide +kernel
theorem fz_dd_89 : dedupAux fz_L_89 [] = fz_S_90 := fz_dcr_89_1
theorem fz_dcr_90_1 : dedupAux fz_CH_90_1 fz_A_90_1 = fz_S_91 := by decide +kernel
theorem fz_dd_90 : dedupAux fz_L_90 [] = fz_S_91 := fz_dcr_90_1
theorem fz_dcr_91_1 : dedupAux fz_CH_91_1 fz_A_91_1 = fz_S_92 := by decide +kernel
theorem fz_dd_91 : dedupAux fz_L_91 [] = fz_S_92 := fz_dcr_91_1
theorem fz_dcr_92_1 : dedupAux fz_CH_92_1 fz_A_92_1 = fz_S_93 := by decide +kernel
theorem fz_dd_92 : dedupAux fz_L_92 [] = fz_S_93 := fz_dcr_92_1
theorem fz_dcr_93_1 : dedupAux fz_CH_93_1 fz_A_93_1 = fz_S_94 := by decide +kernel
theorem fz_dd_93 : dedupAux fz_L_93 [] = fz_S_94 := fz_dcr_93_1
theorem fz_dcr_94_1 : dedupAux fz_CH_94_1 fz_A_94_1 = fz_S_95 := by decide +kernel
theorem fz_dd_94 : dedupAux fz_L_94 [] = fz_S_95 := fz_dcr_94_1
theorem fz_dcr_95_1 : dedupAux fz_CH_95_1 fz_A_95_1 = fz_S_96 := by decide +kernel
theorem fz_dd_95 : dedupAux fz_L_95 [] = fz_S_96 := fz_dcr_95_1
theorem fz_dcr_96_1 : dedupAux fz_CH_96_1 fz_A_96_1 = fz_S_97 := by decide +kernel
theorem fz_dd_96 : dedupAux fz_L_96 [] = fz_S_97 := fz_dcr_96_1
theorem fz_dcr_97_1 : dedupAux fz_CH_97_1 fz_A_97_1 = fz_S_98 := by decide +kernel
theorem fz_dd_97 : dedupAux fz_L_97 [] = fz_S_98 := fz_dcr_97_1
theorem fz_dcr_98_1 : dedupAux fz_CH_98_1 fz_A_98_1 = fz_S_99 := by decide +kernel
theorem fz_dd_98 : dedupAux fz_L_98 [] = fz_S_99 := fz_dcr_98_1
theorem fz_dcr_99_1 : dedupAux fz_CH_99_1 fz_A_99_1 = fz_S_100 := by decide +kernel
theorem fz_dd_99 : dedupAux fz_L_99 [] = fz_S_100 := fz_dcr_99_1
