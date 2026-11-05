import ExactF22
import F22DataS
import F22DataC
import F22DataD1
import F22DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- single-chunk dedup decides + chains (slice 4).
theorem fz_dcr_100_1 : dedupAux fz_CH_100_1 fz_A_100_1 = fz_S_101 := by decide +kernel
theorem fz_dd_100 : dedupAux fz_L_100 [] = fz_S_101 := fz_dcr_100_1
theorem fz_dcr_101_1 : dedupAux fz_CH_101_1 fz_A_101_1 = fz_S_102 := by decide +kernel
theorem fz_dd_101 : dedupAux fz_L_101 [] = fz_S_102 := fz_dcr_101_1
theorem fz_dcr_102_1 : dedupAux fz_CH_102_1 fz_A_102_1 = fz_S_103 := by decide +kernel
theorem fz_dd_102 : dedupAux fz_L_102 [] = fz_S_103 := fz_dcr_102_1
theorem fz_dcr_103_1 : dedupAux fz_CH_103_1 fz_A_103_1 = fz_S_104 := by decide +kernel
theorem fz_dd_103 : dedupAux fz_L_103 [] = fz_S_104 := fz_dcr_103_1
theorem fz_dcr_104_1 : dedupAux fz_CH_104_1 fz_A_104_1 = fz_S_105 := by decide +kernel
theorem fz_dd_104 : dedupAux fz_L_104 [] = fz_S_105 := fz_dcr_104_1
theorem fz_dcr_105_1 : dedupAux fz_CH_105_1 fz_A_105_1 = fz_S_106 := by decide +kernel
theorem fz_dd_105 : dedupAux fz_L_105 [] = fz_S_106 := fz_dcr_105_1
theorem fz_dcr_106_1 : dedupAux fz_CH_106_1 fz_A_106_1 = fz_S_107 := by decide +kernel
theorem fz_dd_106 : dedupAux fz_L_106 [] = fz_S_107 := fz_dcr_106_1
theorem fz_dcr_107_1 : dedupAux fz_CH_107_1 fz_A_107_1 = fz_S_108 := by decide +kernel
theorem fz_dd_107 : dedupAux fz_L_107 [] = fz_S_108 := fz_dcr_107_1
theorem fz_dcr_108_1 : dedupAux fz_CH_108_1 fz_A_108_1 = fz_S_109 := by decide +kernel
theorem fz_dd_108 : dedupAux fz_L_108 [] = fz_S_109 := fz_dcr_108_1
theorem fz_dcr_109_1 : dedupAux fz_CH_109_1 fz_A_109_1 = fz_S_110 := by decide +kernel
theorem fz_dd_109 : dedupAux fz_L_109 [] = fz_S_110 := fz_dcr_109_1
theorem fz_dcr_110_1 : dedupAux fz_CH_110_1 fz_A_110_1 = fz_S_111 := by decide +kernel
theorem fz_dd_110 : dedupAux fz_L_110 [] = fz_S_111 := fz_dcr_110_1
theorem fz_dcr_111_1 : dedupAux fz_CH_111_1 fz_A_111_1 = fz_S_112 := by decide +kernel
theorem fz_dd_111 : dedupAux fz_L_111 [] = fz_S_112 := fz_dcr_111_1
theorem fz_dcr_112_1 : dedupAux fz_CH_112_1 fz_A_112_1 = fz_S_113 := by decide +kernel
theorem fz_dd_112 : dedupAux fz_L_112 [] = fz_S_113 := fz_dcr_112_1
theorem fz_dcr_113_1 : dedupAux fz_CH_113_1 fz_A_113_1 = fz_S_114 := by decide +kernel
theorem fz_dd_113 : dedupAux fz_L_113 [] = fz_S_114 := fz_dcr_113_1
theorem fz_dcr_114_1 : dedupAux fz_CH_114_1 fz_A_114_1 = fz_S_115 := by decide +kernel
theorem fz_dd_114 : dedupAux fz_L_114 [] = fz_S_115 := fz_dcr_114_1
theorem fz_dcr_115_1 : dedupAux fz_CH_115_1 fz_A_115_1 = fz_S_116 := by decide +kernel
theorem fz_dd_115 : dedupAux fz_L_115 [] = fz_S_116 := fz_dcr_115_1
theorem fz_dcr_117_1 : dedupAux fz_CH_117_1 fz_A_117_1 = fz_S_118 := by decide +kernel
theorem fz_dd_117 : dedupAux fz_L_117 [] = fz_S_118 := fz_dcr_117_1
theorem fz_dcr_118_1 : dedupAux fz_CH_118_1 fz_A_118_1 = fz_S_119 := by decide +kernel
theorem fz_dd_118 : dedupAux fz_L_118 [] = fz_S_119 := fz_dcr_118_1
theorem fz_dcr_119_1 : dedupAux fz_CH_119_1 fz_A_119_1 = fz_S_120 := by decide +kernel
theorem fz_dd_119 : dedupAux fz_L_119 [] = fz_S_120 := fz_dcr_119_1
theorem fz_dcr_121_1 : dedupAux fz_CH_121_1 fz_A_121_1 = fz_S_122 := by decide +kernel
theorem fz_dd_121 : dedupAux fz_L_121 [] = fz_S_122 := fz_dcr_121_1
theorem fz_dcr_125_1 : dedupAux fz_CH_125_1 fz_A_125_1 = fz_S_126 := by decide +kernel
theorem fz_dd_125 : dedupAux fz_L_125 [] = fz_S_126 := fz_dcr_125_1
theorem fz_dcr_126_1 : dedupAux fz_CH_126_1 fz_A_126_1 = fz_S_127 := by decide +kernel
theorem fz_dd_126 : dedupAux fz_L_126 [] = fz_S_127 := fz_dcr_126_1
theorem fz_dcr_127_1 : dedupAux fz_CH_127_1 fz_A_127_1 = fz_S_128 := by decide +kernel
theorem fz_dd_127 : dedupAux fz_L_127 [] = fz_S_128 := fz_dcr_127_1
theorem fz_dcr_128_1 : dedupAux fz_CH_128_1 fz_A_128_1 = fz_S_129 := by decide +kernel
theorem fz_dd_128 : dedupAux fz_L_128 [] = fz_S_129 := fz_dcr_128_1
theorem fz_dcr_129_1 : dedupAux fz_CH_129_1 fz_A_129_1 = fz_S_130 := by decide +kernel
theorem fz_dd_129 : dedupAux fz_L_129 [] = fz_S_130 := fz_dcr_129_1
