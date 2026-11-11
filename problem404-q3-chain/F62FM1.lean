import ExactF62
import F62DataS
import F62DataC
import F62DataD2

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- flatMap decides.
theorem fz_FM_65 : (fz_S_65.filter (fun st => decide (fz_C_65.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_65.2.1 st.1 st.2 fz_C_65.2.2]) = fz_L_65 := by decide +kernel
theorem fz_FM_66 : (fz_S_66.filter (fun st => decide (fz_C_66.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_66.2.1 st.1 st.2 fz_C_66.2.2]) = fz_L_66 := by decide +kernel
theorem fz_FM_67 : (fz_S_67.filter (fun st => decide (fz_C_67.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_67.2.1 st.1 st.2 fz_C_67.2.2]) = fz_L_67 := by decide +kernel
theorem fz_FM_68 : (fz_S_68.filter (fun st => decide (fz_C_68.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_68.2.1 st.1 st.2 fz_C_68.2.2]) = fz_L_68 := by decide +kernel
theorem fz_FM_69 : (fz_S_69.filter (fun st => decide (fz_C_69.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_69.2.1 st.1 st.2 fz_C_69.2.2]) = fz_L_69 := by decide +kernel
theorem fz_FM_70 : (fz_S_70.filter (fun st => decide (fz_C_70.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_70.2.1 st.1 st.2 fz_C_70.2.2]) = fz_L_70 := by decide +kernel
theorem fz_FM_71 : (fz_S_71.filter (fun st => decide (fz_C_71.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_71.2.1 st.1 st.2 fz_C_71.2.2]) = fz_L_71 := by decide +kernel
theorem fz_FM_72 : (fz_S_72.filter (fun st => decide (fz_C_72.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_72.2.1 st.1 st.2 fz_C_72.2.2]) = fz_L_72 := by decide +kernel
theorem fz_FM_73 : (fz_S_73.filter (fun st => decide (fz_C_73.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_73.2.1 st.1 st.2 fz_C_73.2.2]) = fz_L_73 := by decide +kernel
theorem fz_FM_74 : (fz_S_74.filter (fun st => decide (fz_C_74.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_74.2.1 st.1 st.2 fz_C_74.2.2]) = fz_L_74 := by decide +kernel
theorem fz_FM_75 : (fz_S_75.filter (fun st => decide (fz_C_75.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_75.2.1 st.1 st.2 fz_C_75.2.2]) = fz_L_75 := by decide +kernel
theorem fz_FM_76 : (fz_S_76.filter (fun st => decide (fz_C_76.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_76.2.1 st.1 st.2 fz_C_76.2.2]) = fz_L_76 := by decide +kernel
theorem fz_FM_77 : (fz_S_77.filter (fun st => decide (fz_C_77.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_77.2.1 st.1 st.2 fz_C_77.2.2]) = fz_L_77 := by decide +kernel
theorem fz_FM_78 : (fz_S_78.filter (fun st => decide (fz_C_78.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_78.2.1 st.1 st.2 fz_C_78.2.2]) = fz_L_78 := by decide +kernel
theorem fz_FM_79 : (fz_S_79.filter (fun st => decide (fz_C_79.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_79.2.1 st.1 st.2 fz_C_79.2.2]) = fz_L_79 := by decide +kernel
theorem fz_FM_80 : (fz_S_80.filter (fun st => decide (fz_C_80.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_80.2.1 st.1 st.2 fz_C_80.2.2]) = fz_L_80 := by decide +kernel
theorem fz_FM_81 : (fz_S_81.filter (fun st => decide (fz_C_81.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_81.2.1 st.1 st.2 fz_C_81.2.2]) = fz_L_81 := by decide +kernel
theorem fz_FM_82 : (fz_S_82.filter (fun st => decide (fz_C_82.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_82.2.1 st.1 st.2 fz_C_82.2.2]) = fz_L_82 := by decide +kernel
theorem fz_FM_83 : (fz_S_83.filter (fun st => decide (fz_C_83.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_83.2.1 st.1 st.2 fz_C_83.2.2]) = fz_L_83 := by decide +kernel
theorem fz_FM_84 : (fz_S_84.filter (fun st => decide (fz_C_84.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_84.2.1 st.1 st.2 fz_C_84.2.2]) = fz_L_84 := by decide +kernel
theorem fz_FM_85 : (fz_S_85.filter (fun st => decide (fz_C_85.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_85.2.1 st.1 st.2 fz_C_85.2.2]) = fz_L_85 := by decide +kernel
theorem fz_FM_86 : (fz_S_86.filter (fun st => decide (fz_C_86.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_86.2.1 st.1 st.2 fz_C_86.2.2]) = fz_L_86 := by decide +kernel
theorem fz_FM_87 : (fz_S_87.filter (fun st => decide (fz_C_87.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_87.2.1 st.1 st.2 fz_C_87.2.2]) = fz_L_87 := by decide +kernel
theorem fz_FM_88 : (fz_S_88.filter (fun st => decide (fz_C_88.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_88.2.1 st.1 st.2 fz_C_88.2.2]) = fz_L_88 := by decide +kernel
theorem fz_FM_89 : (fz_S_89.filter (fun st => decide (fz_C_89.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_89.2.1 st.1 st.2 fz_C_89.2.2]) = fz_L_89 := by decide +kernel
theorem fz_FM_90 : (fz_S_90.filter (fun st => decide (fz_C_90.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_90.2.1 st.1 st.2 fz_C_90.2.2]) = fz_L_90 := by decide +kernel
theorem fz_FM_91 : (fz_S_91.filter (fun st => decide (fz_C_91.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_91.2.1 st.1 st.2 fz_C_91.2.2]) = fz_L_91 := by decide +kernel
theorem fz_FM_92 : (fz_S_92.filter (fun st => decide (fz_C_92.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_92.2.1 st.1 st.2 fz_C_92.2.2]) = fz_L_92 := by decide +kernel
theorem fz_FM_93 : (fz_S_93.filter (fun st => decide (fz_C_93.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_93.2.1 st.1 st.2 fz_C_93.2.2]) = fz_L_93 := by decide +kernel
theorem fz_FM_94 : (fz_S_94.filter (fun st => decide (fz_C_94.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_94.2.1 st.1 st.2 fz_C_94.2.2]) = fz_L_94 := by decide +kernel
theorem fz_FM_95 : (fz_S_95.filter (fun st => decide (fz_C_95.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_95.2.1 st.1 st.2 fz_C_95.2.2]) = fz_L_95 := by decide +kernel
theorem fz_FM_96 : (fz_S_96.filter (fun st => decide (fz_C_96.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_96.2.1 st.1 st.2 fz_C_96.2.2]) = fz_L_96 := by decide +kernel
theorem fz_FM_97 : (fz_S_97.filter (fun st => decide (fz_C_97.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_97.2.1 st.1 st.2 fz_C_97.2.2]) = fz_L_97 := by decide +kernel
theorem fz_FM_98 : (fz_S_98.filter (fun st => decide (fz_C_98.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_98.2.1 st.1 st.2 fz_C_98.2.2]) = fz_L_98 := by decide +kernel
theorem fz_FM_99 : (fz_S_99.filter (fun st => decide (fz_C_99.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_99.2.1 st.1 st.2 fz_C_99.2.2]) = fz_L_99 := by decide +kernel
theorem fz_FM_100 : (fz_S_100.filter (fun st => decide (fz_C_100.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_100.2.1 st.1 st.2 fz_C_100.2.2]) = fz_L_100 := by decide +kernel
theorem fz_FM_101 : (fz_S_101.filter (fun st => decide (fz_C_101.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_101.2.1 st.1 st.2 fz_C_101.2.2]) = fz_L_101 := by decide +kernel
theorem fz_FM_102 : (fz_S_102.filter (fun st => decide (fz_C_102.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_102.2.1 st.1 st.2 fz_C_102.2.2]) = fz_L_102 := by decide +kernel
theorem fz_FM_103 : (fz_S_103.filter (fun st => decide (fz_C_103.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_103.2.1 st.1 st.2 fz_C_103.2.2]) = fz_L_103 := by decide +kernel
theorem fz_FM_104 : (fz_S_104.filter (fun st => decide (fz_C_104.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_104.2.1 st.1 st.2 fz_C_104.2.2]) = fz_L_104 := by decide +kernel
theorem fz_FM_105 : (fz_S_105.filter (fun st => decide (fz_C_105.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_105.2.1 st.1 st.2 fz_C_105.2.2]) = fz_L_105 := by decide +kernel
theorem fz_FM_106 : (fz_S_106.filter (fun st => decide (fz_C_106.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_106.2.1 st.1 st.2 fz_C_106.2.2]) = fz_L_106 := by decide +kernel
theorem fz_FM_107 : (fz_S_107.filter (fun st => decide (fz_C_107.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_107.2.1 st.1 st.2 fz_C_107.2.2]) = fz_L_107 := by decide +kernel
theorem fz_FM_108 : (fz_S_108.filter (fun st => decide (fz_C_108.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_108.2.1 st.1 st.2 fz_C_108.2.2]) = fz_L_108 := by decide +kernel
theorem fz_FM_109 : (fz_S_109.filter (fun st => decide (fz_C_109.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_109.2.1 st.1 st.2 fz_C_109.2.2]) = fz_L_109 := by decide +kernel
theorem fz_FM_110 : (fz_S_110.filter (fun st => decide (fz_C_110.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_110.2.1 st.1 st.2 fz_C_110.2.2]) = fz_L_110 := by decide +kernel
theorem fz_FM_111 : (fz_S_111.filter (fun st => decide (fz_C_111.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_111.2.1 st.1 st.2 fz_C_111.2.2]) = fz_L_111 := by decide +kernel
theorem fz_FM_112 : (fz_S_112.filter (fun st => decide (fz_C_112.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_112.2.1 st.1 st.2 fz_C_112.2.2]) = fz_L_112 := by decide +kernel
theorem fz_FM_113 : (fz_S_113.filter (fun st => decide (fz_C_113.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_113.2.1 st.1 st.2 fz_C_113.2.2]) = fz_L_113 := by decide +kernel
theorem fz_FM_114 : (fz_S_114.filter (fun st => decide (fz_C_114.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_114.2.1 st.1 st.2 fz_C_114.2.2]) = fz_L_114 := by decide +kernel
theorem fz_FM_115 : (fz_S_115.filter (fun st => decide (fz_C_115.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_115.2.1 st.1 st.2 fz_C_115.2.2]) = fz_L_115 := by decide +kernel
theorem fz_FM_116 : (fz_S_116.filter (fun st => decide (fz_C_116.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_116.2.1 st.1 st.2 fz_C_116.2.2]) = fz_L_116 := by decide +kernel
theorem fz_FM_117 : (fz_S_117.filter (fun st => decide (fz_C_117.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_117.2.1 st.1 st.2 fz_C_117.2.2]) = fz_L_117 := by decide +kernel
theorem fz_FM_118 : (fz_S_118.filter (fun st => decide (fz_C_118.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_118.2.1 st.1 st.2 fz_C_118.2.2]) = fz_L_118 := by decide +kernel
theorem fz_FM_119 : (fz_S_119.filter (fun st => decide (fz_C_119.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_119.2.1 st.1 st.2 fz_C_119.2.2]) = fz_L_119 := by decide +kernel
theorem fz_FM_120 : (fz_S_120.filter (fun st => decide (fz_C_120.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_120.2.1 st.1 st.2 fz_C_120.2.2]) = fz_L_120 := by decide +kernel
theorem fz_FM_121 : (fz_S_121.filter (fun st => decide (fz_C_121.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_121.2.1 st.1 st.2 fz_C_121.2.2]) = fz_L_121 := by decide +kernel
theorem fz_FM_122 : (fz_S_122.filter (fun st => decide (fz_C_122.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_122.2.1 st.1 st.2 fz_C_122.2.2]) = fz_L_122 := by decide +kernel
theorem fz_FM_123 : (fz_S_123.filter (fun st => decide (fz_C_123.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_123.2.1 st.1 st.2 fz_C_123.2.2]) = fz_L_123 := by decide +kernel
theorem fz_FM_124 : (fz_S_124.filter (fun st => decide (fz_C_124.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_124.2.1 st.1 st.2 fz_C_124.2.2]) = fz_L_124 := by decide +kernel
theorem fz_FM_125 : (fz_S_125.filter (fun st => decide (fz_C_125.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_125.2.1 st.1 st.2 fz_C_125.2.2]) = fz_L_125 := by decide +kernel
theorem fz_FM_126 : (fz_S_126.filter (fun st => decide (fz_C_126.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_126.2.1 st.1 st.2 fz_C_126.2.2]) = fz_L_126 := by decide +kernel
theorem fz_FM_127 : (fz_S_127.filter (fun st => decide (fz_C_127.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_127.2.1 st.1 st.2 fz_C_127.2.2]) = fz_L_127 := by decide +kernel
theorem fz_FM_128 : (fz_S_128.filter (fun st => decide (fz_C_128.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_128.2.1 st.1 st.2 fz_C_128.2.2]) = fz_L_128 := by decide +kernel
