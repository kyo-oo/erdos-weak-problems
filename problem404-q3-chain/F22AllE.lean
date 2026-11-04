import F22AllD

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem fz_all_125 : List.all (dpRun fz_TAIL_125 fz_S_125) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_125, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_126⟩

theorem fz_all_124 : List.all (dpRun fz_TAIL_124 fz_S_124) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_124, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_125⟩

theorem fz_all_123 : List.all (dpRun fz_TAIL_123 fz_S_123) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_123, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_124⟩

theorem fz_all_122 : List.all (dpRun fz_TAIL_122 fz_S_122) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_122, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_123⟩

theorem fz_all_121 : List.all (dpRun fz_TAIL_121 fz_S_121) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_121, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_122⟩

theorem fz_all_120 : List.all (dpRun fz_TAIL_120 fz_S_120) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_120, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_121⟩

theorem fz_all_119 : List.all (dpRun fz_TAIL_119 fz_S_119) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_119, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_120⟩

theorem fz_all_118 : List.all (dpRun fz_TAIL_118 fz_S_118) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_118, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_119⟩

theorem fz_all_117 : List.all (dpRun fz_TAIL_117 fz_S_117) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_117, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_118⟩

theorem fz_all_116 : List.all (dpRun fz_TAIL_116 fz_S_116) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_116, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_117⟩

theorem fz_all_115 : List.all (dpRun fz_TAIL_115 fz_S_115) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_115, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_116⟩

theorem fz_all_114 : List.all (dpRun fz_TAIL_114 fz_S_114) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_114, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_115⟩

theorem fz_all_113 : List.all (dpRun fz_TAIL_113 fz_S_113) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_113, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_114⟩

theorem fz_all_112 : List.all (dpRun fz_TAIL_112 fz_S_112) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_112, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_113⟩

theorem fz_all_111 : List.all (dpRun fz_TAIL_111 fz_S_111) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_111, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_112⟩

theorem fz_all_110 : List.all (dpRun fz_TAIL_110 fz_S_110) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_110, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_111⟩

theorem fz_all_109 : List.all (dpRun fz_TAIL_109 fz_S_109) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_109, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_110⟩

theorem fz_all_108 : List.all (dpRun fz_TAIL_108 fz_S_108) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_108, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_109⟩

theorem fz_all_107 : List.all (dpRun fz_TAIL_107 fz_S_107) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_107, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_108⟩

theorem fz_all_106 : List.all (dpRun fz_TAIL_106 fz_S_106) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_106, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_107⟩

theorem fz_all_105 : List.all (dpRun fz_TAIL_105 fz_S_105) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_105, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_106⟩

theorem fz_all_104 : List.all (dpRun fz_TAIL_104 fz_S_104) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_104, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_105⟩

theorem fz_all_103 : List.all (dpRun fz_TAIL_103 fz_S_103) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_103, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_104⟩

theorem fz_all_102 : List.all (dpRun fz_TAIL_102 fz_S_102) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_102, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_103⟩

theorem fz_all_101 : List.all (dpRun fz_TAIL_101 fz_S_101) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_101, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_102⟩

theorem fz_all_100 : List.all (dpRun fz_TAIL_100 fz_S_100) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_100, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_101⟩

theorem fz_all_99 : List.all (dpRun fz_TAIL_99 fz_S_99) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_99, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_100⟩

theorem fz_all_98 : List.all (dpRun fz_TAIL_98 fz_S_98) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_98, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_99⟩

theorem fz_all_97 : List.all (dpRun fz_TAIL_97 fz_S_97) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_97, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_98⟩

theorem fz_all_96 : List.all (dpRun fz_TAIL_96 fz_S_96) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_96, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_97⟩

theorem fz_all_95 : List.all (dpRun fz_TAIL_95 fz_S_95) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_95, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_96⟩

theorem fz_all_94 : List.all (dpRun fz_TAIL_94 fz_S_94) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_94, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_95⟩

