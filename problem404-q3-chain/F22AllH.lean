import F22AllG

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem fz_all_29 : List.all (dpRun fz_TAIL_29 fz_S_29) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_29, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_30⟩

theorem fz_all_28 : List.all (dpRun fz_TAIL_28 fz_S_28) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_28, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_29⟩

theorem fz_all_27 : List.all (dpRun fz_TAIL_27 fz_S_27) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_27, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_28⟩

theorem fz_all_26 : List.all (dpRun fz_TAIL_26 fz_S_26) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_26, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_27⟩

theorem fz_all_25 : List.all (dpRun fz_TAIL_25 fz_S_25) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_25, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_26⟩

theorem fz_all_24 : List.all (dpRun fz_TAIL_24 fz_S_24) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_24, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_25⟩

theorem fz_all_23 : List.all (dpRun fz_TAIL_23 fz_S_23) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_23, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_24⟩

theorem fz_all_22 : List.all (dpRun fz_TAIL_22 fz_S_22) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_22, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_23⟩

theorem fz_all_21 : List.all (dpRun fz_TAIL_21 fz_S_21) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_21, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_22⟩

theorem fz_all_20 : List.all (dpRun fz_TAIL_20 fz_S_20) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_20, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_21⟩

theorem fz_all_19 : List.all (dpRun fz_TAIL_19 fz_S_19) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_19, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_20⟩

theorem fz_all_18 : List.all (dpRun fz_TAIL_18 fz_S_18) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_18, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_19⟩

theorem fz_all_17 : List.all (dpRun fz_TAIL_17 fz_S_17) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_17, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_18⟩

theorem fz_all_16 : List.all (dpRun fz_TAIL_16 fz_S_16) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_16, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_17⟩

theorem fz_all_15 : List.all (dpRun fz_TAIL_15 fz_S_15) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_15, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_16⟩

theorem fz_all_14 : List.all (dpRun fz_TAIL_14 fz_S_14) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_14, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_15⟩

theorem fz_all_13 : List.all (dpRun fz_TAIL_13 fz_S_13) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_13, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_14⟩

theorem fz_all_12 : List.all (dpRun fz_TAIL_12 fz_S_12) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_12, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_13⟩

theorem fz_all_11 : List.all (dpRun fz_TAIL_11 fz_S_11) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_11, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_12⟩

theorem fz_all_10 : List.all (dpRun fz_TAIL_10 fz_S_10) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_10, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_11⟩

theorem fz_all_9 : List.all (dpRun fz_TAIL_9 fz_S_9) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_9, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_10⟩

theorem fz_all_8 : List.all (dpRun fz_TAIL_8 fz_S_8) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_8, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_9⟩

theorem fz_all_7 : List.all (dpRun fz_TAIL_7 fz_S_7) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_7, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_8⟩

theorem fz_all_6 : List.all (dpRun fz_TAIL_6 fz_S_6) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_6, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_7⟩

theorem fz_all_5 : List.all (dpRun fz_TAIL_5 fz_S_5) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_5, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_6⟩

theorem fz_all_4 : List.all (dpRun fz_TAIL_4 fz_S_4) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_4, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_5⟩

theorem fz_all_3 : List.all (dpRun fz_TAIL_3 fz_S_3) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_3, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_4⟩

theorem fz_all_2 : List.all (dpRun fz_TAIL_2 fz_S_2) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_2, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_3⟩

theorem fz_all_1 : List.all (dpRun fz_TAIL_1 fz_S_1) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_1, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_2⟩

