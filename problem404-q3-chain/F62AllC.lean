import F62AllB

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem fz_all_65 : List.all (dpRun fz_TAIL_65 fz_S_65) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_65, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_66⟩

theorem fz_all_64 : List.all (dpRun fz_TAIL_64 fz_S_64) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_64, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_65⟩

theorem fz_all_63 : List.all (dpRun fz_TAIL_63 fz_S_63) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_63, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_64⟩

theorem fz_all_62 : List.all (dpRun fz_TAIL_62 fz_S_62) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_62, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_63⟩

theorem fz_all_61 : List.all (dpRun fz_TAIL_61 fz_S_61) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_61, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_62⟩

theorem fz_all_60 : List.all (dpRun fz_TAIL_60 fz_S_60) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_60, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_61⟩

theorem fz_all_59 : List.all (dpRun fz_TAIL_59 fz_S_59) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_59, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_60⟩

theorem fz_all_58 : List.all (dpRun fz_TAIL_58 fz_S_58) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_58, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_59⟩

theorem fz_all_57 : List.all (dpRun fz_TAIL_57 fz_S_57) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_57, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_58⟩

theorem fz_all_56 : List.all (dpRun fz_TAIL_56 fz_S_56) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_56, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_57⟩

theorem fz_all_55 : List.all (dpRun fz_TAIL_55 fz_S_55) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_55, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_56⟩

theorem fz_all_54 : List.all (dpRun fz_TAIL_54 fz_S_54) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_54, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_55⟩

theorem fz_all_53 : List.all (dpRun fz_TAIL_53 fz_S_53) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_53, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_54⟩

theorem fz_all_52 : List.all (dpRun fz_TAIL_52 fz_S_52) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_52, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_53⟩

theorem fz_all_51 : List.all (dpRun fz_TAIL_51 fz_S_51) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_51, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_52⟩

theorem fz_all_50 : List.all (dpRun fz_TAIL_50 fz_S_50) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_50, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_51⟩

theorem fz_all_49 : List.all (dpRun fz_TAIL_49 fz_S_49) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_49, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_50⟩

theorem fz_all_48 : List.all (dpRun fz_TAIL_48 fz_S_48) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_48, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_49⟩

theorem fz_all_47 : List.all (dpRun fz_TAIL_47 fz_S_47) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_47, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_48⟩

theorem fz_all_46 : List.all (dpRun fz_TAIL_46 fz_S_46) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_46, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_47⟩

theorem fz_all_45 : List.all (dpRun fz_TAIL_45 fz_S_45) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_45, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_46⟩

theorem fz_all_44 : List.all (dpRun fz_TAIL_44 fz_S_44) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_44, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_45⟩

theorem fz_all_43 : List.all (dpRun fz_TAIL_43 fz_S_43) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_43, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_44⟩

theorem fz_all_42 : List.all (dpRun fz_TAIL_42 fz_S_42) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_42, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_43⟩

theorem fz_all_41 : List.all (dpRun fz_TAIL_41 fz_S_41) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_41, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_42⟩

theorem fz_all_40 : List.all (dpRun fz_TAIL_40 fz_S_40) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_40, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_41⟩

theorem fz_all_39 : List.all (dpRun fz_TAIL_39 fz_S_39) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_39, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_40⟩

theorem fz_all_38 : List.all (dpRun fz_TAIL_38 fz_S_38) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_38, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_39⟩

theorem fz_all_37 : List.all (dpRun fz_TAIL_37 fz_S_37) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_37, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_38⟩

theorem fz_all_36 : List.all (dpRun fz_TAIL_36 fz_S_36) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_36, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_37⟩

theorem fz_all_35 : List.all (dpRun fz_TAIL_35 fz_S_35) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_35, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_36⟩

theorem fz_all_34 : List.all (dpRun fz_TAIL_34 fz_S_34) (fun S => decide (maxT S ≤ 129)) = true := by
  rw [fz_run_34, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_35⟩

