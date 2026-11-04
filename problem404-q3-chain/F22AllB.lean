import F22AllA

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem fz_all_221 : List.all (dpRun fz_TAIL_221 fz_S_221) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_221, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_222⟩

theorem fz_all_220 : List.all (dpRun fz_TAIL_220 fz_S_220) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_220, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_221⟩

theorem fz_all_219 : List.all (dpRun fz_TAIL_219 fz_S_219) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_219, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_220⟩

theorem fz_all_218 : List.all (dpRun fz_TAIL_218 fz_S_218) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_218, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_219⟩

theorem fz_all_217 : List.all (dpRun fz_TAIL_217 fz_S_217) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_217, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_218⟩

theorem fz_all_216 : List.all (dpRun fz_TAIL_216 fz_S_216) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_216, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_217⟩

theorem fz_all_215 : List.all (dpRun fz_TAIL_215 fz_S_215) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_215, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_216⟩

theorem fz_all_214 : List.all (dpRun fz_TAIL_214 fz_S_214) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_214, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_215⟩

theorem fz_all_213 : List.all (dpRun fz_TAIL_213 fz_S_213) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_213, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_214⟩

theorem fz_all_212 : List.all (dpRun fz_TAIL_212 fz_S_212) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_212, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_213⟩

theorem fz_all_211 : List.all (dpRun fz_TAIL_211 fz_S_211) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_211, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_212⟩

theorem fz_all_210 : List.all (dpRun fz_TAIL_210 fz_S_210) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_210, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_211⟩

theorem fz_all_209 : List.all (dpRun fz_TAIL_209 fz_S_209) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_209, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_210⟩

theorem fz_all_208 : List.all (dpRun fz_TAIL_208 fz_S_208) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_208, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_209⟩

theorem fz_all_207 : List.all (dpRun fz_TAIL_207 fz_S_207) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_207, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_208⟩

theorem fz_all_206 : List.all (dpRun fz_TAIL_206 fz_S_206) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_206, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_207⟩

theorem fz_all_205 : List.all (dpRun fz_TAIL_205 fz_S_205) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_205, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_206⟩

theorem fz_all_204 : List.all (dpRun fz_TAIL_204 fz_S_204) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_204, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_205⟩

theorem fz_all_203 : List.all (dpRun fz_TAIL_203 fz_S_203) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_203, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_204⟩

theorem fz_all_202 : List.all (dpRun fz_TAIL_202 fz_S_202) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_202, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_203⟩

theorem fz_all_201 : List.all (dpRun fz_TAIL_201 fz_S_201) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_201, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_202⟩

theorem fz_all_200 : List.all (dpRun fz_TAIL_200 fz_S_200) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_200, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_201⟩

theorem fz_all_199 : List.all (dpRun fz_TAIL_199 fz_S_199) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_199, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_200⟩

theorem fz_all_198 : List.all (dpRun fz_TAIL_198 fz_S_198) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_198, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_199⟩

theorem fz_all_197 : List.all (dpRun fz_TAIL_197 fz_S_197) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_197, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_198⟩

theorem fz_all_196 : List.all (dpRun fz_TAIL_196 fz_S_196) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_196, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_197⟩

theorem fz_all_195 : List.all (dpRun fz_TAIL_195 fz_S_195) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_195, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_196⟩

theorem fz_all_194 : List.all (dpRun fz_TAIL_194 fz_S_194) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_194, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_195⟩

theorem fz_all_193 : List.all (dpRun fz_TAIL_193 fz_S_193) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_193, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_194⟩

theorem fz_all_192 : List.all (dpRun fz_TAIL_192 fz_S_192) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_192, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_193⟩

theorem fz_all_191 : List.all (dpRun fz_TAIL_191 fz_S_191) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_191, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_192⟩

theorem fz_all_190 : List.all (dpRun fz_TAIL_190 fz_S_190) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_190, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_191⟩

