import F22Asm0
import F22Asm1

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

/-- The all-chain: every set of the run satisfies the maxT bound. -/
theorem fz_all_253 : List.all (dpRun fz_TAIL_253 fz_S_253) (fun S => decide (maxT S ≤ 253)) = true := by rfl

theorem fz_all_252 : List.all (dpRun fz_TAIL_252 fz_S_252) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_252, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_253⟩

theorem fz_all_251 : List.all (dpRun fz_TAIL_251 fz_S_251) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_251, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_252⟩

theorem fz_all_250 : List.all (dpRun fz_TAIL_250 fz_S_250) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_250, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_251⟩

theorem fz_all_249 : List.all (dpRun fz_TAIL_249 fz_S_249) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_249, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_250⟩

theorem fz_all_248 : List.all (dpRun fz_TAIL_248 fz_S_248) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_248, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_249⟩

theorem fz_all_247 : List.all (dpRun fz_TAIL_247 fz_S_247) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_247, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_248⟩

theorem fz_all_246 : List.all (dpRun fz_TAIL_246 fz_S_246) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_246, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_247⟩

theorem fz_all_245 : List.all (dpRun fz_TAIL_245 fz_S_245) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_245, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_246⟩

theorem fz_all_244 : List.all (dpRun fz_TAIL_244 fz_S_244) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_244, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_245⟩

theorem fz_all_243 : List.all (dpRun fz_TAIL_243 fz_S_243) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_243, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_244⟩

theorem fz_all_242 : List.all (dpRun fz_TAIL_242 fz_S_242) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_242, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_243⟩

theorem fz_all_241 : List.all (dpRun fz_TAIL_241 fz_S_241) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_241, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_242⟩

theorem fz_all_240 : List.all (dpRun fz_TAIL_240 fz_S_240) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_240, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_241⟩

theorem fz_all_239 : List.all (dpRun fz_TAIL_239 fz_S_239) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_239, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_240⟩

theorem fz_all_238 : List.all (dpRun fz_TAIL_238 fz_S_238) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_238, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_239⟩

theorem fz_all_237 : List.all (dpRun fz_TAIL_237 fz_S_237) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_237, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_238⟩

theorem fz_all_236 : List.all (dpRun fz_TAIL_236 fz_S_236) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_236, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_237⟩

theorem fz_all_235 : List.all (dpRun fz_TAIL_235 fz_S_235) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_235, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_236⟩

theorem fz_all_234 : List.all (dpRun fz_TAIL_234 fz_S_234) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_234, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_235⟩

theorem fz_all_233 : List.all (dpRun fz_TAIL_233 fz_S_233) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_233, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_234⟩

theorem fz_all_232 : List.all (dpRun fz_TAIL_232 fz_S_232) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_232, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_233⟩

theorem fz_all_231 : List.all (dpRun fz_TAIL_231 fz_S_231) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_231, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_232⟩

theorem fz_all_230 : List.all (dpRun fz_TAIL_230 fz_S_230) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_230, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_231⟩

theorem fz_all_229 : List.all (dpRun fz_TAIL_229 fz_S_229) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_229, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_230⟩

theorem fz_all_228 : List.all (dpRun fz_TAIL_228 fz_S_228) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_228, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_229⟩

theorem fz_all_227 : List.all (dpRun fz_TAIL_227 fz_S_227) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_227, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_228⟩

theorem fz_all_226 : List.all (dpRun fz_TAIL_226 fz_S_226) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_226, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_227⟩

theorem fz_all_225 : List.all (dpRun fz_TAIL_225 fz_S_225) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_225, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_226⟩

theorem fz_all_224 : List.all (dpRun fz_TAIL_224 fz_S_224) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_224, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_225⟩

theorem fz_all_223 : List.all (dpRun fz_TAIL_223 fz_S_223) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_223, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_224⟩

theorem fz_all_222 : List.all (dpRun fz_TAIL_222 fz_S_222) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_222, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_223⟩

