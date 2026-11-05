import F22AllH

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

theorem fz_all_0 : List.all (dpRun fz_TAIL_0 fz_S_0) (fun S => decide (maxT S ≤ 253)) = true := by
  rw [fz_run_0, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_1⟩

/-- **THE HYPOTHESIS KILL: obstructionCheck = true, UNCONDITIONALLY.** -/
theorem obstructionCheck_true : obstructionCheck = true := by
  unfold obstructionCheck allSets
  rw [table_eq, List.all_cons, Bool.and_eq_true]
  exact ⟨by decide +kernel, fz_all_0⟩

/-- **f(2,2) = 254 — UNCONDITIONAL, ZERO HYPOTHESES.** -/
theorem erdos404_f22_final :
    v2 (2 + (witnessB.map fact).sum) = 254
    ∧ ∀ B : List Nat, NoDupL B → (∀ i ∈ B, 3 ≤ i) →
      v2 (2 + (B.map fact).sum) ≤ 254 :=
  erdos404_f22_exact obstructionCheck_true

#print axioms obstructionCheck_true
#print axioms erdos404_f22_final
