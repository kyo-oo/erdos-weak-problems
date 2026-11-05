import ExactF22

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144

/-- dedupAux is chunk-associative. -/
theorem fz_dedupAux_cons (y : Nat × Nat) (ys : List (Nat × Nat)) (acc : List (Nat × Nat)) :
    dedupAux (y :: ys) acc = if memB y acc then dedupAux ys acc else dedupAux ys (y :: acc) := by
  simp only [dedupAux]

theorem fz_ddA : ∀ (l₁ l₂ : List (Nat × Nat)) (acc : List (Nat × Nat)),
    dedupAux (l₁ ++ l₂) acc = dedupAux l₂ (dedupAux l₁ acc) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ acc; rfl
  | cons y ys ih =>
      intro l₂ acc
      rw [List.cons_append, fz_dedupAux_cons, fz_dedupAux_cons]
      by_cases h : memB y acc = true
      · rw [if_pos h, if_pos h, ih]
      · rw [if_neg h, if_neg h, ih]

/-- stepCoin in the frozen form. -/
theorem fz_stepCoin_eq (c : Nat × Nat × Nat) (S : List (Nat × Nat)) :
    stepCoin c S = dedupAux ((S.filter (fun st => decide (c.2.1 ≤ st.1))).flatMap
      (fun st => [st, step1 c.2.1 st.1 st.2 c.2.2])) [] := by rfl

/-- dpRun in the frozen form. -/
theorem fz_dpRun_cons (c : Nat × Nat × Nat) (cs : List (Nat × Nat × Nat)) (S : List (Nat × Nat)) :
    dpRun (c :: cs) S = stepCoin c S :: dpRun cs (stepCoin c S) := by rfl
