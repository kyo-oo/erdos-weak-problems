import GSTHandwrittenHorizontalParentBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- Exact live prefix-one package. A child Navigation witness is converted to
its literal digit/carry gate and then to the physical binary first-BIG1
boundary. Simultaneously an assumed parent failure is retained as the exact
seed-one affine bad trace on c(s)/3 + 4^(3^s)*T. -/
theorem gpt56_prefix_one_live_handwritten_package
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      1 ≤ N ∧
      GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      GSTSeededAffineBadTrace 1 X := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, hd2, hspace⟩ := hchild
  have hCmod : gstCarry T q % 3 = 0 := by
    dsimp [T]
    exact gstGoodSpace_carry_mod3_zero _ q hspace
  have hClt : gstCarry T q < 4 := by
    cases q with
    | zero =>
        simp only [gstCarry, Nat.pow_zero, Nat.mod_one, Nat.mul_zero,
          Nat.zero_div]
        decide
    | succ r =>
        exact gstCarry_lt_four T (r+1) (by omega)
  have hC : gstCarry T q = 0 ∨ gstCarry T q = 3 := by omega
  obtain ⟨N, hN, hfirst⟩ :=
    gpt56_child_digit_two_forces_first_big1 T q hd2
  have hseeded : GSTSeededAffineBadTrace 1 X := by
    have h := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
    have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
      rw [Nat.pow_one, c_mod3 s hs]
    rw [hseed] at h
    simpa [T, A, X] using h
  exact ⟨q, N, hd2, hC, hN, hfirst, hseeded⟩

/-- Same live package, exposing the exact handwritten first-BIG1 DESTROY
boundary immediately before the physical information value one. -/
theorem gpt56_prefix_one_live_destroy_boundary
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      GSTSeededAffineBadTrace 1 X ∧
      1 ≤ N ∧
      GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      let j := N - 1
      GSTPhysicalKernel.binaryColumnCarry T q j = 0 ∧
      GSTPhysicalKernel.binaryColumnDigit T q j = 2 ∧
      gstBinaryBridgeMassS
        (GSTPhysicalKernel.binaryColumnCarry T q j)
        (GSTPhysicalKernel.binaryColumnDigit T q j) = 4 ∧
      gstBinaryBridgeEventS
        (GSTPhysicalKernel.binaryColumnCarry T q j)
        (GSTPhysicalKernel.binaryColumnDigit T q j) = 5 := by
  dsimp only
  obtain ⟨q, _, hd2, hC, _, _, hseeded⟩ :=
    gpt56_prefix_one_live_handwritten_package s n hs hn hchild hBad
  obtain ⟨N, hN, hfirst, hboundary⟩ :=
    gpt56_child_digit_two_forces_destroy_boundary
      (gstNavigationConstant (s+1) n) q hd2
  exact ⟨q, N, hd2, hC, hseeded, hN, hfirst, hboundary⟩

#check gpt56_prefix_one_live_handwritten_package
#check gpt56_prefix_one_live_destroy_boundary
#print axioms gpt56_prefix_one_live_handwritten_package
#print axioms gpt56_prefix_one_live_destroy_boundary
