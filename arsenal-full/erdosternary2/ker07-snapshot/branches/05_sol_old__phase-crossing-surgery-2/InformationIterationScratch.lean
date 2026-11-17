/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0330 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/InformationIterationScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-15 17:06:28 +0530  (3166a7b)
/-    Last-commit  : 2026-08-15 17:06:28 +0530  (3166a7b)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 17:06:28 +0530  3166a7b  (ker07-dev)
/-        Formalize iterable two-endpoint information state
/- ====================================================================== -/

import InformationForcingScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The high endpoint of the shared information word obeys the same exact
    ternary regeneration law.  `r` is the child input digit, `u` its realised
    output digit under carry `C`, and `C'` the regenerated child carry. -/
theorem gst_shared_high_regenerates_exactS
    (A W C r : Nat) :
    (W + A*C + 4*A*r) / 3 =
      (W + A*gstOutputDigitS C r) / 3 +
        A * gstStepCarryS C r := by
  let U := C + 4*r
  have hU : U = U % 3 + 3*(U/3) := by
    have h := Nat.mod_add_div U 3
    omega
  have hshape0 : W + A*C + 4*A*r = W + A*U := by
    dsimp [U]
    ring
  rw [hshape0, hU]
  have hshape1 :
      W + A*(U % 3 + 3*(U/3)) =
        (W + A*(U%3)) + 3*(A*(U/3)) := by
    ring
  rw [hshape1]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  simp [gstOutputDigitS, gstStepCarryS, U]

/-- The regenerated high remainder remains strictly below the horizontal
    multiplier.  Thus the child carry continues to be the top base-4
    coordinate of the same finite information word after every row. -/
theorem gst_shared_high_remainder_ltS
    (A W C r : Nat) (hA : 0 < A) (hW : W < A) :
    (W + A*gstOutputDigitS C r) / 3 < A := by
  have hu : gstOutputDigitS C r < 3 := by
    unfold gstOutputDigitS
    exact Nat.mod_lt _ (by decide)
  have hu1 : gstOutputDigitS C r + 1 ≤ 3 := Nat.succ_le_of_lt hu
  have hnum : W + A*gstOutputDigitS C r < 3*A := by
    calc
      W + A*gstOutputDigitS C r <
          A + A*gstOutputDigitS C r := Nat.add_lt_add_right hW _
      _ = A * (gstOutputDigitS C r + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        ac_rfl
      _ ≤ A*3 := Nat.mul_le_mul_left A hu1
      _ = 3*A := by ac_rfl
  exact Nat.div_lt_of_lt_mul hnum

/-- One vertical row preserves both endpoint decompositions of the same shared
    information word.  The low endpoint is the parent seeded carry; the high
    endpoint is the child carry.  CREATE/DESTROY/SURVIVE are therefore
    different realisations of one conserved state rather than different
    information objects. -/
theorem gst_shared_two_endpoint_regeneratesS
    (A D Z W C r : Nat)
    (hEq : D + 4*Z = W + A*C) :
    let e := (Z + A*r) % 3
    let D' := gstStepCarryS D e
    let Z' := (Z + A*r) / 3
    let u := gstOutputDigitS C r
    let C' := gstStepCarryS C r
    let W' := (W + A*u) / 3
    D' + 4*Z' = W' + A*C' := by
  dsimp only
  have hlow := gst_shared_word_regenerates_exactS A D Z r
  have hhigh := gst_shared_high_regenerates_exactS A W C r
  calc
    gstStepCarryS D ((Z + A*r) % 3) + 4*((Z + A*r)/3) =
        (D + 4*Z + 4*A*r) / 3 := hlow.symm
    _ = (W + A*C + 4*A*r) / 3 := by rw [hEq]
    _ = (W + A*gstOutputDigitS C r) / 3 +
          A*gstStepCarryS C r := hhigh

/-- The complete iterative package.  A seed-retaining parent bad trace and the
    two endpoint decompositions regenerate together after consuming one child
    ternary digit.  No NULL absorption or finite wave cutoff is used. -/
theorem gst_coupled_bad_information_regeneratesS
    (A D Z W C Y : Nat)
    (hA : 0 < A) (hW : W < A)
    (hEq : D + 4*Z = W + A*C)
    (hbad : GSTSeededBadTraceS D (Z + A*Y)) :
    let r := Y % 3
    let e := (Z + A*r) % 3
    let D' := gstStepCarryS D e
    let Z' := (Z + A*r) / 3
    let u := gstOutputDigitS C r
    let C' := gstStepCarryS C r
    let W' := (W + A*u) / 3
    GSTSeededBadTraceS D' (Z' + A*(Y/3)) ∧
      D' + 4*Z' = W' + A*C' ∧
      W' < A := by
  dsimp only
  have hbad' := gst_relative_parent_bad_regeneratesS A D Z Y hbad
  dsimp only at hbad'
  have hEq' := gst_shared_two_endpoint_regeneratesS A D Z W C (Y%3) hEq
  dsimp only at hEq'
  have hW' := gst_shared_high_remainder_ltS A W C (Y%3) hA hW
  exact ⟨hbad', hEq', hW'⟩

/-- At a child Happy Gate the high endpoint realises digit two on both sides:
    NULL (carry 0) regenerates to latent carry 2 and GST+ (carry 3) remains
    carry 3, while in either case the high remainder is driven by the same
    realised digit two. -/
theorem gst_child_gate_high_realisationS
    (C : Nat) (hC : C = 0 ∨ C = 3) :
    gstOutputDigitS C 2 = 2 ∧
      (gstStepCarryS C 2 = 2 ∨ gstStepCarryS C 2 = 3) := by
  rcases hC with h0 | h3
  · subst C
    decide
  · subst C
    decide
