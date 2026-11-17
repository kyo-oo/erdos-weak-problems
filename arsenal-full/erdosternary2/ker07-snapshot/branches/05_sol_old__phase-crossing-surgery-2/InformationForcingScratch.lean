/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0315 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/InformationForcingScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-15 16:38:26 +0530  (c2444a3)
/-    Last-commit  : 2026-08-15 17:01:42 +0530  (c2740a7)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-15 16:38:26 +0530  c2444a3  (ker07-dev)
/-        Formalize localized information forcing step
/- [02/2] 2026-08-15 17:01:42 +0530  c2740a7  (ker07-dev)
/-        Repair exact forcing proof argument order
/- ====================================================================== -/

import InformationLocalizationScratch
import InformationFluxScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Output digit paired with the scratch carry recurrence. -/
def gstOutputDigitS (C d : Nat) : Nat :=
  (C + 4*d) % 3

/-- The low-end shared information word commutes exactly with one vertical
    ternary regeneration step.  `D` is the parent carry, `Z` the vertical
    information quotient, `A` the fixed horizontal multiplier, and `r` the
    current child digit.  No information is discarded: the regenerated parent
    carry and regenerated information quotient are exactly the quotient of the
    old shared word after the child digit has been injected. -/
theorem gst_shared_word_regenerates_exactS
    (A D Z r : Nat) :
    (D + 4*Z + 4*A*r) / 3 =
      gstStepCarryS D ((Z + A*r) % 3) +
        4 * ((Z + A*r) / 3) := by
  let E := Z + A*r
  have hE : E = E % 3 + 3*(E/3) := by
    have h := Nat.mod_add_div E 3
    omega
  have hshape :
      D + 4*Z + 4*A*r = D + 4*E := by
    dsimp [E]
    ring
  rw [hshape, hE]
  have hnum :
      D + 4 * (E % 3 + 3 * (E / 3)) =
        (D + 4*(E%3)) + 3*(4*(E/3)) := by
    ring
  rw [hnum]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  rfl

/-- The parent bad language regenerates in the same relative affine form.
    Only the finite offset and incoming seed change; the multiplier `A` is
    untouched. -/
theorem gst_relative_parent_bad_regeneratesS
    (A D Z Y : Nat)
    (hbad : GSTSeededBadTraceS D (Z + A*Y)) :
    let r := Y % 3
    let e := (Z + A*r) % 3
    let D' := gstStepCarryS D e
    let Z' := (Z + A*r) / 3
    GSTSeededBadTraceS D' (Z' + A*(Y/3)) := by
  dsimp only
  have hsuffix :=
    gst_seeded_bad_trace_regenerates_tailS D (Z + A*Y) hbad
  have htail := gst_relative_affine_tail_divS A Z Y
  have hemit := gst_relative_affine_emitted_digitS A Z Y
  have hseed :
      gstAffineMulCarryS 4 D (Z + A*Y) 1 =
        gstStepCarryS D ((Z + A*(Y%3)) % 3) := by
    rw [gst_parent_seed_after_regenerationS]
    rw [hemit]
  rw [hseed, htail] at hsuffix
  exact hsuffix

/-- A localized child Happy Gate cannot simply disappear when the parent is
    assumed completely bad.  After consuming the gate row, the parent bad
    suffix is regenerated exactly, the child information survives as seed 2
    (NULL realization) or seed 3 (GST+ realization), and the low shared word
    obeys the exact commuting conservation equation. -/
theorem gst_localized_gate_forcing_stepS
    (A D Z C Y : Nat)
    (hgate : Y % 3 = 2 ∧ (C = 0 ∨ C = 3))
    (hbad : GSTSeededBadTraceS D (Z + A*Y)) :
    let e := (Z + A*2) % 3
    let D' := gstStepCarryS D e
    let Z' := (Z + A*2) / 3
    let C' := gstStepCarryS C 2
    GSTSeededBadTraceS D' (Z' + A*(Y/3)) ∧
      (C' = 2 ∨ C' = 3) ∧
      (D + 4*Z + 8*A) / 3 = D' + 4*Z' := by
  dsimp only
  have hparent := gst_relative_parent_bad_regeneratesS A D Z Y hbad
  dsimp only at hparent
  rw [hgate.1] at hparent
  have hlatent : gstStepCarryS C 2 = 2 ∨ gstStepCarryS C 2 = 3 := by
    rcases hgate.2 with h0 | h3
    · left
      rw [h0]
      decide
    · right
      rw [h3]
      decide
  have hshared := gst_shared_word_regenerates_exactS A D Z 2
  refine ⟨hparent, hlatent, ?_⟩
  convert hshared using 1 <;> ring
