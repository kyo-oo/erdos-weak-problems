/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0285 / 1132
/-    Path         : branches/sol_phase-crossing-surgery-2/InformationLocalizationScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery-2
/-    First-commit : 2026-08-15 15:26:29 +0530  (607a4b5)
/-    Last-commit  : 2026-08-15 16:52:47 +0530  (b8cbd8f)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-15 15:26:29 +0530  607a4b5  (ker07-dev)
/-        Localize shared-information gates without losing seeds
/- [02/4] 2026-08-15 15:40:28 +0530  8bbed38  (ker07-dev)
/-        Preserve accumulated seed explicitly at localized row zero
/- [03/4] 2026-08-15 16:46:13 +0530  1ce88bb  (ker07-dev)
/-        Close localized gate position-zero simplification
/- [04/4] 2026-08-15 16:52:47 +0530  b8cbd8f  (ker07-dev)
/-        Close localized seed modulo-one identity
/- ====================================================================== -/

import InformationRegenerationScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- A complete seeded bad trace can be cut at any ternary position without
    losing its incoming carry. -/
theorem gst_seeded_bad_trace_suffixS
    (D X q : Nat) (hbad : GSTSeededBadTraceS D X) :
    GSTSeededBadTraceS
      (gstAffineMulCarryS 4 D X q) (X / 3^q) := by
  intro j
  have h := hbad (q+j)
  rw [gst_seeded_affine_carry_semigroupS D X q j,
      gst_seeded_affine_digit_shiftS X q j] at h
  exact h

/-- A seeded child Happy Gate at position q becomes a position-zero Happy Gate
    after cutting at q; the accumulated child carry is retained as the seed. -/
theorem gst_seeded_gate_localizesS
    (C Y q : Nat)
    (hgate : gstDigitS Y q = 2 ∧
      (gstAffineMulCarryS 4 C Y q = 0 ∨
       gstAffineMulCarryS 4 C Y q = 3)) :
    gstDigitS (Y / 3^q) 0 = 2 ∧
      (gstAffineMulCarryS 4 (gstAffineMulCarryS 4 C Y q)
          (Y / 3^q) 0 = 0 ∨
       gstAffineMulCarryS 4 (gstAffineMulCarryS 4 C Y q)
          (Y / 3^q) 0 = 3) := by
  have hseed0 :
      gstAffineMulCarryS 4 (gstAffineMulCarryS 4 C Y q)
          (Y / 3^q) 0 = gstAffineMulCarryS 4 C Y q := by
    simp [gstAffineMulCarryS, Nat.mod_one]
  constructor
  · rw [← gst_seeded_affine_digit_shiftS Y q 0]
    simpa [Nat.mod_one] using hgate.1
  · rcases hgate.2 with h0 | h3
    · left
      rw [hseed0, h0]
    · right
      rw [hseed0, h3]

/-- Cutting a relative affine realization keeps the same relative multiplier A;
    all processed information is absorbed into the regenerated finite offset. -/
theorem gst_relative_affine_suffixS
    (A Z Y q : Nat) :
    (Z + A*Y) / 3^q =
      gstAffineMulCarryS A Z Y q + A*(Y / 3^q) := by
  exact gst_affine_tail_div_decompositionS Z A Y q

/-- Full localization package at an arbitrary child gate.  The parent bad
    language, child gate, and shared relative affine form all survive the cut. -/
theorem gst_shared_gate_localizationS
    (A Z Y D C q : Nat)
    (hgate : gstDigitS Y q = 2 ∧
      (gstAffineMulCarryS 4 C Y q = 0 ∨
       gstAffineMulCarryS 4 C Y q = 3))
    (hbad : GSTSeededBadTraceS D (Z + A*Y)) :
    let Yq := Y / 3^q
    let Zq := gstAffineMulCarryS A Z Y q
    let Dq := gstAffineMulCarryS 4 D (Z + A*Y) q
    let Cq := gstAffineMulCarryS 4 C Y q
    GSTSeededBadTraceS Dq (Zq + A*Yq) ∧
      (gstDigitS Yq 0 = 2 ∧
        (gstAffineMulCarryS 4 Cq Yq 0 = 0 ∨
         gstAffineMulCarryS 4 Cq Yq 0 = 3)) := by
  dsimp only
  have hsuffix := gst_seeded_bad_trace_suffixS D (Z + A*Y) q hbad
  have hshape := gst_relative_affine_suffixS A Z Y q
  have hgate0 := gst_seeded_gate_localizesS C Y q hgate
  constructor
  · rw [hshape] at hsuffix
    exact hsuffix
  · exact hgate0
