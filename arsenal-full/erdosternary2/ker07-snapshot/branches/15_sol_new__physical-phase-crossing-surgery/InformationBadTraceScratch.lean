/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0214 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery/InformationBadTraceScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery
/-    First-commit : 2026-08-15 10:45:20 +0530  (7e5cadd)
/-    Last-commit  : 2026-08-15 10:45:20 +0530  (7e5cadd)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 10:45:20 +0530  7e5cadd  (ker07-dev)
/-        Add bad-trace consequences for information surgery
/- ====================================================================== -/

import InformationDescentScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Scratch copy of the real bad-pair predicate. -/
def GSTBadPairS (C d : Nat) : Prop :=
  ¬ (d = 2 ∧ (C = 0 ∨ C = 3))

/-- A seed-retaining affine bad trace cannot contain the universal 22 synchronizer. -/
theorem gst_bad_trace_forbids_22S
    (D X : Nat)
    (hD : D < 4)
    (hbad : ∀ j, GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)) :
    ∀ j, ¬ (gstDigitS X j = 2 ∧ gstDigitS X (j+1) = 2) := by
  intro j h22
  rcases h22 with ⟨hd0, hd1⟩
  have hC : gstAffineMulCarryS 4 D X j < 4 :=
    gst_affine_carry_lt_multiplierS 4 D X j (by decide) hD
  rcases gst_two_two_forces_happy_gateS D X j hC hd0 hd1 with h0 | h1
  · exact (hbad j) h0
  · exact (hbad (j+1)) h1

/-- The LSB-first word 1,2,1,0,2 is a universal bad-state destroyer. -/
theorem gst_word_12102_synchronizesS (C : Nat) (hC : C < 4) :
    (C = 0 ∨ C = 3) ∨
    let C1 := gstStepCarryS C 1
    (C1 = 0 ∨ C1 = 3) ∨
    let C2 := gstStepCarryS C1 2
    let C3 := gstStepCarryS C2 1
    let C4 := gstStepCarryS C3 0
    (C4 = 0 ∨ C4 = 3) := by
  rcases Nat.lt_trichotomy C 1 with hlt | heq | hgt
  · have h0 : C = 0 := by omega
    exact Or.inl (Or.inl h0)
  · subst C
    norm_num [gstStepCarryS]
  · have hcases : C = 2 ∨ C = 3 := by omega
    rcases hcases with h2 | h3
    · subst C
      norm_num [gstStepCarryS]
    · subst C
      exact Or.inl (Or.inr rfl)
