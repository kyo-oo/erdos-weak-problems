/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0161 / 1132
/-    Path         : branches/sol_comparator-surgery/SynchronizerScratch.lean
/-    Ref          : origin/sol/comparator-surgery
/-    First-commit : 2026-08-15 10:01:27 +0530  (04ac43f)
/-    Last-commit  : 2026-08-15 10:01:27 +0530  (04ac43f)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-15 10:01:27 +0530  04ac43f  (ker07-dev)
/-        Formalize universal GST 12102 synchronizer
/- ====================================================================== -/

import Mathlib

/-!
Finite GST synchronizer facts used by the corrected phase-strip surgery.
No perfect-power or Erdős theorem appears in this file.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def gstSyncStepS (C d : Nat) : Nat := (C + 4*d) / 3

def gstSyncHappyS (C d : Nat) : Prop :=
  d = 2 ∧ (C = 0 ∨ C = 3)

/-- The prefix 1210 resets every legal incoming GST carry to NULL. -/
theorem gst_word_1210_resetsS
    (C : Nat) (hC : C < 4) :
    gstSyncStepS
      (gstSyncStepS
        (gstSyncStepS
          (gstSyncStepS C 1) 2) 1) 0 = 0 := by
  have hcases : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · subst C; decide
  · subst C; decide
  · subst C; decide
  · subst C; decide

/-- Therefore the complete stable c-tower word 12102 is a universal Happy
    synchronizer: its final digit 2 is read in NULL carry. -/
theorem gst_word_12102_synchronizesS
    (C : Nat) (hC : C < 4) :
    gstSyncHappyS
      (gstSyncStepS
        (gstSyncStepS
          (gstSyncStepS
            (gstSyncStepS C 1) 2) 1) 0)
      2 := by
  have hreset := gst_word_1210_resetsS C hC
  simp [gstSyncHappyS, hreset]

/-- A globally bad GST trace cannot contain the synchronizing word 12102 at
    any position once the incoming carry is known to be below four. -/
theorem gst_bad_trace_forbids_12102S
    (carryAt : Nat → Nat) (digitAt : Nat → Nat) (p : Nat)
    (hC : carryAt p < 4)
    (hstep : ∀ j,
      carryAt (j+1) = gstSyncStepS (carryAt j) (digitAt j))
    (hbad : ∀ j, ¬ gstSyncHappyS (carryAt j) (digitAt j))
    (h0 : digitAt p = 1)
    (h1 : digitAt (p+1) = 2)
    (h2 : digitAt (p+2) = 1)
    (h3 : digitAt (p+3) = 0)
    (h4 : digitAt (p+4) = 2) :
    False := by
  have s0 := hstep p
  have s1 := hstep (p+1)
  have s2 := hstep (p+2)
  have s3 := hstep (p+3)
  rw [h0] at s0
  rw [h1] at s1
  rw [h2] at s2
  rw [h3] at s3
  have hcases : carryAt p = 0 ∨ carryAt p = 1 ∨
      carryAt p = 2 ∨ carryAt p = 3 := by omega
  have hfinal : carryAt (p+4) = 0 := by
    rcases hcases with hc0 | hc1 | hc2 | hc3
    · rw [hc0] at s0
      norm_num [gstSyncStepS] at s0
      rw [s0] at s1
      norm_num [gstSyncStepS] at s1
      rw [s1] at s2
      norm_num [gstSyncStepS] at s2
      rw [s2] at s3
      norm_num [gstSyncStepS] at s3
      exact s3
    · rw [hc1] at s0
      norm_num [gstSyncStepS] at s0
      rw [s0] at s1
      norm_num [gstSyncStepS] at s1
      rw [s1] at s2
      norm_num [gstSyncStepS] at s2
      rw [s2] at s3
      norm_num [gstSyncStepS] at s3
      exact s3
    · rw [hc2] at s0
      norm_num [gstSyncStepS] at s0
      rw [s0] at s1
      norm_num [gstSyncStepS] at s1
      rw [s1] at s2
      norm_num [gstSyncStepS] at s2
      rw [s2] at s3
      norm_num [gstSyncStepS] at s3
      exact s3
    · rw [hc3] at s0
      norm_num [gstSyncStepS] at s0
      rw [s0] at s1
      norm_num [gstSyncStepS] at s1
      rw [s1] at s2
      norm_num [gstSyncStepS] at s2
      rw [s2] at s3
      norm_num [gstSyncStepS] at s3
      exact s3
  exact hbad (p+4) ⟨h4, Or.inl hfinal⟩
