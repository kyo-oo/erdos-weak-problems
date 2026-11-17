/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1098 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/ScopedTwoDigitPhysicalBlockScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Last-commit  : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
/-        surgery: lock 5c579 with full BIG-N right-chord research monolith
/- ====================================================================== -/

import RightChordCanonicalGateScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Scoped physical two-information-digit block

Boss's correction is enforced literally here.

`I != 1` is NOT quantified over a trace.  It is introduced only for a single
chosen pair of consecutive information digits `p,p+1`.  When the formula also
selects the nonzero sector for those two entries, finite ternary legality makes
the pair exactly `22`.

If the incoming physical GST carry at that pair is 3, the aligned two-row mass
is then

  3 + 4*(22_3) = 3 + 4*8 = 35 = 6^2-1,

and both rows are literal GST+ Happy Gates.  Consequently a complete bad suffix
with seed 3 cannot contain such a selected two-digit component.
-/

/-- Boss's local two-digit information condition at exactly positions p,p+1.
No statement is made about any other information position. -/
def GSTScopedTwoInformationDigitsS (X p : Nat) : Prop :=
  gstDigitS X p ≠ 0 ∧
  gstDigitS X p ≠ 1 ∧
  gstDigitS X (p+1) ≠ 0 ∧
  gstDigitS X (p+1) ≠ 1

/-- In a legal ternary word, the locally selected nonzero / not-BIG1 pair is
exactly the physical two-trit word 22. -/
theorem gst_scoped_two_information_digits_force_22S
    (X p : Nat)
    (hscope : GSTScopedTwoInformationDigitsS X p) :
    gstDigitS X p = 2 ∧ gstDigitS X (p+1) = 2 := by
  have h0lt : gstDigitS X p < 3 := gst_digitS_lt_three_allS X p
  have h1lt : gstDigitS X (p+1) < 3 := gst_digitS_lt_three_allS X (p+1)
  constructor <;> omega

/-- Exact aligned base-nine word and 36-state mass of the scoped two-digit
component when its incoming carry is GST+ carry three. -/
theorem gst_scoped_two_digit_seed_three_is_physical_35S
    (D X p : Nat)
    (hD3 : gstAffineMulCarryS 4 D X p = 3)
    (hscope : GSTScopedTwoInformationDigitsS X p) :
    let w := gstDigitS X p + 3*gstDigitS X (p+1)
    w = 8 ∧
      gstAffineMulCarryS 4 D X p + 4*w = 35 ∧
      35 = 6^2 - 1 ∧
      gstAffineMulCarryS 4 D X (p+1) = 3 := by
  dsimp only
  obtain ⟨hd0, hd1⟩ :=
    gst_scoped_two_information_digits_force_22S X p hscope
  have hstep := gstAffineS_forward_exact_all D X p
  rw [hd0, hD3] at hstep
  norm_num [gstStepCarryS] at hstep
  rw [hd0, hd1, hD3, hstep]
  decide

/-- The 35 cell is physically Happy at BOTH rows, not merely an aligned
re-coordinate. -/
theorem gst_scoped_two_digit_seed_three_two_happy_rowsS
    (D X p : Nat)
    (hD3 : gstAffineMulCarryS 4 D X p = 3)
    (hscope : GSTScopedTwoInformationDigitsS X p) :
    GSTSeededHappyS D X p ∧ GSTSeededHappyS D X (p+1) := by
  obtain ⟨hd0, hd1⟩ :=
    gst_scoped_two_information_digits_force_22S X p hscope
  have hstep := gstAffineS_forward_exact_all D X p
  rw [hd0, hD3] at hstep
  norm_num [gstStepCarryS] at hstep
  constructor
  · exact ⟨hd0, Or.inr hD3⟩
  · exact ⟨hd1, Or.inr hstep⟩

/-- A complete bad trace can never contain one locally selected two-digit
nonzero/not-BIG1 component at a position whose incoming carry is 3. -/
theorem gst_bad_trace_forbids_scoped_two_digit_at_seed_threeS
    (D X p : Nat)
    (hbad : GSTSeededBadTraceS D X)
    (hD3 : gstAffineMulCarryS 4 D X p = 3) :
    ¬ GSTScopedTwoInformationDigitsS X p := by
  intro hscope
  have hhappy :=
    gst_scoped_two_digit_seed_three_two_happy_rowsS D X p hD3 hscope
  exact (hbad p) hhappy.1

/-- Position-zero specialization used by the strengthened canonical trap.
A seeded bad suffix with exact incoming seed 3 cannot begin with Boss's scoped
two-digit nonzero/not-BIG1 component. -/
theorem gst_seed_three_bad_suffix_forbids_scoped_two_digit_headS
    (Y : Nat)
    (hbad : GSTSeededBadTraceS 3 Y) :
    ¬ GSTScopedTwoInformationDigitsS Y 0 := by
  have hC0 : gstAffineMulCarryS 4 3 Y 0 = 3 := by
    simp [gstAffineMulCarryS]
  exact gst_bad_trace_forbids_scoped_two_digit_at_seed_threeS
    3 Y 0 hbad hC0

/-- Pack the physical right chord at the head of a seed-three suffix.  This is
exactly the two-digit case that would contradict trapped complete badness. -/
theorem gst_seed_three_scoped_two_digit_head_chord_35S
    (Y : Nat)
    (hscope : GSTScopedTwoInformationDigitsS Y 0) :
    let w := gstDigitS Y 0 + 3*gstDigitS Y 1
    w = 8 ∧ 3 + 4*w = 35 ∧ 35 = 6^2 - 1 := by
  dsimp only
  obtain ⟨hd0, hd1⟩ :=
    gst_scoped_two_information_digits_force_22S Y 0 hscope
  rw [hd0, hd1]
  decide
