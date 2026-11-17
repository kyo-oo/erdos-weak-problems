/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0935 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/HandwrittenKernelCanonicalLevelOneScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 08:39:44 +0530  (4c8b342)
/-    Last-commit  : 2026-08-17 08:39:44 +0530  (4c8b342)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:39:44 +0530  4c8b342  (ker07-dev)
/-        Identify handwritten 7/(x-6) with canonical GST level-one data
/- ====================================================================== -/

import CanonicalPrefixScratch
import HandwrittenSixUniverseScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Canonical meaning of the handwritten 7/(x-6) kernel at GST level one

The constants 7 and 6 are not introduced here: they are shown to be the exact
first canonical GST bridge coefficient and its forced-prefix displacement.
-/

/-- The canonical level-one block is 4^3 = 64. -/
theorem gst_level_one_block_eq_64S : (4:Nat)^(3^1) = 64 := by
  decide

/-- The canonical Navigation unit at level one is seven. -/
theorem gst_level_one_Q1_eq_7S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 1 = 7 := by
  have h := hQ 1 1 (by decide)
  norm_num at h
  omega

/-- The forced prefix-one tail coordinate is therefore z_1=2. -/
theorem gst_level_one_z_eq_2S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (z1 : Nat) (hz : Q 1 1 = 1 + 3*z1) :
    z1 = 2 := by
  rw [gst_level_one_Q1_eq_7S Q hQ] at hz
  omega

/-- Boss's denominator pole 6 is exactly c_1-1 = 3*z_1. -/
theorem gst_handwritten_six_is_level_one_prefix_displacementS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 1 - 1 = 6 := by
  rw [gst_level_one_Q1_eq_7S Q hQ]

/-- The exact level-one binary Navigation quotient. -/
theorem gst_level_one_Q2_eq_455S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 2 = 455 := by
  have h := hQ 1 2 (by decide)
  norm_num at h
  omega

/-- All three factors from the full handwritten/V2 experiment are canonical
level-one expressions in c_1=7. -/
theorem gst_level_one_455_canonical_factorS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 2 =
      Q 1 1 * (Q 1 1 - 2) * (2*Q 1 1 - 1) := by
  rw [gst_level_one_Q2_eq_455S Q hQ,
    gst_level_one_Q1_eq_7S Q hQ]
  decide

/-- Equivalent six-world factorization. -/
theorem gst_level_one_455_six_world_factorS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 2 = (6^2 - 1) * (2*6 + 1) := by
  rw [gst_level_one_Q2_eq_455S Q hQ]
  decide

/-- 455 has the exact alternating ternary word 121212 (MSD first).  The Nat
identity below is the LSB-first digit expansion 2,1,2,1,2,1. -/
theorem gst_level_one_Q2_ternary_121212S
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    Q 1 2 =
      2*3^0 + 1*3^1 + 2*3^2 + 1*3^3 + 2*3^4 + 1*3^5 := by
  rw [gst_level_one_Q2_eq_455S Q hQ]
  decide

/-- The event factor 13 is exactly two times the six-state boundary plus one,
and equally 2*c_1-1. -/
theorem gst_level_one_event_factor_thirteenS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q) :
    13 = 2*6 + 1 ∧ 13 = 2*Q 1 1 - 1 := by
  rw [gst_level_one_Q1_eq_7S Q hQ]
  decide
