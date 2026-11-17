/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1083 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/HandwrittenUSpaceChargeScratch.lean
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

import GSTGraphV2Scratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Exact V2 space charge for Boss's simultaneous U multiply/divide operator

Every nonfixed local GST V2 re-coordinate orbit has length five.  Directly
from the legal 12-cell table, each such orbit contains one GST+ carry and four
non-GST+ carries (one NULL and three ALT-).  Therefore the integer charge

    GST+  -> +4
    NULL/ALT- -> -1

has zero total on every nonfixed five-cycle.

This determines the exponents of the handwritten simultaneous U operator up to
an overall common scaling.  No physical horizontal-transport claim is made:
this is a theorem about the five alternate readings of one local information
cell.
-/

def gstV2SpaceChargeS (C : Nat) : Int :=
  if C = 3 then 4 else -1

/-- Charge depends exactly on the three-space classification: GST+ gets +4;
NULL and both ALT- carries get -1. -/
theorem gst_v2_space_charge_tableS :
    gstV2SpaceChargeS 0 = -1 ∧
    gstV2SpaceChargeS 1 = -1 ∧
    gstV2SpaceChargeS 2 = -1 ∧
    gstV2SpaceChargeS 3 = 4 := by
  decide

/-- Sum of the space charges seen over five successive local re-coordinates. -/
def gstFiveOrbitChargeS (C d : Nat) : Int :=
  let x0 := (C,d)
  let x1 := gstLocalRotateS x0
  let x2 := gstLocalRotateS x1
  let x3 := gstLocalRotateS x2
  let x4 := gstLocalRotateS x3
  gstV2SpaceChargeS x0.1 + gstV2SpaceChargeS x1.1 +
    gstV2SpaceChargeS x2.1 + gstV2SpaceChargeS x3.1 +
    gstV2SpaceChargeS x4.1

/-- Every legal nonfixed five-cycle is U-neutral. -/
theorem gst_nonfixed_five_orbit_charge_zeroS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hnot0 : (C,d) ≠ (0,0))
    (hnotPlus : (C,d) ≠ (3,2)) :
    gstFiveOrbitChargeS C d = 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    simp [gstFiveOrbitChargeS, gstV2SpaceChargeS, gstLocalRotateS] at hnot0 hnotPlus ⊢

/-- The NULL child Happy gate belongs to a nonfixed BIG2 orbit, so its complete
five-subspace U charge is neutral rather than terminal. -/
theorem gst_null_big2_five_orbit_charge_zeroS :
    gstFiveOrbitChargeS 0 2 = 0 := by
  decide

/-- The fixed GST+ SURVIVE cell has positive charge at every reading. -/
theorem gst_plus_survive_five_orbit_chargeS :
    gstFiveOrbitChargeS 3 2 = 20 := by
  decide

/-- The fixed all-zero NULL cell has negative charge at every reading. -/
theorem gst_null_zero_five_orbit_chargeS :
    gstFiveOrbitChargeS 0 0 = -5 := by
  decide

/-- One explicit nonfixed orbit: 0,2 -> 2,2 -> 3,1 -> 2,1 -> 2,0 -> 0,2.
Its GST+ reading appears exactly once. -/
theorem gst_null_big2_orbit_explicitS :
    let x0 : Nat × Nat := (0,2)
    let x1 := gstLocalRotateS x0
    let x2 := gstLocalRotateS x1
    let x3 := gstLocalRotateS x2
    let x4 := gstLocalRotateS x3
    x1 = (2,2) ∧ x2 = (3,1) ∧ x3 = (2,1) ∧ x4 = (2,0) ∧
      gstLocalRotateS x4 = x0 := by
  decide
