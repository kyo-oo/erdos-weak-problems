/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1064 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/PrefixOneRightChordHistoricalScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 21:32:57 +0530  (a700800)
/-    Last-commit  : 2026-08-17 21:32:57 +0530  (a700800)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 21:32:57 +0530  a700800  (ker07-dev)
/-        Attach scoped two-digit right chord to historical Omega child gate
/- ====================================================================== -/

import ErdosTernary2
import RightChordTwoDigitPayload

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Historical prefix-one right-chord bridge

This file attaches the new finite two-digit payload directly to the exact
`GSTPrefixOneOmegaData` object of the 401200-byte historical monolith.

Scope discipline: `I != 1` is used only while resolving the single x4 / two
micro-layer cell selected by `data.childGateIndex`.  Nothing here assumes a
BIG1 exclusion at every Omega position.
-/

/-- Every historical Omega child carry is a legal x4 carry, including j=0. -/
theorem gst_omega_childCarry_lt_four_right_chord
    (s n j : Nat) :
    (gstOmega s 1 n j).childCarry < 4 := by
  simp only [gstOmega]
  by_cases hj : j = 0
  · subst j
    simp [gstCarry]
  · exact gstCarry_lt_four (gstNavigationConstant (s+1) n) j (by omega)

/-- Every historical Omega child digit is a legal ternary digit. -/
theorem gst_omega_childDigit_lt_three_right_chord
    (s n j : Nat) :
    (gstOmega s 1 n j).childDigit < 3 := by
  simp only [gstOmega]
  exact gstDigit_lt_three (gstNavigationConstant (s+1) n) j

/-- Boss's `I != 1` condition, scoped to the one two-digit cell currently
being resolved.  This is intentionally not quantified over the Omega trace. -/
def GSTOmegaScopedTwoDigitClear
    (s n j : Nat) : Prop :=
  (gstOmega s 1 n j).childDigit ≠ 1 ∧
  rcFirstMicroOutput
      (gstOmega s 1 n j).childCarry
      (gstOmega s 1 n j).childDigit ≠ 1 ∧
  rcSecondMicroOutput
      (gstOmega s 1 n j).childCarry
      (gstOmega s 1 n j).childDigit ≠ 1

/-- At the exact child Happy Gate stored by Old Sol's Omega data, the scoped
handwritten two-digit rule removes the NULL orientation and selects the unique
GST+ right chord.

The result is attached to the historical state itself:

  child carry = 3
  child digit = 2
  information path 2 -> 2 -> 2
  microscopic masses (5,5)
  code 55_6 = 35 = 6^2-1.
-/
theorem gst_prefix_one_omegaData_scoped_child_right_chord
    (s n : Nat)
    (data : GSTPrefixOneOmegaData s n)
    (hclear : GSTOmegaScopedTwoDigitClear s n data.childGateIndex) :
    (gstOmega s 1 n data.childGateIndex).childCarry = 3 ∧
      (gstOmega s 1 n data.childGateIndex).childDigit = 2 ∧
      rcFirstMicroOutput
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit = 2 ∧
      rcSecondMicroOutput
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit = 2 ∧
      rcFirstMicroMass
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit = 5 ∧
      rcSecondMicroMass
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit = 5 ∧
      rcFirstMicroMass
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit +
        6 * rcSecondMicroMass
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit = 35 := by
  let j := data.childGateIndex
  let C := (gstOmega s 1 n j).childCarry
  let d := (gstOmega s 1 n j).childDigit
  have hC : C < 4 := by
    dsimp [C, j]
    exact gst_omega_childCarry_lt_four_right_chord s n data.childGateIndex
  have hd : d < 3 := by
    dsimp [d, j]
    exact gst_omega_childDigit_lt_three_right_chord s n data.childGateIndex
  have hd2 : d = 2 := by
    dsimp [d, j]
    exact data.childGate.1
  have hd0 : d ≠ 0 := by rw [hd2]; decide
  have hlocal :
      d ≠ 1 ∧
      rcFirstMicroOutput C d ≠ 1 ∧
      rcSecondMicroOutput C d ≠ 1 := by
    simpa [GSTOmegaScopedTwoDigitClear, C, d, j] using hclear
  obtain ⟨hC3, hd2', hmid2, hout2, hM1, hM2⟩ :=
    rc_two_digit_big1_clear_forces_gst_plus
      C d hC hd hd0 hlocal.1 hlocal.2.1 hlocal.2.2
  have h35 := rc_two_digit_right_chord_35
    C d hC hd hd0 hlocal.1 hlocal.2.1 hlocal.2.2
  dsimp [C, d, j] at hC3 hd2' hmid2 hout2 hM1 hM2 h35
  exact ⟨hC3, hd2', hmid2, hout2, hM1, hM2, h35.1⟩

/-- The historical child gate's post-cell binary micro carry is one on both
microscopic layers, another exact form of the SURVIVE/SURVIVE orientation. -/
theorem gst_prefix_one_omegaData_scoped_child_micro_carries_one
    (s n : Nat)
    (data : GSTPrefixOneOmegaData s n)
    (hclear : GSTOmegaScopedTwoDigitClear s n data.childGateIndex) :
    rcBridgeNextCarry
        (rcMicroHighBit (gstOmega s 1 n data.childGateIndex).childCarry)
        (gstOmega s 1 n data.childGateIndex).childDigit = 1 ∧
      rcBridgeNextCarry
        (rcMicroLowBit (gstOmega s 1 n data.childGateIndex).childCarry)
        (rcFirstMicroOutput
          (gstOmega s 1 n data.childGateIndex).childCarry
          (gstOmega s 1 n data.childGateIndex).childDigit) = 1 := by
  have h := gst_prefix_one_omegaData_scoped_child_right_chord s n data hclear
  rw [h.1, h.2.1, h.2.2.1]
  decide
