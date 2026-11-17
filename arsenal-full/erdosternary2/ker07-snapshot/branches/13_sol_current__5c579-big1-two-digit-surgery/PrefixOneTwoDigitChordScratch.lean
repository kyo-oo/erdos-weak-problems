/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1061 / 1132
/-    Path         : branches/sol_5c579-big1-two-digit-surgery/PrefixOneTwoDigitChordScratch.lean
/-    Ref          : origin/sol/5c579-big1-two-digit-surgery
/-    First-commit : 2026-08-17 21:16:02 +0530  (5f5de17)
/-    Last-commit  : 2026-08-17 21:16:02 +0530  (5f5de17)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 21:16:02 +0530  5f5de17  (ker07-dev)
/-        Begin 5c579 prefix-one two-digit chord surgery
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Prefix-one two-digit chord surgery scratch

SCOPE LOCK:
`I != 1` is used only for an actual two-digit / two-micro-layer cell.
It is NOT promoted to a universal all-depth hypothesis.

This file isolates the finite six-state rigidity that will be transplanted
into the historical 5c579 prefix-one Ω/navigation closure once the canonical
shared-information cell is identified inside `GSTPrefixOneOmegaData`.
-/

/-- One x2/base3 microscopic bridge. -/
def surgeryBridgeOutput (a d : Nat) : Nat := (a + 2*d) % 3

def surgeryBridgeCarry (a d : Nat) : Nat := (a + 2*d) / 3

def surgeryBridgeMass (a d : Nat) : Nat := a + 2*d

/-- First micro-layer of one physical x4 cell: high carry bit plus information. -/
def surgeryHighBit (C : Nat) : Nat := C / 2

def surgeryLowBit (C : Nat) : Nat := C % 2

def surgeryFirstOut (C d : Nat) : Nat :=
  surgeryBridgeOutput (surgeryHighBit C) d

def surgeryFirstCarry (C d : Nat) : Nat :=
  surgeryBridgeCarry (surgeryHighBit C) d

/-- The second micro-layer receives the exact intermediate information digit. -/
def surgerySecondMass (C d : Nat) : Nat :=
  surgeryLowBit C + 2 * surgeryFirstOut C d

def surgerySecondOut (C d : Nat) : Nat := surgerySecondMass C d % 3

def surgeryFirstMass (C d : Nat) : Nat :=
  surgeryBridgeMass (surgeryHighBit C) d

/-- Two-digit-only BIG1 elimination.  For a legal physical carry C<4 and
ternary input d<3, if the actual two-digit cell begins nonzero and neither
input/intermediate/output information vertex is BIG1, the unique cell is
C=3,d=2 with microscopic masses (5,5) and information path 2->2->2. -/
theorem surgery_two_digit_not1_forces_gst_plus
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : surgeryFirstOut C d ≠ 1)
    (hout1 : surgerySecondOut C d ≠ 1) :
    C = 3 ∧ d = 2 ∧
      surgeryFirstOut C d = 2 ∧
      surgerySecondOut C d = 2 ∧
      surgeryFirstMass C d = 5 ∧
      surgerySecondMass C d = 5 := by
  have hd2 : d = 2 := by omega
  subst d
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    subst C <;>
    norm_num [surgeryFirstOut, surgeryFirstMass, surgerySecondOut,
      surgerySecondMass, surgeryBridgeOutput, surgeryBridgeMass,
      surgeryHighBit, surgeryLowBit] at hmid1 hout1 ⊢

/-- The exact two-digit chord selected by the local projector. -/
theorem surgery_two_digit_chord_35
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : surgeryFirstOut C d ≠ 1)
    (hout1 : surgerySecondOut C d ≠ 1) :
    surgeryFirstMass C d + 6 * surgerySecondMass C d = 35 := by
  obtain ⟨_hC3, _hd2, _hm, _ho, hM1, hM2⟩ :=
    surgery_two_digit_not1_forces_gst_plus C d hC hd hd0 hd1 hmid1 hout1
  rw [hM1, hM2]

/-- 35 is simultaneously the base-six word 55 and the maximal state of the
aligned 4x9 = 36-state two-digit cell. -/
theorem surgery_two_digit_world_chord :
    5 + 6*5 = 35 ∧ 3 + 4*8 = 35 ∧ 8 = 2 + 3*2 ∧ 35 = 6^2 - 1 := by
  decide

/-!
NEXT INCISION (must use historical definitions, not a new assumption):

1. Extract from `GSTPrefixOneOmegaData` the real canonical shared-information
   two-digit cell at/around `childGateIndex`.
2. Derive the four LOCAL premises needed above from the canonical Ω/origin
   geometry.  In particular, `I != 1` must be proved/available for that actual
   two-digit case; it must never be quantified over every depth.
3. Convert the resulting `(5,5)` cell to the historical GST+ / SURVIVE event.
4. Prove a direct parent-SURVIVE lemma and use it to replace the old
   `gst_prefix_one_information_bad_descends_inline -> residual Ω` dependency
   inside `gst_prefix_one_navigation_lift`.
-/