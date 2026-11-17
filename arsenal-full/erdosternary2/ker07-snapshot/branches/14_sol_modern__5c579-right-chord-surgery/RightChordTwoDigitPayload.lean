/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1060 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/RightChordTwoDigitPayload.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 21:15:11 +0530  (2340c30)
/-    Last-commit  : 2026-08-17 21:15:11 +0530  (2340c30)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 21:15:11 +0530  2340c30  (ker07-dev)
/-        Add scoped two-digit right-chord surgery payload
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Right-chord two-digit surgery payload

This file is deliberately scoped to ONE physical x4/two-digit cell.
The handwritten condition `I != 1` is used only while resolving that
specific two-micro-layer cell; it is not promoted to a global hypothesis
on the rest of the Erdős/GST proof.

The exact local bridge is

  a + 2*d = e + 3*a'

and one x4 cell decomposes into two x2/base-3 micro bridges.  The scoped
BIG1-clear projector removes the two orientation-changing realizations and
forces the unique GST+ SURVIVE/SURVIVE realization `(5,5)`.
-/

/-- Fundamental x2/base-3 bridge output information digit. -/
def rcBridgeOutput (a d : Nat) : Nat :=
  (a + 2*d) % 3

/-- Fundamental x2/base-3 bridge next binary carry. -/
def rcBridgeNextCarry (a d : Nat) : Nat :=
  (a + 2*d) / 3

/-- Fundamental six-state bridge mass. -/
def rcBridgeMass (a d : Nat) : Nat :=
  a + 2*d

/-- Two-trit event symbol d + 3e. -/
def rcBridgeEvent (a d : Nat) : Nat :=
  d + 3 * rcBridgeOutput a d

/-- Exact local 2-world/3-world bridge equation. -/
theorem rc_bridge_exact (a d : Nat) :
    rcBridgeMass a d = rcBridgeOutput a d + 3 * rcBridgeNextCarry a d := by
  unfold rcBridgeMass rcBridgeOutput rcBridgeNextCarry
  have h := Nat.mod_add_div (a + 2*d) 3
  omega

/-- Exact local origin of the handwritten numerator seven. -/
theorem rc_bridge_event_seven_balance (a d : Nat) :
    rcBridgeEvent a d + 9 * rcBridgeNextCarry a d = 7*d + 3*a := by
  unfold rcBridgeEvent rcBridgeOutput rcBridgeNextCarry
  have h := Nat.mod_add_div (a + 2*d) 3
  omega

/-- Split a legal x4 carry into the two binary micro carries. -/
def rcMicroHighBit (C : Nat) : Nat := C / 2
def rcMicroLowBit  (C : Nat) : Nat := C % 2

/-- First x2 micro mass inside an x4 cell. -/
def rcFirstMicroMass (C d : Nat) : Nat := rcMicroHighBit C + 2*d

/-- Intermediate information digit. -/
def rcFirstMicroOutput (C d : Nat) : Nat := rcFirstMicroMass C d % 3

/-- Second x2 micro mass inside an x4 cell. -/
def rcSecondMicroMass (C d : Nat) : Nat :=
  rcMicroLowBit C + 2 * rcFirstMicroOutput C d

/-- Output information digit after the second micro layer. -/
def rcSecondMicroOutput (C d : Nat) : Nat := rcSecondMicroMass C d % 3

/-- Integer denominator of the handwritten kernel magnitude |7/(x-6)|
    on the physical spectrum x<6. -/
def rcKernelDenom (x : Nat) : Nat := 6 - x

/-- The three canonical two-layer orientations. -/
theorem rc_two_digit_orientation_table :
    (rcFirstMicroMass 0 1, rcSecondMicroMass 0 1) = (2,4) ∧
    (rcFirstMicroMass 0 2, rcSecondMicroMass 0 2) = (4,2) ∧
    (rcFirstMicroMass 3 2, rcSecondMicroMass 3 2) = (5,5) := by
  decide

/-- SCOPED projector theorem.

Use `I != 1` only at the input/intermediate/output information vertices of
this two-digit cell.  Together with a nonzero aligned input it forces the
unique physical GST+ cell:

  C=3, d=2, 2 -> 2 -> 2, masses (5,5), events SURVIVE/SURVIVE.
-/
theorem rc_two_digit_big1_clear_forces_gst_plus
    (C d : Nat)
    (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0)
    (hin1 : d ≠ 1)
    (hmid1 : rcFirstMicroOutput C d ≠ 1)
    (hout1 : rcSecondMicroOutput C d ≠ 1) :
    C = 3 ∧ d = 2 ∧
      rcFirstMicroOutput C d = 2 ∧
      rcSecondMicroOutput C d = 2 ∧
      rcFirstMicroMass C d = 5 ∧
      rcSecondMicroMass C d = 5 := by
  have hd2 : d = 2 := by omega
  subst d
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    subst C <;>
    norm_num [rcFirstMicroOutput, rcFirstMicroMass,
      rcSecondMicroOutput, rcSecondMicroMass,
      rcMicroHighBit, rcMicroLowBit] at hmid1 hout1 ⊢

/-- The same scoped theorem expressed as the exact right chord:

  55_6 = 35 = 6^2 - 1,

and the kernel denominator is one on each surviving micro edge, hence
|7/(5-6)| = 7. -/
theorem rc_two_digit_right_chord_35
    (C d : Nat)
    (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0)
    (hin1 : d ≠ 1)
    (hmid1 : rcFirstMicroOutput C d ≠ 1)
    (hout1 : rcSecondMicroOutput C d ≠ 1) :
    rcFirstMicroMass C d + 6 * rcSecondMicroMass C d = 35 ∧
      35 = 6^2 - 1 ∧
      rcKernelDenom (rcFirstMicroMass C d) = 1 ∧
      rcKernelDenom (rcSecondMicroMass C d) = 1 := by
  obtain ⟨_hC3, _hd2, _hm, _ho, hM1, hM2⟩ :=
    rc_two_digit_big1_clear_forces_gst_plus C d hC hd hd0 hin1 hmid1 hout1
  rw [hM1, hM2]
  decide

/-- Mixed-radix form of exactly the same two-digit chord:
    C=3 and ternary word 22_3 = 8 give 3 + 4*8 = 35. -/
theorem rc_aligned_36_state_chord :
    8 = 2 + 3*2 ∧ 3 + 4*8 = 35 ∧ 35 = 6^2 - 1 := by
  decide

/-- General six-world coefficient used by the 11-equation chord.
    This definition does NOT impose `I != 1` globally; it only records the
    algebraic coefficient that the two-digit case specializes to at k=2. -/
def rcWorldProjectionCoefficient (k : Nat) : Nat := 6^k - 1

theorem rc_world_projection_coefficient_two_digit :
    rcWorldProjectionCoefficient 2 = 35 := by
  decide
