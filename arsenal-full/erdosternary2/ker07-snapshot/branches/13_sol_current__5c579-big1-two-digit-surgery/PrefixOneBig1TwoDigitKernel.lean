/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1056 / 1132
/-    Path         : branches/sol_5c579-big1-two-digit-surgery/PrefixOneBig1TwoDigitKernel.lean
/-    Ref          : origin/sol/5c579-big1-two-digit-surgery
/-    First-commit : 2026-08-17 20:53:55 +0530  (c3c0955)
/-    Last-commit  : 2026-08-17 20:55:35 +0530  (1c2e31e)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 20:53:55 +0530  c3c0955  (ker07-dev)
/-        Add local two-digit BIG1 projector kernel for 5c579 surgery
/- [02/2] 2026-08-17 20:55:35 +0530  1c2e31e  (ker07-dev)
/-        Add exact x4 reconstruction identities to local two-digit kernel
/- ====================================================================== -/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Prefix-one two-digit BIG1 projector kernel

Surgery rule: `I ≠ 1` is NOT a global hypothesis on an Ω∞ trace.
It is used only while solving an actual two-digit / two-micro-layer cell of
Boss's handwritten operator.  The unrestricted Ω∞ and Navigation layers remain
unchanged outside that local cell.

One physical x4 cell is decomposed into two x2/base3 bridges.  A legal x4 carry
`C < 4` supplies binary high/low bits.  With incoming ternary information digit
`d < 3`, the two microscopic masses and information outputs are exact natural
number formulas below.
-/

def gstSurgeryMicroHighBit (C : Nat) : Nat := C / 2
def gstSurgeryMicroLowBit (C : Nat) : Nat := C % 2

def gstSurgeryFirstMass (C d : Nat) : Nat :=
  gstSurgeryMicroHighBit C + 2*d

def gstSurgeryFirstOutput (C d : Nat) : Nat :=
  gstSurgeryFirstMass C d % 3

def gstSurgeryFirstCarry (C d : Nat) : Nat :=
  gstSurgeryFirstMass C d / 3

def gstSurgerySecondMass (C d : Nat) : Nat :=
  gstSurgeryMicroLowBit C + 2*gstSurgeryFirstOutput C d

def gstSurgerySecondOutput (C d : Nat) : Nat :=
  gstSurgerySecondMass C d % 3

def gstSurgerySecondCarry (C d : Nat) : Nat :=
  gstSurgerySecondMass C d / 3

/-- The two x2 micro layers are not an alternate-space metaphor: together they
reconstruct the literal physical x4/base3 output digit for every legal cell. -/
theorem gst_surgery_two_micro_reconstruct_x4_output
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstSurgerySecondOutput C d = (C + 4*d) % 3 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- The two microscopic binary carries also reconstruct the literal physical
x4/base3 outgoing carry. -/
theorem gst_surgery_two_micro_reconstruct_x4_carry
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    2 * gstSurgeryFirstCarry C d + gstSurgerySecondCarry C d =
      (C + 4*d) / 3 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- Exact orientation table used by the physical two-digit solve. -/
theorem gst_surgery_two_digit_orientation_table :
    (gstSurgeryFirstMass 0 1, gstSurgerySecondMass 0 1) = (2,4) ∧
    (gstSurgeryFirstOutput 0 1, gstSurgerySecondOutput 0 1) = (2,1) ∧
    (gstSurgeryFirstMass 0 2, gstSurgerySecondMass 0 2) = (4,2) ∧
    (gstSurgeryFirstOutput 0 2, gstSurgerySecondOutput 0 2) = (1,2) ∧
    (gstSurgeryFirstMass 3 2, gstSurgerySecondMass 3 2) = (5,5) ∧
    (gstSurgeryFirstOutput 3 2, gstSurgerySecondOutput 3 2) = (2,2) := by
  decide

/-- LOCAL two-digit projector.

Only inside this two-digit solve, incoming/intermediate/output information are
required to avoid BIG1.  Nonzero input then forces the unique GST+ orientation:
`C=3`, `d=2`, information path `2 -> 2 -> 2`, microscopic masses `(5,5)`.
-/
theorem gst_surgery_local_big1_two_digit_forces_gst_plus
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstSurgeryFirstOutput C d ≠ 1)
    (hout1 : gstSurgerySecondOutput C d ≠ 1) :
    C = 3 ∧ d = 2 ∧
      gstSurgeryFirstOutput C d = 2 ∧
      gstSurgerySecondOutput C d = 2 ∧
      gstSurgeryFirstMass C d = 5 ∧
      gstSurgerySecondMass C d = 5 := by
  have hd2 : d = 2 := by omega
  subst d
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    subst C <;>
    norm_num [gstSurgeryFirstOutput, gstSurgeryFirstMass,
      gstSurgerySecondOutput, gstSurgerySecondMass,
      gstSurgeryMicroHighBit, gstSurgeryMicroLowBit] at hmid1 hout1 ⊢

/-- On the locally projected child Happy Gate, the selected microscopic state
is therefore the physical x4 GST+ state and its literal x4 output remains BIG2. -/
theorem gst_surgery_local_big1_two_digit_is_physical_gst_plus
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstSurgeryFirstOutput C d ≠ 1)
    (hout1 : gstSurgerySecondOutput C d ≠ 1) :
    C = 3 ∧ d = 2 ∧
      (C + 4*d) % 3 = 2 ∧
      (C + 4*d) / 3 = 3 := by
  obtain ⟨hC3, hd2, _hm, hout, _hM1, _hM2⟩ :=
    gst_surgery_local_big1_two_digit_forces_gst_plus
      C d hC hd hd0 hd1 hmid1 hout1
  subst C
  subst d
  decide

/-- Right-chord value selected by the local two-digit projector. -/
theorem gst_surgery_local_big1_two_digit_chord_35
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstSurgeryFirstOutput C d ≠ 1)
    (hout1 : gstSurgerySecondOutput C d ≠ 1) :
    gstSurgeryFirstMass C d + 6 * gstSurgerySecondMass C d = 35 := by
  obtain ⟨_hC3, _hd2, _hm, _ho, hM1, hM2⟩ :=
    gst_surgery_local_big1_two_digit_forces_gst_plus
      C d hC hd hd0 hd1 hmid1 hout1
  rw [hM1, hM2]

/-- `55_6 = 35 = 6^2-1`, and the same 35 is the aligned 36-state V2 mass
`C + 4*w` at `(C,w)=(3,8)` with `w=(22)_3`. -/
theorem gst_surgery_right_chord_identifications :
    5 + 6*5 = 35 ∧
    35 = 6^2 - 1 ∧
    8 = 2 + 3*2 ∧
    3 + 4*8 = 35 := by
  decide

/-- On the surviving mass five, Boss's handwritten kernel has denominator one:
`|7/(5-6)| = 7`.  The theorem records the exact natural denominator identity. -/
def gstSurgeryKernelDenom (m : Nat) : Nat := 6 - m

theorem gst_surgery_gst_plus_kernel_denominator_one :
    gstSurgeryKernelDenom 5 = 1 := by
  decide
