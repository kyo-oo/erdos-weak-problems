/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0872 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/HandwrittenBigNOmegaScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-17 07:27:32 +0530  (1c98216)
/-    Last-commit  : 2026-08-17 07:27:32 +0530  (1c98216)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 07:27:32 +0530  1c98216  (ker07-dev)
/-        Add exact six-state bridge and Navigation-horizon scratch
/- ====================================================================== -/

import OmegaSpacetimeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Handwritten BIG-N / Omega exact algebra scratch

This file contains only exact finite algebra extracted from the handwritten
operator experiment.  It does NOT assert the missing residual termination
law, a global mirror, or terminal NULL.
-/

/-- Output ternary digit of one fundamental multiply-by-two/base-three bridge. -/
def gstBinaryBridgeOutputS (a d : Nat) : Nat :=
  (a + 2*d) % 3

/-- Next binary carry of one fundamental multiply-by-two/base-three bridge. -/
def gstBinaryBridgeNextCarryS (a d : Nat) : Nat :=
  (a + 2*d) / 3

/-- Six-state microscopic mass.  Under `a<2`, `d<3`, this lies in `{0,...,5}`. -/
def gstBinaryBridgeMassS (a d : Nat) : Nat :=
  a + 2*d

/-- Input/output event symbol.  It is the two-trit base-three word `d + 3e`. -/
def gstBinaryBridgeEventS (a d : Nat) : Nat :=
  d + 3 * gstBinaryBridgeOutputS a d

/-- Exact fundamental 2-world / 3-world bridge equation. -/
theorem gst_binary_bridge_exactS (a d : Nat) :
    gstBinaryBridgeMassS a d =
      gstBinaryBridgeOutputS a d +
        3 * gstBinaryBridgeNextCarryS a d := by
  unfold gstBinaryBridgeMassS gstBinaryBridgeOutputS
    gstBinaryBridgeNextCarryS
  have h := Nat.mod_add_div (a + 2*d) 3
  omega

/-- Exact local origin of the handwritten numerator seven.

`J + 9 a' = 7 d + 3 a`.

After base-three weighting and summation over a complete finite word, the
binary-carry boundary telescopes and gives the global event word `7R`. -/
theorem gst_binary_bridge_event_seven_balanceS (a d : Nat) :
    gstBinaryBridgeEventS a d +
        9 * gstBinaryBridgeNextCarryS a d =
      7*d + 3*a := by
  unfold gstBinaryBridgeEventS gstBinaryBridgeOutputS
    gstBinaryBridgeNextCarryS
  have h := Nat.mod_add_div (a + 2*d) 3
  omega

/-- The physical x2 bridge has exactly six possible event symbols.
The missing event symbol `6` is therefore outside the physical microscopic
image. -/
theorem gst_binary_bridge_event_six_valuesS
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    gstBinaryBridgeEventS a d = 0 ∨
    gstBinaryBridgeEventS a d = 1 ∨
    gstBinaryBridgeEventS a d = 3 ∨
    gstBinaryBridgeEventS a d = 5 ∨
    gstBinaryBridgeEventS a d = 7 ∨
    gstBinaryBridgeEventS a d = 8 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- The handwritten pole coordinate `6` is absent from every physical x2
bridge state. -/
theorem gst_binary_bridge_event_ne_sixS
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    gstBinaryBridgeEventS a d ≠ 6 := by
  rcases gst_binary_bridge_event_six_valuesS a d ha hd with
      h0 | h1 | h3 | h5 | h7 | h8 <;> omega

/-- In the microscopic x2 bridge, CREATE is exactly event symbol seven. -/
theorem gst_binary_bridge_create_iff_event7S
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    (d ≠ 2 ∧ gstBinaryBridgeOutputS a d = 2) ↔
      gstBinaryBridgeEventS a d = 7 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- In the microscopic x2 bridge, DESTROY is exactly event symbol five. -/
theorem gst_binary_bridge_destroy_iff_event5S
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    (d = 2 ∧ gstBinaryBridgeOutputS a d ≠ 2) ↔
      gstBinaryBridgeEventS a d = 5 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- In the microscopic x2 bridge, SURVIVE is exactly event symbol eight. -/
theorem gst_binary_bridge_survive_iff_event8S
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    (d = 2 ∧ gstBinaryBridgeOutputS a d = 2) ↔
      gstBinaryBridgeEventS a d = 8 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- Hard phase-one low cell: hidden BIG2 is CREATE then DESTROY. -/
theorem gst_binary_bridge_phase1_hidden_pairS :
    gstBinaryBridgeEventS 0 1 = 7 ∧
      gstBinaryBridgeEventS 0 2 = 5 := by
  norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- NULL Happy cell: the same microscopic orientation is reversed. -/
theorem gst_binary_bridge_null_survive_pairS :
    gstBinaryBridgeEventS 0 2 = 5 ∧
      gstBinaryBridgeEventS 0 1 = 7 := by
  norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-- GST+ Happy cell: both microscopic layers are SURVIVE. -/
theorem gst_binary_bridge_plus_survive_pairS :
    gstBinaryBridgeEventS 1 2 = 8 ∧
      gstBinaryBridgeEventS 1 2 = 8 := by
  norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

/-! General binary block. -/

def gstBinaryBlockOutputS (B C d : Nat) : Nat :=
  (C + B*d) % 3

def gstBinaryBlockNextCarryS (B C d : Nat) : Nat :=
  (C + B*d) / 3

def gstBinaryBlockEventS (B C d : Nat) : Nat :=
  d + 3 * gstBinaryBlockOutputS B C d

/-- General exact event balance.  For `B=2` its event factor is `7`; for
`B=4` it is `13`. -/
theorem gst_binary_block_event_balanceS (B C d : Nat) :
    gstBinaryBlockEventS B C d +
        9 * gstBinaryBlockNextCarryS B C d =
      (1 + 3*B)*d + 3*C := by
  unfold gstBinaryBlockEventS gstBinaryBlockOutputS
    gstBinaryBlockNextCarryS
  have h := Nat.mod_add_div (C + B*d) 3
  omega

/-! Navigation finite horizon.  This is ordinary support arithmetic, not a
terminal-space axiom. -/

theorem gst_self_lt_three_powS : ∀ N : Nat, 1 ≤ N → N < 3^N
  | 0, hN => by omega
  | N+1, hN => by
      by_cases h0 : N = 0
      · subst N
        decide
      · have ih : N < 3^N := gst_self_lt_three_powS N (by omega)
        have hp : 0 < 3^N := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega

/-- At its own natural Navigation index, the ordinary natural descent is
already zero. -/
theorem gst_navigation_self_horizon_zeroS
    (N : Nat) (hN : 1 ≤ N) :
    N / 3^N = 0 := by
  exact Nat.div_eq_of_lt (gst_self_lt_three_powS N hN)

/-- Consequently the ternary information digit of `N` at its own Navigation
index is zero. -/
theorem gst_navigation_self_digit_zeroS
    (N : Nat) (hN : 1 ≤ N) :
    gstDigitS N N = 0 := by
  unfold gstDigitS
  rw [gst_navigation_self_horizon_zeroS N hN]
  simp

/-- The Omega pressure packet has no new transfer at the finite Navigation
horizon itself.  Information already transferred to the past coordinate is not
erased by this statement. -/
theorem gst_omega_transfer_at_navigation_horizon_zeroS
    (t N : Nat) (hN : 1 ≤ N) :
    gstOmegaPressureTransferS t N N = 0 := by
  unfold gstOmegaPressureTransferS
  rw [gst_navigation_self_digit_zeroS N hN]
  simp
