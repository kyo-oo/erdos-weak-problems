/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0893 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/PrefixOneTerminalZScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 08:02:36 +0530  (6be2e4b)
/-    Last-commit  : 2026-08-17 08:02:36 +0530  (6be2e4b)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:02:36 +0530  6be2e4b  (ker07-dev)
/-        Add terminal seed-one prefix stripping mechanics
/- ====================================================================== -/

import PurePowerBadAxisScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Prefix-one terminal z mechanics

This file isolates the finite-origin base case suggested by the full
handwritten Ω/U/Navigation constructor.  It is deliberately independent of the
broken monolith-facing prefix-one theorem.

If an ordinary canonical word has the forced low ternary prefix

    1 + 3*z,

then stripping that one trit turns the ordinary multiply-by-four carry into a
seed-one affine carry on `z`.  Hence every Happy Gate above the forced prefix
is exactly a seed-one Happy Gate of `z`.
-/

/-- Exact digit stripping through the forced leading ternary digit one. -/
theorem gst_prefixed_one_digit_shiftS
    (z j : Nat) :
    gstDigitS (1 + 3*z) (j+1) = gstDigitS z j := by
  have h := gst_prefixed_tail_digitS 1 z 1 j (by decide : 1 < 3^1)
  norm_num at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Exact carry stripping through the forced leading ternary digit one.
The stripped word inherits incoming GST seed one. -/
theorem gst_prefixed_one_carry_shiftS
    (z j : Nat) :
    gstCarryS (1 + 3*z) (j+1) =
      gstAffineMulCarryS 4 1 z j := by
  have h := gst_prefixed_tail_carryS 1 z 1 j (by decide : 1 < 3^1)
  norm_num at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Happy-gate equivalence after removing the forced prefix `1`.
This is an iff: no gate is invented or lost by the coordinate change. -/
theorem gst_prefixed_one_happy_iff_seed_oneS
    (z j : Nat) :
    (gstDigitS (1 + 3*z) (j+1) = 2 ∧
      (gstCarryS (1 + 3*z) (j+1) = 0 ∨
       gstCarryS (1 + 3*z) (j+1) = 3)) ↔
    (gstDigitS z j = 2 ∧
      (gstAffineMulCarryS 4 1 z j = 0 ∨
       gstAffineMulCarryS 4 1 z j = 3)) := by
  rw [gst_prefixed_one_digit_shiftS, gst_prefixed_one_carry_shiftS]

/-- The forced first digit of `1+3*z` is one, so position zero itself can never
be a Happy Gate. -/
theorem gst_prefixed_one_not_happy_zeroS
    (z : Nat) :
    ¬ (gstDigitS (1 + 3*z) 0 = 2 ∧
      (gstCarryS (1 + 3*z) 0 = 0 ∨
       gstCarryS (1 + 3*z) 0 = 3)) := by
  intro h
  have hd : gstDigitS (1 + 3*z) 0 = 1 := by
    simp [gstDigitS]
  omega

/-- Property-level terminal adapter.  Any ordinary Happy Gate of `1+3*z`
must lie above the forced prefix and therefore yields a seed-one gate of `z`.
The witness is supplied explicitly so this theorem has no dependency on the
monolith's Navigation witness type. -/
theorem gst_terminal_seed_one_gate_of_prefixed_oneS
    (z p : Nat)
    (hgate : gstDigitS (1 + 3*z) p = 2 ∧
      (gstCarryS (1 + 3*z) p = 0 ∨
       gstCarryS (1 + 3*z) p = 3)) :
    ∃ j,
      gstDigitS z j = 2 ∧
        (gstAffineMulCarryS 4 1 z j = 0 ∨
         gstAffineMulCarryS 4 1 z j = 3) := by
  have hp : 1 ≤ p := by
    by_contra hnot
    have hp0 : p = 0 := by omega
    subst p
    exact gst_prefixed_one_not_happy_zeroS z hgate
  let j := p - 1
  have hpj : p = j + 1 := by
    dsimp [j]
    omega
  refine ⟨j, ?_⟩
  rw [hpj] at hgate
  exact (gst_prefixed_one_happy_iff_seed_oneS z j).1 hgate
