/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0181 / 1132
/-    Path         : branches/sol_phase-crossing-surgery/CarryWordScratch.lean
/-    Ref          : origin/sol/phase-crossing-surgery
/-    First-commit : 2026-08-15 10:05:50 +0530  (3f6e523)
/-    Last-commit  : 2026-08-15 10:22:15 +0530  (b3477e8)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-15 10:05:50 +0530  3f6e523  (ker07-dev)
/-        Formalize horizontal GST carry-word decomposition
/- [02/3] 2026-08-15 10:16:22 +0530  4f5ec51  (ker07-dev)
/-        Fix horizontal carry append recurrence proof
/- [03/3] 2026-08-15 10:22:15 +0530  b3477e8  (ker07-dev)
/-        Use explicit numerator congruence in carry-word recurrence
/- ====================================================================== -/

import Mathlib

/-!
Generic radix theorem behind the GST phase strip.
For a fixed ternary cut M, repeated multiplication by 4 produces one carry
per horizontal step.  The quotient after many steps stores those carries as
its base-4 digits, in reverse chronological order.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def gstStripQuotientS (r M j : Nat) : Nat :=
  (4^j * r) / M

def gstStripCarryS (r M j : Nat) : Nat :=
  (4 * ((4^j * r) % M)) / M

/-- One horizontal ×4 step appends exactly one base-4 carry digit. -/
theorem gst_strip_quotient_succS
    (r M j : Nat) (hM : 0 < M) :
    gstStripQuotientS r M (j+1) =
      4 * gstStripQuotientS r M j + gstStripCarryS r M j := by
  simp only [gstStripQuotientS, gstStripCarryS]
  have hsplit :
      4^j * r = M * ((4^j * r) / M) + (4^j * r) % M := by
    exact (Nat.div_add_mod (4^j * r) M).symm
  have hnumPow : 4^(j+1) * r = 4 * (4^j * r) := by
    rw [Nat.pow_succ]
    ac_rfl
  calc
    (4^(j+1) * r) / M = (4 * (4^j * r)) / M :=
      congrArg (fun x : Nat => x / M) hnumPow
    _ = (4 * (M * ((4^j * r) / M) + (4^j * r) % M)) / M := by
      rw [← hsplit]
    _ = (4 * ((4^j * r) % M) + M * (4 * ((4^j * r) / M))) / M := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (4 * ((4^j * r) % M)) / M + 4 * ((4^j * r) / M) := by
      rw [Nat.add_mul_div_left _ _ hM]
    _ = 4 * ((4^j * r) / M) + (4 * ((4^j * r) % M)) / M := by ac_rfl

/-- Every horizontal carry is one legal quaternary digit. -/
theorem gst_strip_carry_lt_fourS
    (r M j : Nat) (hM : 0 < M) :
    gstStripCarryS r M j < 4 := by
  unfold gstStripCarryS
  have hr : (4^j * r) % M < M := Nat.mod_lt _ hM
  have hnum : 4 * ((4^j * r) % M) < M * 4 := by
    have h := Nat.mul_lt_mul_of_pos_left hr (by decide : 0 < 4)
    simpa [Nat.mul_comm] using h
  exact Nat.div_lt_of_lt_mul hnum

/-- The newest horizontal carry is the low base-4 digit of the new quotient. -/
theorem gst_strip_quotient_succ_mod4S
    (r M j : Nat) (hM : 0 < M) :
    gstStripQuotientS r M (j+1) % 4 = gstStripCarryS r M j := by
  rw [gst_strip_quotient_succS r M j hM]
  have hc := gst_strip_carry_lt_fourS r M j hM
  omega

/-- Removing the newest base-4 digit recovers the preceding strip quotient. -/
theorem gst_strip_quotient_succ_div4S
    (r M j : Nat) (hM : 0 < M) :
    gstStripQuotientS r M (j+1) / 4 = gstStripQuotientS r M j := by
  rw [gst_strip_quotient_succS r M j hM]
  have hc := gst_strip_carry_lt_fourS r M j hM
  have h4 : 0 < (4:Nat) := by decide
  have hshape :
      4 * gstStripQuotientS r M j + gstStripCarryS r M j =
        gstStripCarryS r M j + 4 * gstStripQuotientS r M j := by ac_rfl
  rw [hshape, Nat.add_mul_div_left _ _ h4]
  have hzero : gstStripCarryS r M j / 4 = 0 := Nat.div_eq_of_lt hc
  simp [hzero]

/-- Repeatedly removing k newest carry digits recovers the older quotient. -/
theorem gst_strip_quotient_shift_divS
    (r M i k : Nat) (hM : 0 < M) :
    gstStripQuotientS r M (i+k) / 4^k = gstStripQuotientS r M i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := gst_strip_quotient_succ_div4S r M (i+k) hM
      have hidx : i + (k+1) = (i+k)+1 := by omega
      rw [hidx]
      have hpow : 4^(k+1) = 4 * 4^k := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hpow, ← Nat.div_div_eq_div_mul]
      rw [hstep]
      exact ih

/-- Every intermediate GST carry is therefore an exact base-4 coordinate of
    the final shared carry word. -/
theorem gst_strip_carry_is_information_digitS
    (r M i k : Nat) (hM : 0 < M) :
    gstStripQuotientS r M (i+k+1) / 4^k % 4 =
      gstStripCarryS r M i := by
  have hshift := gst_strip_quotient_shift_divS r M (i+1) k hM
  have hidx : (i+1)+k = i+k+1 := by omega
  rw [hidx] at hshift
  rw [hshift]
  exact gst_strip_quotient_succ_mod4S r M i hM
