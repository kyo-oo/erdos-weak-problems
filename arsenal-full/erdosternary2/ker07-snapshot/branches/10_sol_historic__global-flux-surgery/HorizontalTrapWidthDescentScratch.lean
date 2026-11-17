/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0948 / 1132
/-    Path         : branches/sol_global-flux-surgery/HorizontalTrapWidthDescentScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 08:58:46 +0530  (47a4fe4)
/-    Last-commit  : 2026-08-17 08:58:46 +0530  (47a4fe4)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 08:58:46 +0530  47a4fe4  (ker07-dev)
/-        Add exact horizontal width descent of canonical information trap
/- ====================================================================== -/

import CanonicalTrapScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Horizontal width descent of the canonical two-boundary trap

The canonical last-gate trap stores one shared information integer in two
radix-four readings:

    D + 4*Z = W + 4^N*C,

with `D<4`, `W<4^N`, and latent child seed `C in {2,3}`.

Because the high term is divisible by four, the low base-four digit of W is
forced to be D.  Removing that digit peels one physical x4 column from the
trap and absorbs the latent child carry into the next horizontal tail.

This file proves only the exact arithmetic descent.  It does NOT assert that
parent/child badness automatically survives the width peel.
-/

/-- Low-digit extraction from the shared trap word. -/
theorem gst_trap_low_digit_exactS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    W % 4 = D := by
  have h4pow : 4 ∣ 4^N := by
    exact Nat.dvd_pow_self 4 (by omega)
  have hhigh : (4^N*C) % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left h4pow C)
  have hleft : (D + 4*Z) % 4 = D := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hD]
  have hright : (W + 4^N*C) % 4 = W % 4 := by
    rw [Nat.add_mod, hhigh, Nat.add_zero, Nat.mod_mod]
  rw [hEq] at hleft
  rw [hright] at hleft
  exact hleft.symm

/-- Therefore W has the exact form D+4*w. -/
theorem gst_trap_high_remainder_splitS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    W = D + 4*(W/4) := by
  have hmod := gst_trap_low_digit_exactS N D Z W C hN hD hEq
  have hsplit : W = 4*(W/4) + W%4 :=
    (Nat.div_add_mod W 4).symm
  rw [hmod] at hsplit
  omega

/-- Removing the common low digit gives one-column horizontal descent of Z. -/
theorem gst_trap_width_peel_quotientS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    Z = W/4 + 4^(N-1)*C := by
  have hW := gst_trap_high_remainder_splitS N D Z W C hN hD hEq
  have hpow : 4^N = 4 * 4^(N-1) := by
    have hidx : N = (N-1)+1 := by omega
    rw [hidx, Nat.pow_succ]
    ac_rfl
  rw [hW, hpow] at hEq
  omega

/-- The full trapped parent tail after the cut can therefore be rewritten with
one fewer horizontal x4 column.  The removed column is absorbed into the
latent next-column tail `C+4Y`. -/
theorem gst_trap_width_peel_tailS
    (N D Z W C Y : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    Z + 4^N*Y =
      W/4 + 4^(N-1) * (C + 4*Y) := by
  rw [gst_trap_width_peel_quotientS N D Z W C hN hD hEq]
  have hpow : 4^N = 4^(N-1) * 4 := by
    have hidx : N = (N-1)+1 := by omega
    rw [hidx, Nat.pow_succ]
  rw [hpow]
  ring

/-- If W was strictly inside the old width-4^N interval, its peeled remainder
is strictly inside the new width-4^(N-1) interval. -/
theorem gst_trap_width_peel_remainder_boundS
    (N W : Nat)
    (hN : 1 ≤ N)
    (hW : W < 4^N) :
    W/4 < 4^(N-1) := by
  have hpow : 4^N = 4^(N-1) * 4 := by
    have hidx : N = (N-1)+1 := by omega
    rw [hidx, Nat.pow_succ]
  rw [hpow] at hW
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2 (by
    simpa [Nat.mul_comm] using hW)

/-- Packaged one-step arithmetic width descent. -/
theorem gst_trap_width_peel_packageS
    (N D Z W C Y : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hW : W < 4^N)
    (hEq : D + 4*Z = W + 4^N*C) :
    let w := W/4
    let X := C + 4*Y
    w < 4^(N-1) ∧
      Z = w + 4^(N-1)*C ∧
      Z + 4^N*Y = w + 4^(N-1)*X := by
  dsimp only
  exact ⟨gst_trap_width_peel_remainder_boundS N W hN hW,
    gst_trap_width_peel_quotientS N D Z W C hN hD hEq,
    gst_trap_width_peel_tailS N D Z W C Y hN hD hEq⟩
