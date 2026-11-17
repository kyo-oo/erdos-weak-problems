/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1000 / 1132
/-    Path         : branches/sol_right-chord-firepower-base/ResidualNullBranchReductionScratch.lean
/-    Ref          : origin/sol/right-chord-firepower-base
/-    First-commit : 2026-08-17 10:51:58 +0530  (b5d61f2)
/-    Last-commit  : 2026-08-17 10:52:53 +0530  (f371623)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-17 10:51:58 +0530  b5d61f2  (ker07-dev)
/-        Package locked residual NULL branch reduction
/- [02/2] 2026-08-17 10:52:53 +0530  f371623  (ker07-dev)
/-        Harden NULL branch residue proof
/- ====================================================================== -/

import OmegaUPotentialBridgeScratch
import PrefixOneOriginPhaseRecursionScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Locked residual NULL-branch reduction

This file handles only the genuine k=1 residual branch n % 3 = 1.
It does not address the CREATE branch and it does not assert final crossing.

The purpose is to package one well-founded natural-origin step without dropping
any finite offset, seed, or canonical multiplier.
-/

/-- The monolith Navigation map is a canonical origin-energy map in the scratch
interface. -/
theorem gst_navigation_constant_origin_energyS :
    GSTCanonicalOriginEnergyS gstNavigationConstant := by
  intro t n ht
  exact gst_navigation_decomposition t n ht

/-- Canonical prefix-one offset function. -/
def gstCanonicalPrefixOffsetS (t : Nat) : Nat := c t / 3

/-- The unit Navigation constant has the exact forced prefix 1+3*z_t. -/
theorem gst_navigation_constant_unit_prefixS
    (t : Nat) (ht : 1 ≤ t) :
    gstNavigationConstant t 1 = 1 + 3 * gstCanonicalPrefixOffsetS t := by
  rw [gstNavigationConstant_one t ht]
  unfold gstCanonicalPrefixOffsetS
  have hc3 : c t % 3 = 1 := c_mod3 t ht
  have hsplit := Nat.mod_add_div (c t) 3
  omega

/-- The canonical offset has stable residue two modulo three. -/
theorem gst_canonical_prefix_offset_mod3S
    (t : Nat) (ht : 1 ≤ t) :
    gstCanonicalPrefixOffsetS t % 3 = 2 := by
  unfold gstCanonicalPrefixOffsetS
  have hc9 : c t % 9 = 7 := c_mod9 t ht
  have hc3 : c t % 3 = 1 := c_mod3 t ht
  have hsplit :
      c t % 9 = c t % 3 + 3 * (c t / 3 % 3) := by
    rw [show (9:Nat) = 3 * 3 by decide, Nat.mod_mul]
  rw [hc9, hc3] at hsplit
  omega

/-- The exact U/Ω phase-one tail is literally the hard-prefix-one tail used by
the origin recursion. -/
theorem gst_prefix_one_u_tail_eq_hard_tailS
    (s n : Nat) :
    gstPrefixOneUPotentialTailS s n =
      GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n := by
  rfl

/-- Exact canonical child recurrence on the NULL origin branch n=3u+1. -/
theorem gst_residual_null_child_recurrenceS
    (s n : Nat) (hs : 1 ≤ s) (hn1 : n % 3 = 1) :
    let u := n / 3
    gstNavigationConstant (s+1) n =
      gstNavigationConstant (s+1) 1 +
        3 * 4^(3^(s+1)) * gstNavigationConstant (s+2) u := by
  dsimp only
  have hn : n = 1 + 3*(n/3) := by
    have h := Nat.mod_add_div n 3
    omega
  have hrec := gst_canonical_prefix_recurrenceS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    (s+1) 1 1 (n/3) (by omega)
  norm_num at hrec
  rw [← hn] at hrec
  simpa [Nat.mul_assoc] using hrec

/-- One exact residual NULL step.  A hypothetical complete phase-one bad trace
regenerates with seed 0 on the full finite outer offset, the natural origin
strictly decreases, and the handwritten U-potential jump of the consumed row
is exactly zero.

Nothing is identified with a terminal NULL state: this is one ordinary
regeneration edge. -/
theorem gst_residual_null_branch_reductionS
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn1 : n % 3 = 1)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let u := n / 3
    let A := GSTCanonicalBlockS s
    let z := gstCanonicalPrefixOffsetS s
    let Hnext := GSTHardPrefixOneTailS
      gstNavigationConstant gstCanonicalPrefixOffsetS (s+1) u
    u < n ∧
      GSTSeededBadTraceS 0
        ((z + A) / 3 + A * Hnext) ∧
      gstHandwrittenUJumpS 1 0 = 0 := by
  dsimp only
  have hu_lt : n / 3 < n :=
    Nat.div_lt_self (by omega) (by decide : 1 < 3)

  have hseededS : ∀ j,
      GSTBadPairS
        (gstAffineMulCarryS 4 1
          (gstPrefixOneUPotentialTailS s n) j)
        (gstDigitS (gstPrefixOneUPotentialTailS s n) j) :=
    gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad

  have hseeded : GSTSeededBadTraceS 1
      (GSTHardPrefixOneTailS
        gstNavigationConstant gstCanonicalPrefixOffsetS s n) := by
    intro j
    have hj := hseededS j
    simpa [gst_prefix_one_u_tail_eq_hard_tailS] using hj

  have hnshape : n = 3*(n/3) + 1 := by
    have h := Nat.mod_add_div n 3
    omega

  have hregen0 := gst_bad_hard_tail_origin_one_regeneratesS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    gstCanonicalPrefixOffsetS
    gst_navigation_constant_unit_prefixS
    gst_canonical_prefix_offset_mod3S
    s (n/3) hs
  have hregen : GSTSeededBadTraceS 0
      ((gstCanonicalPrefixOffsetS s + GSTCanonicalBlockS s) / 3 +
        GSTCanonicalBlockS s *
          GSTHardPrefixOneTailS
            gstNavigationConstant gstCanonicalPrefixOffsetS (s+1) (n/3)) := by
    rw [← hnshape] at hregen0
    exact hregen0 hseeded

  exact ⟨hu_lt, hregen, by decide⟩
