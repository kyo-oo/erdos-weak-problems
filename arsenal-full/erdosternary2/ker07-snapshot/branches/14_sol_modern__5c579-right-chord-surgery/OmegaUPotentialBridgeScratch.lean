/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0983 / 1132
/-    Path         : branches/sol_5c579-right-chord-surgery/OmegaUPotentialBridgeScratch.lean
/-    Ref          : origin/sol/5c579-right-chord-surgery
/-    First-commit : 2026-08-17 10:39:29 +0530  (8ef2ea1)
/-    Last-commit  : 2026-08-17 10:39:29 +0530  (8ef2ea1)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 10:39:29 +0530  8ef2ea1  (ker07-dev)
/-        Bridge prefix-one Omega bad trace to U-potential
/- ====================================================================== -/

import ErdosTernary2
import HandwrittenUniversalParadoxPotentialScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Atomic bridge: monolith Ω∞ bad trace -> handwritten U-potential

This file is deliberately narrow.  It does not prove prefix-one crossing and
it does not activate the quarantined residual Ω termination block.

For k=1 and s>=1, the exact Ω∞ parent seed is

  (4 * (c s % 3)) / 3 = 1,

so the monolith's `GSTOmegaInfiniteBadTrace s 1 n` is the same seed-one bad
language consumed by `HandwrittenUniversalParadoxPotentialScratch`.
-/

/-- The exact prefix-one affine tail used simultaneously by Ω∞ and the
U-potential scratch. -/
def gstPrefixOneUPotentialTailS (s n : Nat) : Nat :=
  c s / 3 + 4^(3^s) * gstNavigationConstant (s+1) n

/-- A complete prefix-one Ω∞ bad trace is exactly a complete seed-one bad
trace on the same affine tail, expressed in the independent scratch
coordinates. -/
theorem gst_prefix_one_omega_bad_to_u_seeded_badS
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∀ j,
      GSTBadPairS
        (gstAffineMulCarryS 4 1 (gstPrefixOneUPotentialTailS s n) j)
        (gstDigitS (gstPrefixOneUPotentialTailS s n) j) := by
  intro j hGate
  have hNe := hBad j
  change GSTOmegaGatePolynomial (gstOmega s 1 n j) ≠ 0 at hNe
  apply hNe
  apply (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n j)).2
  have hc3 : c s % 3 = 1 := c_mod3 s hs
  simpa [gstPrefixOneUPotentialTailS, gstOmega, gstDigitS,
    gstAffineMulCarryS, Nat.pow_one, hc3] using hGate

/-- The monolith Ω∞ bad hypothesis therefore inherits the exact finite
U-potential telescope at every information depth K. -/
theorem gst_prefix_one_omega_bad_u_potential_boundS
    (s n K : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    24 * (gstPrefixOneUPotentialTailS s n % 3^K) + 15 ≤
      3^K * gstHandwrittenUChargeS
        (gstAffineMulCarryS 4 1 (gstPrefixOneUPotentialTailS s n) K) := by
  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  simpa [gstHandwrittenUChargeS] using
    gst_bad_prefix_u_potential_boundS
      1 (gstPrefixOneUPotentialTailS s n) K (by decide)
      (fun j hj => hseeded j)

/-- Once the exact seed-one output has emptied at a finite ternary height K,
the Ω∞ bad hypothesis satisfies the sharp terminal U-bound. -/
theorem gst_prefix_one_omega_bad_u_terminal_boundS
    (s n K : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hempty : 1 + 4 * gstPrefixOneUPotentialTailS s n < 3^K) :
    24 * gstPrefixOneUPotentialTailS s n + 15 ≤ 5 * 3^K := by
  exact gst_seed_one_complete_bad_u_boundS
    (gstPrefixOneUPotentialTailS s n) K
    (gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad)
    hempty
