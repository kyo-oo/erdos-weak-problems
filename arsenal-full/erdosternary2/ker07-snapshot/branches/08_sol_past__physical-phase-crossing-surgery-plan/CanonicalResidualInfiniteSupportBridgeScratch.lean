/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0992 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/CanonicalResidualInfiniteSupportBridgeScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-17 10:49:36 +0530  (b2570fa)
/-    Last-commit  : 2026-08-17 10:49:36 +0530  (b2570fa)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 10:49:36 +0530  b2570fa  (ker07-dev)
/-        Lock residual infinite-support bridge interface
/- ====================================================================== -/

import OmegaUPotentialBridgeScratch
import FiniteSupportScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Locked residual-only final bridge interface

This module contains no new forcing axiom.  It packages the exact one theorem
still required by the prefix-one residual seam and proves its consumer.

The residual origin is already maximally 3-free, so only n % 3 != 0 enters
this interface.  All origin-closed and non-residual branches remain owned by
the monolith's existing strong-induction machinery.
-/

/-- Exact remaining forcing statement.  Under a certified child Navigation
witness and a complete phase-one Omega bad trace, the ordinary natural origin
would have to carry nonzero ternary information beyond every finite cutoff. -/
def GSTCanonicalResidualInfiniteSupportBridgeS : Prop :=
  ∀ s n,
    1 ≤ s →
    1 ≤ n →
    n % 3 ≠ 0 →
    GSTNavigationWitness (gstNavigationConstant (s+1) n) →
    GSTOmegaInfiniteBadTrace s 1 n →
    InfiniteTernarySupportS n

/-- Once the residual forcing statement is supplied, a complete prefix-one
Omega bad trace is impossible for an ordinary natural origin. -/
theorem gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS
    (hbridge : GSTCanonicalResidualInfiniteSupportBridgeS)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ¬ GSTOmegaInfiniteBadTrace s 1 n := by
  intro hBad
  have hinf : InfiniteTernarySupportS n :=
    hbridge s n hs hn hn3 hchild hBad
  exact finite_origin_contradictionS n hinf

/-- The same consumer with the handwritten U-potential attached explicitly.
This theorem records that any hypothetical residual bad trace simultaneously
obeys every finite U-potential bound before finite support destroys it. -/
theorem gst_residual_prefix_one_u_bad_contradiction_of_bridgeS
    (hbridge : GSTCanonicalResidualInfiniteSupportBridgeS)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have _hU : ∀ K,
      24 * (gstPrefixOneUPotentialTailS s n % 3^K) + 15 ≤
        3^K * gstHandwrittenUChargeS
          (gstAffineMulCarryS 4 1 (gstPrefixOneUPotentialTailS s n) K) :=
    fun K => gst_prefix_one_omega_bad_u_potential_boundS s n K hs hBad
  have hinf : InfiniteTernarySupportS n :=
    hbridge s n hs hn hn3 hchild hBad
  exact finite_origin_contradictionS n hinf
