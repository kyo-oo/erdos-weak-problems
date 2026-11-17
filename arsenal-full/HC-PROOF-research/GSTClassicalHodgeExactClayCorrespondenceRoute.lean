import GSTClassicalHodgeExactClayStatement
import GSTClassicalHodgeClosedCorrespondenceGhostExtinction
import GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives

/-!
# GST CLASSICAL HODGE — EXACT CLAY TARGET VIA GENUINE CORRESPONDENCE REACHABILITY

The low-level transfer files establish what a genuine algebraic
correspondence does on rational Betti cohomology.  The Hodge conjecture asks a
different question: is every rational `(p,p)` class algebraic?

The repo's non-circular bridge between those questions is the microscopic
reachability condition `ClosedCorrespondenceHitsSheet`: every Hodge basis sheet
must be reached, up to a nonzero rational scalar, from one genuine algebraic
point class by a finite rational word of genuinely realized closed
correspondences.

This file makes that remaining Hodge-specific burden explicit and proves that
it yields the literal Clay-style finite rational combination statement.
No reachability theorem is smuggled in here: the proposition is named and left
visible until geometry proves it.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeExactClayCorrespondenceRoute

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeClosedCorrespondenceGhostExtinction
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable (H : HodgeBigradedBettiData V)

/-- The precise remaining geometry statement for the closed-correspondence
route: every rational Hodge basis sheet is genuinely reachable from an
algebraic point class by a realized closed-correspondence word. -/
def UniversalClosedCorrespondenceSheetReachability : Prop :=
  ∀ p : Nat,
  ∀ j : ClassicalHodgeBasisIndex V H p,
    ClosedCorrespondenceHitsSheet (V := V) (H := H) j

/-- Universal genuine sheet reachability implies the exact Stage-2G Hodge
conjecture. -/
theorem stage2G_of_universalClosedCorrespondenceSheetReachability
    (hReach : UniversalClosedCorrespondenceSheetReachability H) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_closedCorrespondenceHits
    V H (fun p j => hReach p j)

/-- **EXACT CLAY-STYLE LANDING.**
Universal genuine correspondence reachability implies literally:
every rational Hodge class is the class of a rational algebraic cycle. -/
theorem everyHodgeClassIsRationalAlgebraic_of_reachability
    (hReach : UniversalClosedCorrespondenceSheetReachability H) :
    EveryHodgeClassIsRationalAlgebraic H := by
  exact
    (exact_rational_hodge_conjecture_normal_form H).mp
      (stage2G_of_universalClosedCorrespondenceSheetReachability H hReach)

/-- Same landing in the wording from the problem statement: every Hodge class
is a FINITE rational linear combination of algebraic cycle classes. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_reachability
    (hReach : UniversalClosedCorrespondenceSheetReachability H) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact
    (exact_rational_hodge_conjecture_finite_sum H).mp
      (stage2G_of_universalClosedCorrespondenceSheetReachability H hReach)

/-- Contrapositive audit.  If the exact rational Hodge conjecture fails for
this carrier, then universal genuine correspondence reachability must fail.
This prevents the reachability premise from being silently weaker than the
actual obstruction. -/
theorem failure_forces_correspondence_reachability_failure
    (hFail : ¬ EveryHodgeClassIsRationalAlgebraic H) :
    ¬ UniversalClosedCorrespondenceSheetReachability H := by
  intro hReach
  exact hFail
    (everyHodgeClassIsRationalAlgebraic_of_reachability H hReach)

/-- Finite-sum failure gives the same geometric obstruction. -/
theorem finiteSum_failure_forces_reachability_failure
    (hFail : ¬ EveryHodgeClassIsFiniteRationalCombination H) :
    ¬ UniversalClosedCorrespondenceSheetReachability H := by
  intro hReach
  exact hFail
    (everyHodgeClassIsFiniteRationalCombination_of_reachability H hReach)

#check UniversalClosedCorrespondenceSheetReachability
#check stage2G_of_universalClosedCorrespondenceSheetReachability
#check everyHodgeClassIsRationalAlgebraic_of_reachability
#check everyHodgeClassIsFiniteRationalCombination_of_reachability
#check failure_forces_correspondence_reachability_failure

#print axioms everyHodgeClassIsRationalAlgebraic_of_reachability
#print axioms everyHodgeClassIsFiniteRationalCombination_of_reachability
#print axioms failure_forces_correspondence_reachability_failure

end GSTClassicalHodgeExactClayCorrespondenceRoute
