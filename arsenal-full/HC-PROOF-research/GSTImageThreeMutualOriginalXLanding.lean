import GSTImageThreeOriginalXNativeLanding
import GSTImageThreeGeometricTwoSourceBirth
import Mathlib

/-!
# GST Image 3 — MUTUAL WORLD SOURCE TRANSPORT ON THE ORIGINAL X

Exact geometric counterpart of the new original native Wave-II
SURVIVE-cross-world F. Two actual ORIGINAL-X Chow-cycle channels
are coupled using the actual native cycle operator M, with the old
10-address shift. The canonical rational Betti cycle-class map
commutes with the coupled operator by the ALREADY green
CycleClassOperatorPair naturality lemmas. No Hodge surjectivity or
unrealized Chow-to-Hodge inverse is postulated.

This is the correct typed original-X landing interface for the
strong original 24-state mutual-source full-rank Wolfram certificate.
A theorem identifying a given X Hodge space with the resulting
GST quotient, and proving full Hodge orbit rank, remains necessary.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeMutualOriginalXLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTImageThreeOriginalXNativeLanding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Two ACTUAL original-X algebraic cycle channels, not symbolic
arbitrary input Hodge classes. -/
abbrev CyclePair := codimensionCycles V.X p × codimensionCycles V.X p

/-- Their canonical Betti cohomology channels. -/
abbrev BettiPair :=
  RationalSingularCohomology H.analytification (2*p) ×
  RationalSingularCohomology H.analytification (2*p)

/-- Apply the ACTUAL original-X canonical rational Betti cycleClass
to each genuine native source-world cycle independently. -/
def pairCycleClass (Z : CyclePair (V := V) (p := p)) :
    BettiPair (H := H) (p := p) :=
  (H.cycleClass p Z.1, H.cycleClass p Z.2)

/-- Original-X native navigation and source mutual-transport F.
Cross-world transport is the very SAME true native M operator.
The shift TEN is the old Wave-II channel address separation. -/
def mutualNativeF
    (U J M : CycleClassOperatorPair V H p)
    (R₀ R₁ : Nat) (Z : CyclePair (V := V) (p := p)) :
    CyclePair (V := V) (p := p) :=
  ((geometricF U J M R₀).cycleOperator Z.1 +
      M.cycleOperator Z.2,
   (geometricF U J M R₁).cycleOperator Z.2 +
      (10 : ℚ) • Z.2 + M.cycleOperator Z.1)

/-- The corresponding original-X rational Betti operator. -/
def mutualBettiF
    (U J M : CycleClassOperatorPair V H p)
    (R₀ R₁ : Nat) (alpha : BettiPair (H := H) (p := p)) :
    BettiPair (H := H) (p := p) :=
  ((geometricF U J M R₀).cohomologyOperator alpha.1 +
      M.cohomologyOperator alpha.2,
   (geometricF U J M R₁).cohomologyOperator alpha.2 +
      (10 : ℚ) • alpha.2 + M.cohomologyOperator alpha.1)

/-- THE EXACT GEOMETRIC MUTUAL-SOURCE SQUARE.

For EVERY genuine original-X native algebraic input cycle pair,
the actual rational Betti class of the born pair equals the action
of the corresponding native F on its canonical Betti classes.
No cycles representing unknown Hodge classes are presumed. -/
theorem mutual_originalX_cycleClass_square
    (U J M : CycleClassOperatorPair V H p)
    (R₀ R₁ : Nat) (Z : CyclePair (V := V) (p := p)) :
    pairCycleClass (mutualNativeF U J M R₀ R₁ Z) =
      mutualBettiF U J M R₀ R₁ (pairCycleClass Z) := by
  apply Prod.ext
  · change
      H.cycleClass p
        ((geometricF U J M R₀).cycleOperator Z.1 +
          M.cycleOperator Z.2) =
      (geometricF U J M R₀).cohomologyOperator
        (H.cycleClass p Z.1) +
          M.cohomologyOperator (H.cycleClass p Z.2)
    rw [map_add,
      (geometricF U J M R₀).cycleClass_cycleOperator,
      M.cycleClass_cycleOperator]
  · change
      H.cycleClass p
        ((geometricF U J M R₁).cycleOperator Z.2 +
          (10 : ℚ) • Z.2 + M.cycleOperator Z.1) =
      (geometricF U J M R₁).cohomologyOperator
        (H.cycleClass p Z.2) +
          (10 : ℚ) • H.cycleClass p Z.2 +
          M.cohomologyOperator (H.cycleClass p Z.1)
    rw [map_add, map_add, map_smul,
      (geometricF U J M R₁).cycleClass_cycleOperator,
      M.cycleClass_cycleOperator]

#check pairCycleClass
#check mutualNativeF
#check mutualBettiF
#check mutual_originalX_cycleClass_square
#print axioms mutual_originalX_cycleClass_square

end GSTImageThreeMutualOriginalXLanding
