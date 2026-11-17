import GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
import GSTClassicalHodgeNativeCycleCorrespondenceGhostAttack

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT CORRESPONDENCE GHOST STRIKE

This file fuses the two strongest geometry-first arteries now available:

1. nonzero genuine principal-cut action on one point atom produces an explicit
   nonzero native algebraic Hodge seed in the next codimension, directly
   from the spine commuting square, with no degree-semantics premise;
2. a single genuine realized correspondence word carrying ANY native source
   cycle to a nonzero multiple of a target Hodge basis sheet destroys the
   separator at that sheet.

After this fusion the target is microscopic.  For the explicit principal-cut
cycle `Seed.cycle`, construct one realized correspondence word `W` and one
nonzero rational scalar `c` such that

  W(cl(Seed.cycle)) = c * basis_j.

No global matrix-unit descent, no all-vector operator identity, and no point
source restriction occurs here.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutCorrespondenceGhostStrike

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
open GSTClassicalHodgeNativeCycleCorrespondenceGhostAttack
open GSTClassicalHodgeSingleSheetCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The explicit naturality-certified principal-cut source used by the final ghost
attack. -/
noncomputable def principalCutGhostSource
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) :=
  nativeHodgeSeed_of_principalCut_point_nonzero G p x hCoh

/-- **ONE SOURCE-SPECIFIC CORRESPONDENCE WORD KILLS THE TARGET GHOST.**
The source is not supplied abstractly: it is the actual
principal-cut cycle manufactured by the geometry. -/
theorem nativeCycleHit_of_principalCut_word
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (W : RealizedCorrespondenceWord V H (p + 1))
    (c : ℚ)
    (hc : c ≠ 0)
    (hWord :
      (realizedWordPair W).cohomologyOperator
          (principalCutGhostSource G p x hCoh).hodge.1 =
        c • (classicalHodgeBasis V H (p + 1) j).1) :
    NativeCycleCorrespondenceHitsSheet (V := V) (H := H) j := by
  let S := principalCutGhostSource G p x hCoh
  refine ⟨S.cycle, W, c, hc, ?_⟩
  rw [S.class_eq]
  exact hWord

/-- Consequently the target basis separator is empty as soon as one genuine
word realizes the required source action. -/
theorem isEmpty_separator_of_principalCut_word
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (W : RealizedCorrespondenceWord V H (p + 1))
    (c : ℚ)
    (hc : c ≠ 0)
    (hWord :
      (realizedWordPair W).cohomologyOperator
          (principalCutGhostSource G p x hCoh).hodge.1 =
        c • (classicalHodgeBasis V H (p + 1) j).1) :
    IsEmpty (BasisAtomicSeparator V H (p + 1) j) := by
  exact isEmpty_basisAtomicSeparator_of_nativeCycleCorrespondenceHit j
    (nativeCycleHit_of_principalCut_word G p x hCoh j W c hc hWord)

/-- Contrapositive form used while attacking a surviving ghost: if a separator
exists at j, then NO realized correspondence word can carry the explicit
principal-cut source to a nonzero multiple of j. -/
theorem separator_forbids_principalCut_word
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0)
    (j : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) j)
    (W : RealizedCorrespondenceWord V H (p + 1))
    (c : ℚ)
    (hc : c ≠ 0) :
    (realizedWordPair W).cohomologyOperator
          (principalCutGhostSource G p x hCoh).hodge.1 ≠
        c • (classicalHodgeBasis V H (p + 1) j).1 := by
  intro hWord
  have hEmpty :=
    isEmpty_separator_of_principalCut_word G p x hCoh j W c hc hWord
  exact hEmpty.false S

#check principalCutGhostSource
#check nativeCycleHit_of_principalCut_word
#check isEmpty_separator_of_principalCut_word
#check separator_forbids_principalCut_word

#print axioms nativeCycleHit_of_principalCut_word
#print axioms isEmpty_separator_of_principalCut_word
#print axioms separator_forbids_principalCut_word

end GSTClassicalHodgePrincipalCutCorrespondenceGhostStrike
