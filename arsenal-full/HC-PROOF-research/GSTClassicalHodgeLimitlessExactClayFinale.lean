import GSTClassicalHodgeFullLimitlessCrown
import GSTClassicalHodgeExactClayStatement
open GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — LIMITLESS EXACT CLAY FINALE

This file is the literal terminal landing of the upgraded limitless GST route.
It does not introduce a new Hodge surrogate.  It composes the already-built
native/cosmic/projective machinery with the exact rational Hodge statement:

* `NativeMassCycleClassBridge` manufactures live spine-mass survival;
* `FullProjectiveCosmicExternalization` realizes the limitless cosmic
  read/write algebra through genuine projective correspondence operators;
* `GSTClassicalHodgeFullLimitlessCrown.bigradedBettiHodge_of_liveMassSurvival`
  closes the genuine Stage-2G rational `(p,p)` range statement;
* `GSTClassicalHodgeExactClayStatement` converts that statement literally into
  an algebraic cycle and, equivalently, a finite rational combination of
  irreducible codimension-p cycle classes.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessExactClayFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeFullLimitlessCrown
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **LIMITLESS EXACT RATIONAL HODGE FINALE.**
The upgraded native-mass spine and full projective/cosmic externalization land
in the literal statement that every rational `(p,p)` class is the class of an
actual rational codimension-p algebraic cycle. -/
theorem everyHodgeClassIsRationalAlgebraic_of_fullLimitless
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : FullProjectiveCosmicExternalization G) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).2
  exact bigradedBettiHodge_of_liveMassSurvival G
    (liveSpineMassSurvival_of_nativeMassBridge G M) R

/-- The same finale in the exact wording requested by the classical rational
Hodge conjecture: every rational Hodge class is a finite rational linear
combination of classes of genuine codimension-p irreducible algebraic cycles. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_fullLimitless
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : FullProjectiveCosmicExternalization G) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  apply (rationalAlgebraic_iff_finiteRationalCombination H).1
  exact everyHodgeClassIsRationalAlgebraic_of_fullLimitless G M R

/-- Elementwise terminal form.  This exposes the produced native cycle without
leaving the result behind an intermediate Stage-2G proposition. -/
theorem hodgeClass_has_nativeCycle_of_fullLimitless
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact everyHodgeClassIsRationalAlgebraic_of_fullLimitless G M R
    p alpha halpha

/-- Fully expanded finite-sum terminal form for one Hodge class. -/
theorem hodgeClass_has_finiteRationalCombination_of_fullLimitless
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ phi : FiniteCodimensionPresentation V.X p,
      phi.sum (fun x q =>
        q • H.cycleClass p (codimensionPointCycle V.X p x)) = alpha := by
  exact everyHodgeClassIsFiniteRationalCombination_of_fullLimitless G M R
    p alpha halpha

#check everyHodgeClassIsRationalAlgebraic_of_fullLimitless
#check everyHodgeClassIsFiniteRationalCombination_of_fullLimitless
#check hodgeClass_has_nativeCycle_of_fullLimitless
#check hodgeClass_has_finiteRationalCombination_of_fullLimitless

#print axioms everyHodgeClassIsRationalAlgebraic_of_fullLimitless
#print axioms everyHodgeClassIsFiniteRationalCombination_of_fullLimitless
#print axioms hodgeClass_has_nativeCycle_of_fullLimitless
#print axioms hodgeClass_has_finiteRationalCombination_of_fullLimitless

end GSTClassicalHodgeLimitlessExactClayFinale
