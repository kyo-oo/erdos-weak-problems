import GSTClassicalHodgeGeneralSpaceOperatorCosmos
import GSTClassicalHodgeExactClayStatement

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceExactOperatorFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeNativeWordFromArbitrarySeed
open GSTClassicalHodgeGeneralSpaceRealization
open GSTClassicalHodgeGeneralSpaceOperatorCosmos
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A concrete nonzero native Hodge seed in every weight, together with genuine
geometry-first GST primitive realizations from its live source coordinate to
every target sheet, gives the exact elementwise rational Hodge statement.

This theorem does not package Hodge surjectivity.  It assembles the already
constructed native GST words and their cycle-class commuting squares. -/
theorem everyHodgeClassIsRationalAlgebraic_of_operatorCosmos
    (seed : ∀ p : Nat,
      NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p).sourceIndex j) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).2
  exact bigradedBettiHodge_of_nativeHodgeSeeds seed R

/-- **GENERAL SPACE EXACT HODGE FINALE.**
Under the concrete native-seed and geometry-first GST path constructions, every
rational Hodge class is literally a finite rational linear combination of
actual irreducible codimension-p cycle classes. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_operatorCosmos
    (seed : ∀ p : Nat,
      NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p).sourceIndex j) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  apply (rationalAlgebraic_iff_finiteRationalCombination H).1
  exact everyHodgeClassIsRationalAlgebraic_of_operatorCosmos seed R

/-- Pointwise General Space statement: every target basis point is native by
an explicit synchronized GST path from the chosen nonzero native seed. -/
theorem all_basis_points_native
    (seed : ∀ p : Nat,
      NativeHodgeSeed (V := V) (H := H) (p := p))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator
          (V := V) (H := H) (seed p).sourceIndex j) :
    ∀ p : Nat,
    ∀ j : ClassicalHodgeBasisIndex V H p,
      OperatorNativeLocus
        (⟨p, (classicalHodgeBasis V H p j).1⟩ : EvenBettiPoint V H) := by
  intro p j
  exact basis_native_of_geometryFirst (seed p) j (R p j)

#check everyHodgeClassIsRationalAlgebraic_of_operatorCosmos
#check everyHodgeClassIsFiniteRationalCombination_of_operatorCosmos
#check all_basis_points_native

#print axioms everyHodgeClassIsRationalAlgebraic_of_operatorCosmos
#print axioms everyHodgeClassIsFiniteRationalCombination_of_operatorCosmos
#print axioms all_basis_points_native

end GSTClassicalHodgeGeneralSpaceExactOperatorFinale
