import GSTClassicalHodgeCorrespondenceInvariantGhost

/-!
# GST CLASSICAL HODGE — CLOSED-CORRESPONDENCE IRREDUCIBILITY BRIDGE

Genuine closed-correspondence realization of every rank-free GST matrix unit
forces irreducibility for every submodule invariant under all actual
Hodge-compatible correspondence expressions.  Thus the new invariant-ghost
route and the historical matrix-unit reachability route are the same
geometric artillery, not separate assumptions.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeClosedCorrespondenceIrreducibilityBridge

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr
open GSTClassicalHodgeCorrespondenceInvariantGhost
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- If every rank-free GST matrix unit is a genuine closed-correspondence word,
then invariance under actual correspondence expressions implies invariance
under the full rank-free GST arsenal. -/
theorem rankFreeArsenalInvariant_of_correspondenceInvariant
    (hReach : ∀ i j : ClassicalHodgeBasisIndex V H p,
      MatrixUnitReachableByClosedCorrespondences
        (V := V) (H := H) i j)
    (S : Submodule ℚ (ClassicalHodgeFiber V H p))
    (hS : CorrespondenceInvariant (V := V) (H := H) (p := p) S) :
    RankFreeArsenalInvariant S := by
  intro i j alpha halpha
  rcases hReach i j with ⟨W, hW⟩
  let E : RealizedCorrespondenceExpr V H p :=
    RealizedCorrespondenceExpr.ofWord W
  have hE : HodgeCompatible (V := V) (H := H) (p := p) E := by
    intro beta
    have hEq :
        E.cohomologyOperator beta.1 =
          (hodgeMatrixUnit i j beta).1 := by
      change E.operatorPair.cohomologyOperator beta.1 =
        (hodgeMatrixUnit i j beta).1
      dsimp [E]
      rw [RealizedCorrespondenceExpr.ofWord_operatorPair]
      exact hW beta
    rw [hEq]
    exact (hodgeMatrixUnit i j beta).2
  have hImage := hS E hE alpha halpha
  have hEq :
      hodgeOperator E hE alpha =
        hodgeMatrixUnit i j alpha := by
    apply Subtype.ext
    change E.cohomologyOperator alpha.1 =
      (hodgeMatrixUnit i j alpha).1
    change E.operatorPair.cohomologyOperator alpha.1 =
      (hodgeMatrixUnit i j alpha).1
    dsimp [E]
    rw [RealizedCorrespondenceExpr.ofWord_operatorPair]
    exact hW alpha
  rw [hEq] at hImage
  exact hImage

/-- Full realized closed-correspondence matrix-unit reachability proves
irreducibility of the genuine Hodge-compatible correspondence action. -/
theorem actualCorrespondenceIrreducible_of_closedCorrespondenceMatrixUnits
    (hReach : ∀ i j : ClassicalHodgeBasisIndex V H p,
      MatrixUnitReachableByClosedCorrespondences
        (V := V) (H := H) i j) :
    ActualCorrespondenceIrreducible (V := V) (H := H) (p := p) := by
  intro S hS hne
  exact rankFreeArsenalInvariant_eq_top S
    (rankFreeArsenalInvariant_of_correspondenceInvariant hReach S hS) hne

/-- Exact rational Hodge conjecture from the two sharp geometric obligations:
actual matrix-unit realization and the zero-fiber-or-genuine-seed condition. -/
theorem exactHodge_of_closedCorrespondenceMatrixUnits
    (hReach : ∀ q : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H q,
        MatrixUnitReachableByClosedCorrespondences
          (V := V) (H := H) i j)
    (hSeed : ∀ q : Nat,
      ZeroFiberOrAlgebraicSeed (V := V) (H := H) (p := q)) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_actualCorrespondenceIrreducible
  · intro q
    exact actualCorrespondenceIrreducible_of_closedCorrespondenceMatrixUnits
      (hReach q)
  · exact hSeed

/-- Literal finite rational-combination form. -/
theorem finiteCombination_of_closedCorrespondenceMatrixUnits
    (hReach : ∀ q : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H q,
        MatrixUnitReachableByClosedCorrespondences
          (V := V) (H := H) i j)
    (hSeed : ∀ q : Nat,
      ZeroFiberOrAlgebraicSeed (V := V) (H := H) (p := q)) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  rw [← rationalAlgebraic_iff_finiteRationalCombination]
  exact exactHodge_of_closedCorrespondenceMatrixUnits hReach hSeed

#check rankFreeArsenalInvariant_of_correspondenceInvariant
#check actualCorrespondenceIrreducible_of_closedCorrespondenceMatrixUnits
#check exactHodge_of_closedCorrespondenceMatrixUnits
#check finiteCombination_of_closedCorrespondenceMatrixUnits

#print axioms rankFreeArsenalInvariant_of_correspondenceInvariant
#print axioms actualCorrespondenceIrreducible_of_closedCorrespondenceMatrixUnits
#print axioms exactHodge_of_closedCorrespondenceMatrixUnits
#print axioms finiteCombination_of_closedCorrespondenceMatrixUnits

end GSTClassicalHodgeClosedCorrespondenceIrreducibilityBridge
