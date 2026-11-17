import GSTClassicalHodgeClosedCorrespondenceFailurePacket
import GSTClassicalHodgeCanonicalCosmicRealizationEquivalence

/-!
# GST CLASSICAL HODGE — CLOSED CORRESPONDENCES REALIZE THE LIMITLESS COSMIC ACTION

The realized closed-correspondence algebra and the canonical limitless cosmic
matrix-unit formalism now meet exactly.

Suppose one finite rational word W of genuine realized closed correspondences
acts on the genuine rational `(p,p)` Hodge fiber as the rank-free matrix unit
`E_ij`.  The geometric cycle-class spine independently proves that EVERY
native codimension-p algebraic cycle class already has Hodge type `(p,p)`.
Therefore W and the canonical cosmic ambient matrix unit agree on the class of
every native cycle, not merely on a chosen Hodge test vector.

Since W already has an exact native/cohomology commuting square, its native
cycle operator is a genuine `NativeCanonicalCosmicRealization`.

This is the desired architecture:

    actual closed X×X correspondences
          -> exact native cycle operator
          -> exact cycle-class square
          -> rank-free Hodge E_ij on the Hodge fiber
          -> canonical limitless cosmic E_ij on ALL algebraic cycle classes.

No range-lift section and no multiplicity-only descent is used.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeClosedCorrespondenceCosmicRealization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A realized closed-correspondence word whose Hodge action is E_ij gives a
full native realization of the canonical limitless cosmic matrix unit. -/
noncomputable def nativeCanonicalCosmicRealization_of_closedCorrespondenceReachability
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (hReach : MatrixUnitReachableByClosedCorrespondences
      (V := V) (H := H) i j) :
    NativeCanonicalCosmicRealization (V := V) (H := H) i j := by
  let W : RealizedCorrespondenceWord V H p := Classical.choose hReach
  have hW : ∀ alpha : ClassicalHodgeFiber V H p,
      (realizedWordPair W).cohomologyOperator alpha.1 =
        (hodgeMatrixUnit i j alpha).1 :=
    Classical.choose_spec hReach
  refine {
    native := (realizedWordPair W).cycleOperator
    naturality := ?_
  }
  intro Z
  let alpha : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p Z, G.algebraic_is_hodge p Z⟩
  have hnat := (realizedWordPair W).cycleClass_cycleOperator Z
  have hmatrix := hW alpha
  have hcosmic :
      canonicalCosmicAmbient i j alpha.1 =
        (hodgeMatrixUnit i j alpha).1 := by
    unfold canonicalCosmicAmbient
    rw [GSTClassicalHodgeUniversalTwoSlotNativeClosure.extendHodgeEndomorphism_on_hodge]
  calc
    H.cycleClass p ((realizedWordPair W).cycleOperator Z) =
        (realizedWordPair W).cohomologyOperator (H.cycleClass p Z) := hnat
    _ = (hodgeMatrixUnit i j alpha).1 := by simpa [alpha] using hmatrix
    _ = canonicalCosmicAmbient i j (H.cycleClass p Z) := by
      simpa [alpha] using hcosmic.symm

/-- Family form: genuine closed-correspondence reachability of every rank-free
matrix unit constructs the complete canonical limitless native-realization
family. -/
noncomputable def allNativeCanonicalCosmicRealizations_of_closedCorrespondences
    (G : GeometricCycleClassSpine V H)
    (hReach : ∀ i j : ClassicalHodgeBasisIndex V H p,
      MatrixUnitReachableByClosedCorrespondences
        (V := V) (H := H) i j) :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      NativeCanonicalCosmicRealization (V := V) (H := H) i j :=
  fun i j =>
    nativeCanonicalCosmicRealization_of_closedCorrespondenceReachability
      G i j (hReach i j)

/-- Hence closed-correspondence reachability gives the exact canonical cosmic
naturality law consumed by the limitless no-escape crown. -/
theorem canonicalCosmicNaturality_of_closedCorrespondenceReachability
    (G : GeometricCycleClassSpine V H)
    (hReach : ∀ i j : ClassicalHodgeBasisIndex V H p,
      MatrixUnitReachableByClosedCorrespondences
        (V := V) (H := H) i j) :
    GSTClassicalHodgeCanonicalLimitlessNaturalityCrown.CanonicalCosmicNaturality
      (V := V) (H := H) p := by
  exact canonicalCosmicNaturality_of_nativeRealizations
    (allNativeCanonicalCosmicRealizations_of_closedCorrespondences G hReach)

/-- One nonzero algebraic seed plus genuine closed-correspondence reachability
therefore activates the complete limitless cosmic no-escape mechanism. -/
theorem hodgeWeight_of_closedCorrespondence_cosmicRealization
    (G : GeometricCycleClassSpine V H)
    (hseed : GSTClassicalHodgeConcreteFailureDichotomy.AlgebraicFiber
      (V := V) (H := H) (p := p) ≠ ⊥)
    (hReach : ∀ i j : ClassicalHodgeBasisIndex V H p,
      MatrixUnitReachableByClosedCorrespondences
        (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact GSTClassicalHodgeCanonicalLimitlessNaturalityCrown.hodge_weight
    hseed
    (canonicalCosmicNaturality_of_closedCorrespondenceReachability G hReach)

#check nativeCanonicalCosmicRealization_of_closedCorrespondenceReachability
#check allNativeCanonicalCosmicRealizations_of_closedCorrespondences
#check canonicalCosmicNaturality_of_closedCorrespondenceReachability
#check hodgeWeight_of_closedCorrespondence_cosmicRealization

#print axioms nativeCanonicalCosmicRealization_of_closedCorrespondenceReachability
#print axioms canonicalCosmicNaturality_of_closedCorrespondenceReachability
#print axioms hodgeWeight_of_closedCorrespondence_cosmicRealization

end GSTClassicalHodgeClosedCorrespondenceCosmicRealization
