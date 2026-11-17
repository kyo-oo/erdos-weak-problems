import GSTClassicalHodgeSuccessorGroundFloor
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeLocalSeedBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — GROUND-FLOOR SIEGE PROPAGATION

The successor ground-floor theorem discharges the exact-stratum hypothesis at
codimension zero.  This module pushes that theorem through the actual Hodge
machinery instead of leaving it as an isolated order-theoretic receipt.

For a projectively live codimension-zero source on an irreducible carrier:

* the canonical separator successor has ambient coheight exactly one;
* projective-degree trace semantics therefore detects its genuine Betti class
  as nonzero;
* the successor becomes an actual nonzero native Hodge orbit seed in weight one;
* the positive-weight local-seed packet for a minimal weight-one ghost no
  longer stores any independent successor-exactness hypothesis;
* consequently the existing bare two-slot L² extinction theorem kills every
  minimal weight-one ghost as soon as its already isolated native point-lift
  condition is supplied.

No Hodge-surjectivity, no ghost extinction, no branch-packet realization law,
and no global catenarity statement is used here.  The point of this layer is
precisely to remove one previously external geometric premise from a live
downstream proof route.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGroundFloorSiegePropagation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeSuccessorGroundFloor
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **CANONICAL GROUND SUCCESSOR IS EXACT.**

This is the exact `hExact` shape consumed by the projective-degree and
positive-weight seed layers, now obtained from the proved ground-floor
coheight theorem rather than accepted as a premise.
-/
theorem separatorSuccessorAmbientExact_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = 0 + 1 := by
  exact
    relativeSuccessorAmbientExact_of_coheight_zero V x
      (relativeHeightOneSeparatorSuccessor V x.1 hlive)
      (relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive)

/-- The same exactness in its simplified numerical form. -/
theorem separatorSuccessorAmbientCoheight_one_of_ground
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = 1 := by
  simpa using separatorSuccessorAmbientExact_of_ground
    (V := V) x hlive

/-- **GROUND SUCCESSOR HAS NONZERO GENUINE BETTI CLASS.**

Projective-degree positivity now applies to the canonical bottom successor
without an externally supplied exact-stratum hypothesis.
-/
theorem groundSeparatorSuccessor_cycleClass_ne_zero
    [IrreducibleSpace V.X]
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    H.cycleClass 1
      (successorNativeOperator V 0
        (codimensionPointCycle V.X 0 x)) ≠ 0 := by
  simpa using
    D.separator_successor_cycleClass_ne_zero
      0 x hlive
      (separatorSuccessorAmbientExact_of_ground (V := V) x hlive)

/-- **ACTUAL WEIGHT-ONE NATIVE HODGE SEED.**

The geometry-built successor of a live ground point is promoted all the way to
the synchronized nonzero algebraic Hodge seed used by the omniversal orbit
machinery.  The former `hExact` argument has disappeared.
-/
noncomputable def groundWeightOneNativeHodgeSeed
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := 1) := by
  simpa using
    D.separator_successor_nativeHodgeSeed
      G 0 x hlive
      (separatorSuccessorAmbientExact_of_ground (V := V) x hlive)

/-- The ground-floor construction also closes the entire weight-one Hodge
fiber once the already isolated geometry-first two-generator realizations are
available.  Again, there is no successor-exactness premise.
-/
theorem hodge_weight_one_of_groundSeparator
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (R : ∀ j : ClassicalHodgeBasisIndex V H 1,
      GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
        (V := V) (H := H)
        (groundWeightOneNativeHodgeSeed G D x hlive).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading 1) ≤
      LinearMap.range (H.cycleClass 1) := by
  simpa using
    D.hodge_weight_of_separator_successor
      G 0 x hlive
      (separatorSuccessorAmbientExact_of_ground (V := V) x hlive)
      R

/-- **WEIGHT-ONE POSITIVE-SEED PACKET WITH EXACTNESS DISCHARGED.**

For a minimal ghost already known to lie in weight one, the ground-floor
theorem constructs the exact positive-weight packet expected by the local-seed
extinction layer.  No `successor_exact` witness is accepted from the caller.
-/
noncomputable def weightOnePositiveWeightSeparatorSeed
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 1)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    PositiveWeightSeparatorSeed G M where
  prevWeight := 0
  weight_eq := by simpa using hM
  sourcePoint := x
  source_live := hlive
  successor_exact := by
    simpa using separatorSuccessorAmbientExact_of_ground
      (V := V) x hlive
  degreeTrace := D

/-- The corresponding minimal-ghost local seed, with the exact-stratum input
fully internalized by the ground-floor construction. -/
noncomputable def weightOneLocalSeed
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 1)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    MinimalGhostLocalSeed G M :=
  (weightOnePositiveWeightSeparatorSeed G D M hM x hlive).localSeed G M

/-- **MINIMAL WEIGHT-ONE GHOST EXTINCTION, WITH L1 GROUND FLOOR REMOVED.**

The only remaining fixed-weight input is the native point-lift realization of
the bare GST `L²` operator already isolated by the local-seed theorem.  The
successor exactness needed to manufacture the nonzero algebraic source is now
a theorem.
-/
theorem minimalGhost_false_of_weightOne_groundSiege
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 1)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hL : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz
        (weightOneLocalSeed G D M hM x hlive).sourceIndex M.sheet)) :
    False :=
  minimalGhost_false_of_localSeed_bareLefschetz
    G M (weightOneLocalSeed G D M hM x hlive) hL

#check separatorSuccessorAmbientExact_of_ground
#check separatorSuccessorAmbientCoheight_one_of_ground
#check groundSeparatorSuccessor_cycleClass_ne_zero
#check groundWeightOneNativeHodgeSeed
#check hodge_weight_one_of_groundSeparator
#check weightOnePositiveWeightSeparatorSeed
#check weightOneLocalSeed
#check minimalGhost_false_of_weightOne_groundSiege

#print axioms separatorSuccessorAmbientExact_of_ground
#print axioms groundSeparatorSuccessor_cycleClass_ne_zero
#print axioms groundWeightOneNativeHodgeSeed
#print axioms hodge_weight_one_of_groundSeparator
#print axioms weightOnePositiveWeightSeparatorSeed
#print axioms minimalGhost_false_of_weightOne_groundSiege

end GSTClassicalHodgeGroundFloorSiegePropagation
