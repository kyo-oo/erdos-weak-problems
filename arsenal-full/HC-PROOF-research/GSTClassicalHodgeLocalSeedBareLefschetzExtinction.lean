import GSTClassicalHodgeTwoSlotLefschetzCollapse
import GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeAtomicAnnihilator
import GSTClassicalHodgeSuccessorSeedEscapeDichotomy
import GSTClassicalHodgeProjectiveDegreeTrace

/-!
# GST CLASSICAL HODGE — LOCAL-SEED BARE-LEFSCHETZ EXTINCTION

The least-weight separator reduction and the two-slot GST collapse together
leave a much smaller classical landing problem than the earlier all-pairs
matrix-unit externalization.

For a hypothetical minimal primitive ghost M it is enough to have:

* one genuine algebraic Hodge source `a` in the same weight;
* one live Hodge coordinate i of `a`;
* native point lifts for the ambient two-slot GST `L^2` primitive from i to
  the detected ghost sheet.

The two-slot cosmology proves that bare `L^2` is already a fixed nonzero scalar
multiple of the matrix unit E_{i,M.sheet}.  Hence it sends `a` to a nonzero
multiple of the very basis sheet detected by the ghost.  Native point lifts
force the same image to stay in the actual atomic algebraic span, which the
ghost annihilates.  Contradiction.

This module then connects the positive-weight source directly to the new
separator-successor geometry: a single exact separator successor together with
the projective degree/Betti trace semantics gives the required nonzero
algebraic source.  No conserved all-weight mass law and no uniform successor
cardinality are required.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLocalSeedBareLefschetzExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeProjectiveDegreeTrace

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Exact Hodge-fiber action of bare two-slot GST `L^2`: read one coordinate
and write it into the target basis sheet with the fixed nonzero world scalar. -/
theorem ambientTwoStepLefschetz_on_hodge_coordinate
    {p : Nat}
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientTwoStepLefschetz i j alpha.1 =
      ((forwardScalar sourceSlot targetSlot : ℚ) * hodgeCoordinate i alpha) •
        (classicalHodgeBasis V H p j).1 := by
  rw [ambientTwoStepLefschetz]
  rw [extendHodgeEndomorphism_on_hodge]
  have h := lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
    (V := V) (H := H) (p := p) i j
  have hfun := LinearMap.congr_fun h alpha
  have hsub := congrArg Subtype.val hfun
  simpa [hodgeMatrixUnit_apply, smul_smul] using hsub

/-- Minimal local source packet required by the one-middle-motion argument. -/
structure MinimalGhostLocalSeed
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  source : ClassicalHodgeFiber V H M.weight
  source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight
  sourceIndex : ClassicalHodgeBasisIndex V H M.weight
  sourceCoefficient_ne_zero : hodgeCoordinate sourceIndex source ≠ 0

/-- Any ambient operator with genuine native point lifts preserves the actual
atomic algebraic span. -/
theorem atomicStable_of_nativePointLifts
    {p : Nat}
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hT : HasNativePointLifts (p := p) (cl := H.cycleClass p) T) :
    AtomicSpanStable (p := p) (cl := H.cycleClass p) T :=
  (smoothProjective_atomicStable_iff_nativePointLifts
    (V := V) (H := H) (p := p) T).2 hT

/-- **ONE BARE GST L² MOTION KILLS THE MINIMAL GHOST.** -/
theorem minimalGhost_false_of_localSeed_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (hL : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz S.sourceIndex M.sheet)) : False := by
  have hstable : AtomicSpanStable
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz S.sourceIndex M.sheet) :=
    atomicStable_of_nativePointLifts
      (ambientTwoStepLefschetz S.sourceIndex M.sheet) hL
  have himage :
      ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) :=
    hstable S.source.1 S.source_algebraic
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  have hzero := hker himage
  rw [ambientTwoStepLefschetz_on_hodge_coordinate] at hzero
  have hscalar :
      (forwardScalar sourceSlot targetSlot : ℚ) *
          hodgeCoordinate S.sourceIndex S.source ≠ 0 :=
    mul_ne_zero twoSlot_forwardScalar_ne_zero S.sourceCoefficient_ne_zero
  exact (smul_ne_zero hscalar M.separator.detects_basis) hzero

/-- Every nonzero algebraic Hodge source contains at least one live coordinate
and hence canonically produces a local seed packet. -/
noncomputable def localSeedOfNonzeroAlgebraic
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (a : ClassicalHodgeFiber V H M.weight)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H M.weight)
    (ha0 : a ≠ 0) : MinimalGhostLocalSeed G M := by
  let i := Classical.choose (exists_nonzero_hodgeCoordinate ha0)
  have hi : hodgeCoordinate i a ≠ 0 :=
    Classical.choose_spec (exists_nonzero_hodgeCoordinate ha0)
  exact {
    source := a
    source_algebraic := haAlg
    sourceIndex := i
    sourceCoefficient_ne_zero := hi
  }

/-- Positive-weight geometric packet: the minimal bad weight is the successor
of a genuine codimension-p source point whose canonical separator successor is
in exact ambient codimension and whose Betti class is certified by projective
degree trace semantics. -/
structure PositiveWeightSeparatorSeed
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  prevWeight : Nat
  weight_eq : M.weight = prevWeight + 1
  sourcePoint : CodimensionPoint V.X prevWeight
  source_live : ProjectivelyLiveSource V.projective.n
    (V.projective.immersion sourcePoint.1)
  successor_exact :
    Order.coheight
      (ambientSuccessorPoint V sourcePoint.1
        (relativeHeightOneSeparatorSuccessor V sourcePoint.1 source_live)) =
      prevWeight + 1
  degreeTrace : ProjectiveDegreeTraceSemantics V H

/-- The separator-successor packet constructs an actual nonzero algebraic Hodge
source in the minimal ghost weight. -/
noncomputable def PositiveWeightSeparatorSeed.localSeed
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (P : PositiveWeightSeparatorSeed G M) :
    MinimalGhostLocalSeed G M := by
  let S0 : NativeHodgeOrbitSeed (V := V) (H := H) (p := P.prevWeight + 1) :=
    P.degreeTrace.separator_successor_nativeHodgeSeed
      G P.prevWeight P.sourcePoint P.source_live P.successor_exact
  have hAlg0 : S0.hodge ∈ AlgebraicHodgeSubspace V H (P.prevWeight + 1) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H (P.prevWeight + 1)]
    exact ⟨S0.cycle, S0.class_eq⟩
  let a : ClassicalHodgeFiber V H M.weight :=
    P.weight_eq.symm ▸ S0.hodge
  have ha0 : a ≠ 0 := by
    subst P.weight_eq
    exact S0.hodge_ne_zero
  have haAlg : a ∈ AlgebraicHodgeSubspace V H M.weight := by
    subst P.weight_eq
    exact hAlg0
  exact localSeedOfNonzeroAlgebraic G M a haAlg ha0

/-- **POSITIVE-WEIGHT MINIMAL-GHOST EXTINCTION.**
For a positive minimal bad weight, one exact projective separator successor and
one native-natural bare GST `L²` motion into the detected sheet are already
incompatible with a Hodge failure. -/
theorem minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (P : PositiveWeightSeparatorSeed G M)
    (hL : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz (P.localSeed G M).sourceIndex M.sheet)) : False :=
  minimalGhost_false_of_localSeed_bareLefschetz
    G M (P.localSeed G M) hL

/-- Global minimal-ghost criterion in its smallest local form: every
hypothetical minimal ghost only needs one nonzero algebraic source and one bare
GST `L²` native motion into its detected sheet. -/
theorem bigradedBettiHodge_of_localSeeds_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostLocalSeed G M))
    (hL : ∀ M : MinimalPrimitiveGhost G,
      ∀ S : MinimalGhostLocalSeed G M,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz S.sourceIndex M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_localSeed_bareLefschetz
    G M (seed M).some (hL M (seed M).some)

#check MinimalGhostLocalSeed
#check ambientTwoStepLefschetz_on_hodge_coordinate
#check minimalGhost_false_of_localSeed_bareLefschetz
#check localSeedOfNonzeroAlgebraic
#check PositiveWeightSeparatorSeed
#check PositiveWeightSeparatorSeed.localSeed
#check minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
#check bigradedBettiHodge_of_localSeeds_bareLefschetz

#print axioms ambientTwoStepLefschetz_on_hodge_coordinate
#print axioms minimalGhost_false_of_localSeed_bareLefschetz
#print axioms PositiveWeightSeparatorSeed.localSeed
#print axioms minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
#print axioms bigradedBettiHodge_of_localSeeds_bareLefschetz

end GSTClassicalHodgeLocalSeedBareLefschetzExtinction
