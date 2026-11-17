import GSTClassicalHodgeLocalSeedBareLefschetzExtinction
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import Mathlib.Topology.Sober

/-!
# GST CLASSICAL HODGE — WEIGHT-ZERO LOCAL SEED

The positive-weight minimal-ghost attack obtains its algebraic source from one
exact principal-cut successor.  Weight zero needs no successor at all.

A nonempty smooth projective carrier is Noetherian and sober.  Pick any point,
choose an irreducible component containing it, and take the generic point of
that component.  The generic point is maximal in the specialization order and
therefore has coheight zero, so it is an actual native codimension-zero point.

Projective-degree trace semantics then proves that the cycle class of this unit
component atom is nonzero.  The geometric cycle-class spine places it in the
rational (0,0) Hodge sector.  Thus every weight-zero minimal ghost already has
the nonzero algebraic source required by the bare two-slot GST L^2 extinction
argument.

No Hodge-surjectivity or realization certificate is used.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgeZeroWeightLocalSeed

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTSmoothProjectiveNoetherian
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A generic point of an irreducible component is maximal in the
specialization order of a T0 sober space. -/
attribute [local instance] specializationOrder in
theorem genericPointOfComponent_isMax
    {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X]
    (C : irreducibleComponents X) :
    IsMax (genericPoints.ofComponent C : X) := by
  let g : X := (genericPoints.ofComponent C : X)
  have hg : IsGenericPoint g C.1 :=
    genericPoints.isGenericPoint_ofComponent C
  intro y hgy
  have hgin : g ∈ closure ({y} : Set X) :=
    (specializationOrder_iff_specializes).mp hgy
  have hCg_le : C.1 ⊆ closure ({y} : Set X) := by
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hgin) isClosed_closure
  have hyIrred : IsIrreducible (closure ({y} : Set X)) :=
    isIrreducible_singleton.closure
  have hyleC : closure ({y} : Set X) ⊆ C.1 := by
    exact C.2.2 (closure ({y} : Set X)) hyIrred hCg_le
  have hEq : closure ({y} : Set X) = C.1 :=
    Set.Subset.antisymm hyleC hCg_le
  have hyGen : IsGenericPoint y C.1 := hEq
  have hyg : y = g := hyGen.eq hg
  subst y
  exact le_rfl

/-- Every nonempty smooth projective carrier has a genuine codimension-zero
point: the generic point of one irreducible component. -/
noncomputable def someCodimensionZeroPoint
    (V : SmoothProjectiveComplexScheme)
    [Nonempty V.X] : CodimensionPoint V.X 0 := by
  let x : V.X := Classical.choice (inferInstance : Nonempty V.X)
  let C : irreducibleComponents V.X :=
    ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
  let g : V.X := (genericPoints.ofComponent C : V.X)
  refine ⟨g, ?_⟩
  exact Order.coheight_eq_zero.mpr (genericPointOfComponent_isMax C)

/-- Projective degree detects the unit codimension-zero component atom, so its
genuine Betti cycle class is nonzero. -/
theorem codimensionZeroPoint_cycleClass_ne_zero
    [Nonempty V.X]
    (D : ProjectiveDegreeTraceSemantics V H) :
    H.cycleClass 0
      (codimensionPointCycle V.X 0 (someCodimensionZeroPoint V)) ≠ 0 := by
  intro hzero
  have htrace := D.trace_point_cycleClass 0 (someCodimensionZeroPoint V)
  rw [hzero, LinearMap.map_zero] at htrace
  have hpos := D.pointDegree_pos 0 (someCodimensionZeroPoint V)
  rw [← htrace] at hpos
  exact lt_irrefl 0 hpos

/-- Canonical nonzero algebraic Hodge seed in weight zero. -/
noncomputable def zeroWeightNativeHodgeSeed
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) :
    GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := 0) := by
  let Z : codimensionCycles V.X 0 :=
    codimensionPointCycle V.X 0 (someCodimensionZeroPoint V)
  let a : ClassicalHodgeFiber V H 0 :=
    ⟨H.cycleClass 0 Z, G.algebraic_is_hodge 0 Z⟩
  refine {
    cycle := Z
    hodge := a
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  have hval : H.cycleClass 0 Z = 0 := congrArg Subtype.val hz
  exact codimensionZeroPoint_cycleClass_ne_zero D (by simpa [Z] using hval)

/-- A weight-zero minimal ghost therefore has the exact local seed packet used
by bare-Lefschetz extinction. -/
noncomputable def zeroWeightLocalSeed
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 0) :
    MinimalGhostLocalSeed G M := by
  let S0 := zeroWeightNativeHodgeSeed G D
  have hAlg0 : S0.hodge ∈ AlgebraicHodgeSubspace V H 0 := by
    rw [← GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span V H 0]
    exact ⟨S0.cycle, S0.class_eq⟩
  let a : ClassicalHodgeFiber V H M.weight := hM.symm ▸ S0.hodge
  have ha0 : a ≠ 0 := by
    subst hM
    exact S0.hodge_ne_zero
  have haAlg : a ∈ AlgebraicHodgeSubspace V H M.weight := by
    subst hM
    exact hAlg0
  exact localSeedOfNonzeroAlgebraic G M a haAlg ha0

/-- **WEIGHT-ZERO MINIMAL-GHOST EXTINCTION.**
On a nonempty projective carrier, projective degree gives the source and one
native-natural bare GST L^2 motion into the ghost sheet gives the
contradiction. -/
theorem minimalGhost_false_of_zeroWeight_bareLefschetz
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 0)
    (hL : GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz
        (zeroWeightLocalSeed G D M hM).sourceIndex M.sheet)) : False :=
  minimalGhost_false_of_localSeed_bareLefschetz
    G M (zeroWeightLocalSeed G D M hM) hL

#check genericPointOfComponent_isMax
#check someCodimensionZeroPoint
#check codimensionZeroPoint_cycleClass_ne_zero
#check zeroWeightNativeHodgeSeed
#check zeroWeightLocalSeed
#check minimalGhost_false_of_zeroWeight_bareLefschetz

#print axioms genericPointOfComponent_isMax
#print axioms codimensionZeroPoint_cycleClass_ne_zero
#print axioms zeroWeightNativeHodgeSeed
#print axioms minimalGhost_false_of_zeroWeight_bareLefschetz

end GSTClassicalHodgeZeroWeightLocalSeed
