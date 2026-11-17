import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgePointClosureIrreducible
import GSTClassicalHodgeRootedStrictRelationFan
import Mathlib.Topology.Sober

/-!
# GST CLASSICAL HODGE — CODIMENSION-ZERO DEGREE APEX

The degree-certified successor route obtains a nonzero algebraic Hodge seed in
weight `q+1` from one exact principal-cut survivor.  For the ROOT of the
ontological fan that hypothesis is unnecessary.

On every nonempty smooth projective carrier choose any point `x`.  The maximal
irreducible component containing `x` is an actual irreducible component.  Its
sober generic point is maximal in the specialization order, hence has coheight
zero.  The corresponding native codimension-zero point cycle is therefore a
genuine algebraic cycle.

Projective-degree trace semantics evaluates its genuine Betti cycle class to a
strictly positive projective degree.  Consequently the class is nonzero.  The
geometric cycle-class spine already says every native algebraic cycle is a
Hodge class, so this one point cycle gives a `NativeHodgeOrbitSeed` in weight
zero with NO principal-cut exactness premise and NO native-mass bridge.

This is the canonical bottom apex from which a graded GST ontological graph can
start its vertical and horizontal relation rays.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace

namespace GSTClassicalHodgeCodimensionZeroDegreeApex

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A maximal irreducible component selected from one arbitrary point of a
nonempty projective carrier. -/
noncomputable def apexIrreducibleComponent
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] : Set V.X :=
  irreducibleComponent (Classical.choice (inferInstance : Nonempty V.X))

/-- The selected component is genuinely an irreducible component. -/
theorem apexIrreducibleComponent_mem
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    apexIrreducibleComponent V ∈ irreducibleComponents V.X := by
  unfold apexIrreducibleComponent
  exact irreducibleComponent_mem_irreducibleComponents _

/-- The selected component is irreducible. -/
theorem apexIrreducibleComponent_irreducible
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    IsIrreducible (apexIrreducibleComponent V) :=
  (apexIrreducibleComponent_mem V).1

/-- Its sober generic point. -/
noncomputable def apexGenericPoint
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] : V.X :=
  (apexIrreducibleComponent_irreducible V).genericPoint

/-- The closure of the chosen generic point is exactly the selected maximal
irreducible component. -/
theorem apexGenericPoint_closure
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    closure ({apexGenericPoint V} : Set V.X) = apexIrreducibleComponent V := by
  exact (apexIrreducibleComponent_irreducible V).closure_genericPoint
    (isClosed_of_mem_irreducibleComponents _ (apexIrreducibleComponent_mem V))

/-- The generic point of a maximal irreducible component is maximal in the
specialization order. -/
theorem apexGenericPoint_isMax
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    IsMax (apexGenericPoint V) := by
  intro y hle
  have hySpec : y ⤳ apexGenericPoint V := hle
  have hmem : apexGenericPoint V ∈ closure ({y} : Set V.X) :=
    specializes_iff_mem_closure.mp hySpec
  have hsubset : apexIrreducibleComponent V ⊆ closure ({y} : Set V.X) := by
    rw [← apexGenericPoint_closure V]
    exact closure_minimal (by simpa using hmem) isClosed_closure
  have hback : closure ({y} : Set V.X) ⊆ apexIrreducibleComponent V :=
    (apexIrreducibleComponent_mem V).2
      isIrreducible_singleton.closure hsubset
  have hclosure : closure ({y} : Set V.X) = apexIrreducibleComponent V :=
    Set.Subset.antisymm hback hsubset
  have hyGeneric : IsGenericPoint y (apexIrreducibleComponent V) := hclosure
  have hηGeneric : IsGenericPoint (apexGenericPoint V) (apexIrreducibleComponent V) :=
    apexGenericPoint_closure V
  have hEq : y = apexGenericPoint V := hyGeneric.eq hηGeneric
  simpa [hEq]

/-- The selected generic point is therefore an actual codimension-zero point. -/
noncomputable def apexCodimensionZeroPoint
    (V : SmoothProjectiveComplexScheme) [Nonempty V.X] :
    CodimensionPoint V.X 0 :=
  ⟨apexGenericPoint V,
    Order.coheight_eq_zero.mpr (apexGenericPoint_isMax V)⟩

/-- Projective degree forces the genuine cycle class of the apex point cycle to
be nonzero. -/
theorem apexPoint_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X] :
    H.cycleClass 0
      (codimensionPointCycle V.X 0 (apexCodimensionZeroPoint V)) ≠ 0 := by
  intro hzero
  have htrace := D.trace_point_cycleClass 0 (apexCodimensionZeroPoint V)
  rw [hzero, LinearMap.map_zero] at htrace
  have hdeg : D.pointDegree 0 (apexCodimensionZeroPoint V) ≠ 0 :=
    ne_of_gt (D.pointDegree_pos 0 (apexCodimensionZeroPoint V))
  exact hdeg htrace.symm

/-- **UNCONDITIONAL NONEMPTY-CARRIER OMNIVERSE APEX.**
A single generic point cycle gives a genuine nonzero algebraic Hodge seed in
weight zero, certified only by projective degree. -/
noncomputable def codimensionZeroDegreeApex
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X] :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := 0) := by
  let Z : codimensionCycles V.X 0 :=
    codimensionPointCycle V.X 0 (apexCodimensionZeroPoint V)
  let alpha : ClassicalHodgeFiber V H 0 :=
    ⟨H.cycleClass 0 Z, G.algebraic_is_hodge 0 Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  have hval : H.cycleClass 0 Z = 0 := congrArg Subtype.val hz
  exact apexPoint_cycleClass_ne_zero D (by simpa [Z] using hval)

/-- The rooted strict-relation fan can therefore start at weight zero without
any exact-successor or native-mass hypothesis. -/
theorem hodge_weight_zero_of_degreeApex_rootedFan
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (F : GSTClassicalHodgeRootedStrictRelationFan.RootedStrictRelationFan
      (codimensionZeroDegreeApex G D)) :
    rationalHodgeSubspace (H.hodgeBigrading 0) ≤
      LinearMap.range (H.cycleClass 0) :=
  GSTClassicalHodgeRootedStrictRelationFan.hodge_weight_of_rootedStrictRelationFan
    (codimensionZeroDegreeApex G D) F

#check apexIrreducibleComponent
#check apexGenericPoint
#check apexGenericPoint_isMax
#check apexCodimensionZeroPoint
#check apexPoint_cycleClass_ne_zero
#check codimensionZeroDegreeApex
#check hodge_weight_zero_of_degreeApex_rootedFan

#print axioms apexGenericPoint_isMax
#print axioms apexPoint_cycleClass_ne_zero
#print axioms codimensionZeroDegreeApex
#print axioms hodge_weight_zero_of_degreeApex_rootedFan

end GSTClassicalHodgeCodimensionZeroDegreeApex
