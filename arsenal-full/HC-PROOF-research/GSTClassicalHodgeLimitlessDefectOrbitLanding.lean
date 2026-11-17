import GSTClassicalHodgeFiberedDefectEquivariance
import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeConcreteRankFreeGeneration
import GSTClassicalHodgeBasisCycleBridge

/-!
# GST CLASSICAL HODGE — LIMITLESS ZERO-DEFECT ORBIT LANDING

The unrestricted GST rank-free machinery already proves that one nonzero source
sheet can reach every genuine Hodge multiplicity direction by concrete finite
projector/Lefschetz/Poincare words.  The remaining classical issue is whether
those words are realized by genuine native algebraic-cycle operators with the
same actual cohomological action.

This file gives the exact constructive landing when they are.  Starting from
one genuine point-cycle whose class equals one source Hodge basis vector, each
target direction is reached by a genuine cycle-class operator pair.  The
fibered defect-equivariance theorem transports zero defect along the GST/native
tensor word.  Dividing by the nonzero native transition mass produces a
zero-defect state whose Hodge face is exactly the target basis vector.

Thus the entire Hodge basis receives actual native cycle representatives, and
finite-support basis reconstruction closes the Stage-2G Hodge statement.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessDefectOrbitLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeTensorArsenal
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedDefectEquivariance
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One genuine source point and one source Hodge sheet already identified by
the actual cycle-class map. -/
structure DefectZeroPointSeed
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  source : ClassicalHodgeBasisIndex V H p
  point : CodimensionPoint V.X p
  class_eq :
    H.cycleClass p (codimensionPointCycle V.X p point) =
      (classicalHodgeBasis V H p source).1

namespace DefectZeroPointSeed

/-- The common source atom has zero classical defect. -/
theorem atom_defect_zero
    (S : DefectZeroPointSeed V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (atom V H p S.source S.point) = 0 := by
  exact (fiberedCycleClassDefect_atom_eq_zero_iff
    (V := V) (H := H) (p := p) S.source S.point).2 S.class_eq

end DefectZeroPointSeed

/-- A genuine native/cohomological tensor transport from the fixed source
sheet to one target sheet, with nonzero point-transition coefficient. -/
structure GenuineTargetTransport
    (S : DefectZeroPointSeed V H p)
    (target : ClassicalHodgeBasisIndex V H p) where
  pair : CycleClassOperatorPair V H p
  intertwines : TensorIntertwinesAt pair S.source target S.point
  mass_ne_zero : pointTransitionMass pair.cycleOperator S.point ≠ 0

namespace GenuineTargetTransport

/-- Raw target orbit state. -/
noncomputable def rawState
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    FiberedNativeAddress V H p :=
  tensorWord S.source target T.pair.cycleOperator
    (atom V H p S.source S.point)

/-- Raw orbit state has zero defect by genuine equivariance. -/
theorem rawState_defect_zero
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) T.rawState = 0 := by
  unfold rawState
  exact defectZero_tensorWord_atom
    T.pair S.source target S.point T.intertwines S.atom_defect_zero

/-- Normalize by the actual nonzero native transition mass. -/
noncomputable def normalizedState
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    FiberedNativeAddress V H p :=
  (pointTransitionMass T.pair.cycleOperator S.point)⁻¹ • T.rawState

/-- Zero defect survives normalization. -/
theorem normalizedState_defect_zero
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      T.normalizedState = 0 := by
  unfold normalizedState
  rw [map_smul, T.rawState_defect_zero]
  simp

/-- The Hodge face of the normalized orbit state is exactly the target basis
vector. -/
theorem normalizedState_hodge_exact
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
      T.normalizedState = classicalHodgeBasis V H p target := by
  unfold normalizedState rawState
  rw [map_smul]
  rw [fiberedHodgeClass_tensorWord_atom_source]
  simp [T.mass_ne_zero]

/-- The native face of the normalized orbit state is therefore an actual
codimension-p cycle representing the target Hodge basis vector. -/
theorem normalizedState_cycleClass
    {S : DefectZeroPointSeed V H p}
    {target : ClassicalHodgeBasisIndex V H p}
    (T : GenuineTargetTransport S target) :
    H.cycleClass p (toNativeCycle V H p T.normalizedState) =
      (classicalHodgeBasis V H p target).1 := by
  have hz := (defect_eq_zero_iff_faces_agree
    (V := V) (H := H) (p := p) T.normalizedState).mp
      T.normalizedState_defect_zero
  simpa [T.normalizedState_hodge_exact] using hz

end GenuineTargetTransport

/-- One genuine source atom plus a genuine target transport to every basis
sheet produces the full basis-cycle bridge in this weight. -/
noncomputable def basisCycleBridgeOfDefectOrbit
    (S : DefectZeroPointSeed V H p)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      GenuineTargetTransport S j) :
    HodgeConjecture.HodgeBasisCycleBridge V H p where
  basisCycle j := toNativeCycle V H p (T j).normalizedState
  basisCycle_spec j := (T j).normalizedState_cycleClass

/-- Weightwise orbit landing: the algebraic cycle-class range contains the
entire genuine rational Hodge fiber. -/
theorem hodge_weight_of_defect_orbit
    (S : DefectZeroPointSeed V H p)
    (T : ∀ j : ClassicalHodgeBasisIndex V H p,
      GenuineTargetTransport S j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  let R := basisCycleBridgeOfDefectOrbit S T
  exact HodgeConjecture.hodge_class_has_cycle_of_basis_bridge
    V H R alpha halpha

/-- **LIMITLESS DEFECT-ORBIT HODGE CROWN.**
If every weight has one genuine zero-defect point seed and genuine
cycle-class-natural GST/native transports from that seed to every unrestricted
Hodge basis direction, the exact Stage-2G Hodge statement follows. -/
theorem bigradedBettiHodge_of_defect_orbits
    (seed : ∀ p : Nat, DefectZeroPointSeed V H p)
    (transport : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        GenuineTargetTransport (seed p) j) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_weight_of_defect_orbit (seed p) (transport p) halpha

#check DefectZeroPointSeed
#check GenuineTargetTransport
#check GenuineTargetTransport.normalizedState
#check GenuineTargetTransport.normalizedState_defect_zero
#check GenuineTargetTransport.normalizedState_hodge_exact
#check GenuineTargetTransport.normalizedState_cycleClass
#check basisCycleBridgeOfDefectOrbit
#check bigradedBettiHodge_of_defect_orbits

#print axioms GenuineTargetTransport.normalizedState_defect_zero
#print axioms GenuineTargetTransport.normalizedState_cycleClass
#print axioms bigradedBettiHodge_of_defect_orbits

end GSTClassicalHodgeLimitlessDefectOrbitLanding
