import GSTGraphV2CMInfiniteCurvatureBridge
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST Graph V2 native fold curvature as actual algebraic-cycle source

The previous CM/information module detected noncommutative fold curvature
in abstract operator algebra. Here the curvature is EXPLICITLY REALIZED
as a rational codimension-p cycle on the ORIGINAL smooth projective X.

Inputs are two existing CycleClassOperatorPair structures: each has a
native algebraic-cycle map, an ambient rational Betti map and the exact
commuting square. The two maps may come from the repository's genuine
realized finite-closed correspondences. All outputs remain actual cycles.

The genuinely constructive curvature cycle is
  Z_curv = N_A(N_B(Z)) - N_B(N_A(Z)).

The exact canonical-semantics cycle-class identity is proved with no
preselected class lift. A rational functional distinguishing the new
commutator class from an old algebraic sector certifies a NEW native
direction, provided the readout is actually obtained from geometry.
The opposite case gives a decisive test: if both operator actions
preserve the old subspace, commutator curvature cannot escape it.
-/

noncomputable section

namespace GSTGraphV2NativeCurvatureBirth

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One actual original-X rational cycle built from noncommuting
native algebraic operators. -/
def nativeCurvatureCycle
    (A B : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  A.cycleOperator (B.cycleOperator Z) -
    B.cycleOperator (A.cycleOperator Z)

/-- Curvature is exactly the cohomological commutator of the two
geometric operations applied to the original algebraic seed. -/
theorem nativeCurvature_cycleClass
    (A B : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeCurvatureCycle A B Z) =
      A.cohomologyOperator (B.cohomologyOperator (H.cycleClass p Z)) -
      B.cohomologyOperator (A.cohomologyOperator (H.cycleClass p Z)) := by
  simp only [nativeCurvatureCycle, map_sub]
  rw [A.cycleClass_cycleOperator, B.cycleClass_cycleOperator,
    B.cycleClass_cycleOperator, A.cycleClass_cycleOperator]

/-- Realized correspondence version: the source operators are anchored
to existing geometric finite-closed correspondences on X. -/
def realizedCurvatureCycle
    (A B : RealizedFiniteClosedCorrespondence V H p)
    (Z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  nativeCurvatureCycle A.operatorPair B.operatorPair Z

theorem realizedCurvature_cycleClass
    (A B : RealizedFiniteClosedCorrespondence V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (realizedCurvatureCycle A B Z) =
      A.cohomologyOperator (B.cohomologyOperator (H.cycleClass p Z)) -
      B.cohomologyOperator (A.cohomologyOperator (H.cycleClass p Z)) := by
  exact nativeCurvature_cycleClass A.operatorPair B.operatorPair Z

/-- A geometric rational detector certifies that a true original-X
curvature cycle leaves an older Hodge-sector subspace. -/
theorem nativeCurvature_escapes_old_sector
    (A B : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (read : RationalSingularCohomology H.analytification (2 * p)
      →ₗ[ℚ] ℚ)
    (hOld : ∀ x ∈ old, read x = 0)
    (hNew : read (H.cycleClass p (nativeCurvatureCycle A B Z)) ≠ 0) :
    H.cycleClass p (nativeCurvatureCycle A B Z) ∉ old := by
  intro hmem
  exact hNew (hOld _ hmem)

/-- Exact restriction on where curvature can create new directions.
When BOTH operations preserve an old algebraic sector, their
commutator necessarily remains in that sector. Hence a geometric
source-birth attempt must exhibit operator escape/mixing. -/
theorem nativeCurvature_stays_in_biinvariant_sector
    (A B : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (hA : ∀ x ∈ old, A.cohomologyOperator x ∈ old)
    (hB : ∀ x ∈ old, B.cohomologyOperator x ∈ old)
    (hZ : H.cycleClass p Z ∈ old) :
    H.cycleClass p (nativeCurvatureCycle A B Z) ∈ old := by
  rw [nativeCurvature_cycleClass]
  exact old.sub_mem (hA _ (hB _ hZ)) (hB _ (hA _ hZ))

/-- A detected curvature-birth class rules out mutual invariance of
the old sector, yielding a sharp criterion for the next CM geometry test. -/
theorem detected_curvature_requires_mixing
    (A B : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (hZ : H.cycleClass p Z ∈ old)
    (hNew : H.cycleClass p (nativeCurvatureCycle A B Z) ∉ old) :
    ¬ ((∀ x ∈ old, A.cohomologyOperator x ∈ old) ∧
       (∀ x ∈ old, B.cohomologyOperator x ∈ old)) := by
  rintro ⟨hA, hB⟩
  exact hNew (nativeCurvature_stays_in_biinvariant_sector
    A B Z old hA hB hZ)

#check nativeCurvatureCycle
#check nativeCurvature_cycleClass
#check realizedCurvatureCycle
#check realizedCurvature_cycleClass
#check nativeCurvature_escapes_old_sector
#check detected_curvature_requires_mixing
#print axioms nativeCurvature_cycleClass
#print axioms detected_curvature_requires_mixing

end GSTGraphV2NativeCurvatureBirth
