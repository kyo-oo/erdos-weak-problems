import GSTClassicalHodgeCycleOperatorNaturality
import GSTGraphV2NativeCurvatureBirth
import GSTImageThreeCurvatureResonance
import Mathlib

/-!
# GST image-3 — TRUE ORIGINAL-X native CM-commutator F compiler

This extension faithfully uses the OWNER'S ORIGINAL geometric
CycleClassOperatorPair and nativeCurvatureCycle semantics, plus its
new original 12-state [J,M] curvature-only source theorem.

The two-parameter ORIGINAL-X cycle F is
  F_(a,b) = U + J + a M + b (J o M - M o J)
on ACTUAL rational native cycles of the SAME ORIGINAL X.
Every operation has an actual cycle operator and its corresponding
canonical rational Betti operator, with an exactly proved commuting
cycle-class square. No basis of unknown rational Hodge classes or
nonexistent Chow inverse is supplied.

This compiler is CONDITIONAL on the independent construction of
TRUE original-X U,J,M pairs. The 12-state native determinant does
not automatically transfer to the target Betti Hodge space.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTImageThreeOriginalXCurvatureLanding

open GSTClassicalHodgeCycleOperatorNaturality
open GSTGraphV2NativeCurvatureBirth
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The TRUE new original-X algebraic source is the CM/source
commutator of two already certified genuine native operators. -/
def cmSourcePair
    (J M : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator :=
    J.cycleOperator.comp M.cycleOperator -
      M.cycleOperator.comp J.cycleOperator
  cohomologyOperator :=
    J.cohomologyOperator.comp M.cohomologyOperator -
      M.cohomologyOperator.comp J.cohomologyOperator
  cycleClass_natural := by
    apply LinearMap.ext
    intro Z
    simp [LinearMap.comp_apply, map_sub,
      J.cycleClass_cycleOperator, M.cycleClass_cycleOperator]

/-- Original-X version of the new TWO-PARAMETER native GST source,
with completely genuine Chow/Betti correspondence semantics. -/
def geometricCurvatureF
    (U J M : CycleClassOperatorPair V H p)
    (a b : ℚ) : CycleClassOperatorPair V H p where
  cycleOperator :=
    U.cycleOperator + J.cycleOperator +
      a • M.cycleOperator + b • (cmSourcePair J M).cycleOperator
  cohomologyOperator :=
    U.cohomologyOperator + J.cohomologyOperator +
      a • M.cohomologyOperator +
        b • (cmSourcePair J M).cohomologyOperator
  cycleClass_natural := by
    apply LinearMap.ext
    intro Z
    simp [LinearMap.comp_apply, map_add, map_smul,
      U.cycleClass_cycleOperator, J.cycleClass_cycleOperator,
      M.cycleClass_cycleOperator,
      (cmSourcePair J M).cycleClass_cycleOperator]

/-- The new GST curvature-only F=U+J+[J,M] has a genuine canonical
original-X native cycle-class realization as soon as its
geometric U,J,M inputs are supplied. -/
def geometricCurvatureOnlyF
    (U J M : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p :=
  geometricCurvatureF U J M 0 1

/-- The actual original-X rational Betti class of the new
CM/source curvature is the Betti commutator, never a formal
synthetic vector or unverified class inverse. -/
theorem cmSourcePair_canonicalClass
    (J M : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((cmSourcePair J M).cycleOperator Z) =
      J.cohomologyOperator (M.cohomologyOperator (H.cycleClass p Z)) -
        M.cohomologyOperator (J.cohomologyOperator (H.cycleClass p Z)) := by
  simpa [cmSourcePair] using
    (nativeCurvature_cycleClass J M Z)

/-- Entire original-X two-parameter F satisfies the canonical
geometric cycle-class square. -/
theorem geometricCurvatureF_canonicalClass
    (U J M : CycleClassOperatorPair V H p)
    (a b : ℚ) (Z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricCurvatureF U J M a b).cycleOperator Z) =
      (geometricCurvatureF U J M a b).cohomologyOperator
        (H.cycleClass p Z) :=
  (geometricCurvatureF U J M a b).cycleClass_cycleOperator Z

/-- This is TRUE native Chow source birth, conditional on the
existence of genuine original-X U/J/M operators, but not on
any artificial target Hodge-class inverse. -/
theorem geometricCurvatureOnlyF_canonicalClass
    (U J M : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricCurvatureOnlyF U J M).cycleOperator Z) =
      (geometricCurvatureOnlyF U J M).cohomologyOperator
        (H.cycleClass p Z) :=
  (geometricCurvatureOnlyF U J M).cycleClass_cycleOperator Z

#check cmSourcePair
#check geometricCurvatureF
#check geometricCurvatureOnlyF
#check cmSourcePair_canonicalClass
#check geometricCurvatureF_canonicalClass
#check geometricCurvatureOnlyF_canonicalClass

#print axioms cmSourcePair_canonicalClass
#print axioms geometricCurvatureOnlyF_canonicalClass

end GSTImageThreeOriginalXCurvatureLanding
