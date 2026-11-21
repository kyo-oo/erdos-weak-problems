import GSTPerfectPowerTailNavigation
import GSTGraphV2NativeCurvatureBirth

/-!
# GST Image 3 — genuine original-X Chow/Hodge compiler gate

This module CONNECTS the user's NEW physical navigation charge with the
owner's ALREADY EXISTING genuine native cycle-class operator-pair
semantics on a fixed ORIGINAL smooth projective complex scheme X.

Crucial distinction:
* The native GST U,J,M operators from WaveFusion are constructed
  completely in the original twelve-cell symbolic GST carrier.
* This file takes three ACTUAL original-X CycleClassOperatorPair objects
  as inputs, each with a genuine rational cycle operator and Betti
  cycle-class square; it does NOT assume that any arbitrary symbolic
  U/J/M matrix magically becomes a Chow correspondence.
* It constructs the navigation-gated cycle/BETTI operator pair from
  those inputs, proves exact canonical naturality, and derives
  the all-rational navigation-gated CM-curvature source formula.

Thus the new image-3 native source machinery has a typed and kernel-
checkable original-X landing INTERFACE, but the universal geometric
construction of U,J,M with the required full Hodge orbit remains the
open part of the owner's GST Hodge antecedent.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeOriginalXNativeLanding

open GSTPerfectPowerTailNavigation
open GSTClassicalHodgeCycleOperatorNaturality
open GSTGraphV2NativeCurvatureBirth
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The TRUE original-X rational Chow and Betti F-operator constructed
from three actual certified native correspondence pairs with the
physical navigation charge from the original seven-axis GST graph. -/
def geometricF
    (U J M : CycleClassOperatorPair V H p)
    (R : Nat) : CycleClassOperatorPair V H p where
  cycleOperator :=
    U.cycleOperator + J.cycleOperator +
      navigationCharge R • M.cycleOperator
  cohomologyOperator :=
    U.cohomologyOperator + J.cohomologyOperator +
      navigationCharge R • M.cohomologyOperator
  cycleClass_natural := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul]
    rw [U.cycleClass_cycleOperator,
      J.cycleClass_cycleOperator,
      M.cycleClass_cycleOperator]

/-- ACTUAL native-to-Hodge square on all original-X rational cycles.
No synthetic matrix basis and no target-class inverse are supplied. -/
theorem geometricF_cycleClass
    (U J M : CycleClassOperatorPair V H p)
    (R : Nat) (z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricF U J M R).cycleOperator z) =
      (geometricF U J M R).cohomologyOperator
        (H.cycleClass p z) :=
  (geometricF U J M R).cycleClass_cycleOperator z

/-- The entire native geometric F is invariant under the EXISTING
canonical-tail navigation equivalence. -/
theorem geometricF_canonicalTail
    (U J M : CycleClassOperatorPair V H p)
    (s b : Nat) (hs : 1 ≤ s) :
    geometricF U J M (4^(3^s*b)) =
      geometricF U J M (canonicalTail s b) := by
  simp only [geometricF, navigationCharge_canonicalTail s b hs]

/-- CM curvature of a REAL original-X native F operation is exactly
the owner's genuine source curvature scaled by Navigation, PROVIDED
the actual geometric U,J satisfy their native commutation law.
No abstract information-space commutation is smuggled into geometry. -/
theorem geometricF_native_CM_defect
    (U J M : CycleClassOperatorPair V H p)
    (hJU : ∀ z : codimensionCycles V.X p,
      J.cycleOperator (U.cycleOperator z) =
        U.cycleOperator (J.cycleOperator z))
    (R : Nat) (z : codimensionCycles V.X p) :
    J.cycleOperator ((geometricF U J M R).cycleOperator z) -
      (geometricF U J M R).cycleOperator (J.cycleOperator z) =
      navigationCharge R •
        (J.cycleOperator (M.cycleOperator z) -
         M.cycleOperator (J.cycleOperator z)) := by
  simp only [geometricF, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul]
  rw [hJU z, smul_sub]
  abel_nf

/-- The corresponding ORIGINAL-X rational Hodge cohomological curvature
is the class of the REAL native cycle, not a symbolic source claim. -/
theorem geometricF_CM_curvature_class
    (U J M : CycleClassOperatorPair V H p)
    (R : Nat) (z : codimensionCycles V.X p) :
    H.cycleClass p (nativeCurvatureCycle J (geometricF U J M R) z) =
      J.cohomologyOperator
        ((geometricF U J M R).cohomologyOperator (H.cycleClass p z)) -
      (geometricF U J M R).cohomologyOperator
        (J.cohomologyOperator (H.cycleClass p z)) :=
  nativeCurvature_cycleClass J (geometricF U J M R) z

#check geometricF
#check geometricF_cycleClass
#check geometricF_canonicalTail
#check geometricF_native_CM_defect
#check geometricF_CM_curvature_class
#print axioms geometricF_cycleClass
#print axioms geometricF_native_CM_defect

end GSTImageThreeOriginalXNativeLanding
