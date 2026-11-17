import GSTClassicalHodgeCrossCarrierCupGysinConstruction
import GSTClassicalHodgeAmbientIntersectionFromPrimitives

/-!
# Exact compatibility of GST cross-carrier and existing self-product Gysin

The new cross-carrier cup/Gysin construction is REQUIRED to agree with the
original HC-PROOF geometric self-correspondence kernel calculus when source
and target are the same smooth projective variety.

This file constructs that specialization from the existing genuine analytic
self-product singular-cohomology space, existing rational cup primitives,
and existing proper projection Gysin primitives. It does not choose a freely
supplied Betti action and does not assume any Hodge class is algebraic.

Consequently the 2026 CM/Kuga-Satake/Gale cross-carrier geometry is an
extension of the original GST action, not a different semantics.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 900000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeCrossCarrierCupGysinConstruction

namespace GSTClassicalHodgeCrossCarrierSelfProductCompatibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}
variable {K : SchemeBiFiniteClosedCorrespondence V}

/-- SAME VARIETY SPECIALIZATION of the geometrically typed source/target
cup and Gysin packet. Source and target dimension d, correspondence
codimension d, source and target cycle codimension p. -/
noncomputable def crossProductOfExistingSelfKernel
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K) :
    CrossProductCupGysin V V H H
      (fun n => ProductCohomology H.analytification n)
      d p p d where
  degree_balance := by omega
  sourcePullback := fstCohomologyPullback H.analytification (2 * p)
  kernelClass := kappa.kernelClass
  cup := P.cupTheory.cup (2 * d) (2 * p)
  targetGysin := P.gysinTheory.sndGysin (2 * p)

/-- THE NEW CROSS-CARRIER ACTION IS EXACTLY THE ORIGINAL AMBIENT
GEOMETRIC CORRESPONDENCE ACTION, not merely pointwise equivalent.

This identity is the integration check that preserves all existing
self-product GST mathematics after adding cross-variety kernels. -/
theorem crossProductOfExistingSelfKernel_action_eq
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K) :
    (crossProductOfExistingSelfKernel (p := p) P kappa).action =
      kernelAction H.analytification P kappa (2 * p) := by
  rfl

/-- Compatibility in its exact computational form for every rational
Betti class: cup with the original kernel, then integrate along p2. -/
theorem crossProductOfExistingSelfKernel_action_apply
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    (crossProductOfExistingSelfKernel (p := p) P kappa).action alpha =
      P.gysinTheory.sndGysin (2 * p)
        (P.cupTheory.cup (2 * d) (2 * p)
          kappa.kernelClass
          (fstCohomologyPullback H.analytification (2 * p) alpha)) := by
  rfl

#check crossProductOfExistingSelfKernel
#check crossProductOfExistingSelfKernel_action_eq
#check crossProductOfExistingSelfKernel_action_apply
#print axioms crossProductOfExistingSelfKernel_action_eq

end GSTClassicalHodgeCrossCarrierSelfProductCompatibility
