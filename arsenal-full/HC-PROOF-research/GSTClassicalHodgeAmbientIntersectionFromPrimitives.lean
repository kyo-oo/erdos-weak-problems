import GSTClassicalHodgeBettiCupGysinPrimitives
import GSTClassicalHodgeAmbientCorrespondenceKernelAction

/-!
# GST CLASSICAL HODGE — AMBIENT INTERSECTION CALCULUS FROM PRIMITIVES

The correspondence layer historically accepted one bundled
`AmbientBettiIntersectionCalculus`.  This file proves that bundle is merely a
repackaging of two strictly lower-level pieces:

* rational singular cup product;
* projection Poincare/Gysin integration.

Thus no correspondence-specific law remains hidden inside the calculus.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeAmbientIntersectionFromPrimitives

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Package the independent cup/Gysin theories into the historical ambient
calculus consumed by the correspondence kernel formula. -/
noncomputable def toAmbientBettiIntersectionCalculus
    {d : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :
    AmbientBettiIntersectionCalculus A d where
  cup := P.cupTheory.cup
  sndGysin := P.gysinTheory.sndGysin
  fstGysin := P.gysinTheory.fstGysin
  swap_cup := P.cupTheory.swap_natural
  sndGysin_swap := P.gysinTheory.snd_swap
  fstGysin_swap := P.gysinTheory.fst_swap

@[simp]
theorem toAmbient_cup
    {d a b : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :
    (toAmbientBettiIntersectionCalculus A P).cup a b =
      P.cupTheory.cup a b := rfl

@[simp]
theorem toAmbient_sndGysin
    {d n : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :
    (toAmbientBettiIntersectionCalculus A P).sndGysin n =
      P.gysinTheory.sndGysin n := rfl

@[simp]
theorem toAmbient_fstGysin
    {d n : Nat}
    (P : RationalBettiIntersectionPrimitives A d) :
    (toAmbientBettiIntersectionCalculus A P).fstGysin n =
      P.gysinTheory.fstGysin n := rfl

/-- Whole-Betti correspondence action constructed directly from the split
low-level topology primitives. -/
noncomputable def kernelAction
    {d : Nat}
    {K : GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.SchemeBiFiniteClosedCorrespondence V}
    (P : RationalBettiIntersectionPrimitives A d)
    (kappa : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ]
      RationalSingularCohomology A n :=
  MiddleBettiCorrespondenceKernel.action A
    (toAmbientBettiIntersectionCalculus A P) kappa n

@[simp]
theorem kernelAction_apply
    {d : Nat}
    {K : GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.SchemeBiFiniteClosedCorrespondence V}
    (P : RationalBettiIntersectionPrimitives A d)
    (kappa : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat)
    (alpha : RationalSingularCohomology A n) :
    kernelAction A P kappa n alpha =
      P.gysinTheory.sndGysin n
        (P.cupTheory.cup (2 * d) n kappa.kernelClass
          (fstCohomologyPullback A n alpha)) := by
  rfl

/-- The algebraic transpose action is already forced by the same two
low-level theories plus genuine factor swap. -/
theorem transpose_kernelAction_apply
    {d : Nat}
    {K : GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.SchemeBiFiniteClosedCorrespondence V}
    (P : RationalBettiIntersectionPrimitives A d)
    (kappa : MiddleBettiCorrespondenceKernel A d K)
    (n : Nat)
    (alpha : RationalSingularCohomology A n) :
    kernelAction A P kappa.transposeKernel n alpha =
      P.gysinTheory.fstGysin n
        (P.cupTheory.cup (2 * d) n kappa.kernelClass
          (sndCohomologyPullback A n alpha)) := by
  exact kappa.transpose_action_apply A
    (toAmbientBettiIntersectionCalculus A P) n alpha

#check toAmbientBettiIntersectionCalculus
#check kernelAction
#check kernelAction_apply
#check transpose_kernelAction_apply

#print axioms kernelAction_apply
#print axioms transpose_kernelAction_apply

end GSTClassicalHodgeAmbientIntersectionFromPrimitives
