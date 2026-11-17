import GSTClassicalHodgeCycleClassIntersectionPrimitives
import GSTClassicalHodgeAmbientCorrespondenceIncidenceNaturality
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — STRICT TRANSFER FROM LOW-LEVEL PRIMITIVES

This file removes the old `PointFiberIntersectionLaw` as an independent input.
It constructs that law from the split low-level ingredients:

* rational cup product and projection Gysin theory;
* genuine point fundamental classes;
* point-cylinder pullback;
* cycle-class/intersection for C ∩ ({x} × X);
* proper pushforward of that finite intersection;
* point-rigidity identifying the supplied Stage-2G cycle-class map with the
  uniquely generated geometric map.

The global cycle-class commuting square is then inherited from the already
proved point-normal-form lift.  Thus the final transfer equality is a theorem,
not a field of any primitive structure.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeAmbientCorrespondenceIncidenceNaturality
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- Construct the historical point-fiber law from the genuinely lower-level
intersection primitives. -/
noncomputable def toPointFiberIntersectionLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    PointFiberIntersectionLaw
      (H := H) (p := p)
      (toAmbientBettiIntersectionCalculus H.analytification P) K kappa where
  fiberIntersectionClass := I.intersection.fiberIntersectionClass
  kernel_cup_pointPullback := by
    intro x
    rw [hpoint x]
    exact I.kernel_cup_pointPullback x
  gysin_fiberIntersection := by
    intro x
    have hclass := suppliedCycleClass_eq_geometric
      (V := V) p H pt hpoint
    rw [hclass]
    exact I.projection.gysin_class x

/-- **GLOBAL STRICT CORRESPONDENCE TRANSFER FROM PRIMITIVES.**
For every native rational algebraic codimension-p cycle Z,

  cl(K_* Z) = T_C(cl Z),

where T_C is the ambient whole-Betti kernel action built from cup and Gysin.
No correspondence naturality equation is assumed. -/
theorem supplied_cycleClass_nativeOperator
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      kernelAction H.analytification P kappa (2 * p)
        (H.cycleClass p Z) := by
  let J := toPointFiberIntersectionLaw
    (V := V) (H := H) (d := d) (p := p) P K kappa pt hpoint I
  exact J.cycleClass_nativeOperator Z

/-- The exact pointwise realization predicate is therefore derived from the
same low-level primitive packet. -/
theorem realizesAmbientOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      |>.RealizesAmbientOnPoints
        (H := H) (kernelAction H.analytification P kappa (2 * p)) := by
  let J := toPointFiberIntersectionLaw
    (V := V) (H := H) (d := d) (p := p) P K kappa pt hpoint I
  exact J.realizesAmbientOnPoints

/-- Forward and genuine factor-swap transpose transfer are both forced once
we have the corresponding low-level incidence primitives for K and K^t. -/
theorem supplied_forward_and_transpose_transfer
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (It : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p)
      P K.transpose kappa.transposeKernel pt) :
    (∀ Z : codimensionCycles V.X p,
      H.cycleClass p
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativeOperator p Z) =
        kernelAction H.analytification P kappa (2 * p)
          (H.cycleClass p Z))
    ∧
    (∀ Z : codimensionCycles V.X p,
      H.cycleClass p
          (K.transpose.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativeOperator p Z) =
        kernelAction H.analytification P kappa.transposeKernel (2 * p)
          (H.cycleClass p Z)) := by
  let J := toPointFiberIntersectionLaw
    (V := V) (H := H) (d := d) (p := p) P K kappa pt hpoint I
  let Jt := toPointFiberIntersectionLaw
    (V := V) (H := H) (d := d) (p := p)
    P K.transpose kappa.transposeKernel pt hpoint It
  let B : BiPointFiberIntersectionLaw
      (H := H) (p := p)
      (toAmbientBettiIntersectionCalculus H.analytification P) K kappa :=
    { forward := J, transpose := Jt }
  exact B.forward_and_transpose_cycleClass_natural

#check toPointFiberIntersectionLaw
#check supplied_cycleClass_nativeOperator
#check realizesAmbientOnPoints
#check supplied_forward_and_transpose_transfer

#print axioms supplied_cycleClass_nativeOperator
#print axioms supplied_forward_and_transpose_transfer

end GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
