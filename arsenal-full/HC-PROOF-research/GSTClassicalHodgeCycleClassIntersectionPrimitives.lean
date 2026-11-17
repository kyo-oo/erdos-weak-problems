import GSTClassicalHodgeAmbientIntersectionFromPrimitives
import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgeFiniteClosedCorrespondenceOperator

/-!
# GST CLASSICAL HODGE — CYCLE-CLASS INTERSECTION PRIMITIVES

This is the scheme/intersection-theory layer below correspondence naturality.
It decomposes the point-incidence calculation into three independent standard
facts:

1. the Betti class of `{x} x X` is p1^* of the point fundamental class;
2. cup with the correspondence class `[C]` computes the class of the
   scheme-theoretic intersection `C ∩ ({x} x X)`;
3. proper projection p2_! of that intersection class is the cycle class of the
   residue-degree-weighted finite image.

No final `cl(K_*Z) = T_C(cl Z)` law is stored as an input.  That equation is
proved at the bottom from these three pieces and then can be globalized using
the already-proved point normal form.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCycleClassIntersectionPrimitives

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAmbientBettiSelfProduct
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeGeometricCycleClassPointRigidity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

abbrev PointClass
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  PointBettiClass (V := V) (p := p) H.analytification

abbrev GeometricCycleClass
    (pt : PointClass (V := V) (H := H) p) :=
  cycleClassFromPointGeometry (V := V) p H.analytification pt

/-- Standard pullback law for a point cylinder `{x} x X`.
The cylinder class itself is explicit data of the cycle-class construction;
the equality is ordinary pullback naturality. -/
structure PointCylinderPullbackLaw
    (pt : PointClass (V := V) (H := H) p) where
  pointCylinderClass :
    CodimensionPoint V.X p →
      ProductCohomology H.analytification (2 * p)

  class_eq_fstPullback :
    ∀ x : CodimensionPoint V.X p,
      pointCylinderClass x =
        fstCohomologyPullback H.analytification (2 * p) (pt x)

/-- Standard cycle-class/intersection identity for intersecting `[C]` with
`{x} x X`.  It does not mention the projected incidence cycle. -/
structure KernelFiberIntersectionLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    {K : SchemeBiFiniteClosedCorrespondence V}
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    {pt : PointClass (V := V) (H := H) p}
    (Cyl : PointCylinderPullbackLaw (V := V) (H := H) (p := p) pt) where
  fiberIntersectionClass :
    CodimensionPoint V.X p →
      ProductCohomology H.analytification (2 * d + 2 * p)

  class_eq_kernel_cup_cylinder :
    ∀ x : CodimensionPoint V.X p,
      fiberIntersectionClass x =
        P.cupTheory.cup (2 * d) (2 * p) kappa.kernelClass
          (Cyl.pointCylinderClass x)

/-- Standard proper-pushforward compatibility for the finite fiber
intersection.  The target class is the GEOMETRIC cycle class generated from
point fundamental classes, not the historical Stage-2G field. -/
structure ProperProjectionFiberLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    {pt : PointClass (V := V) (H := H) p}
    {kappa : MiddleBettiCorrespondenceKernel H.analytification d K}
    {Cyl : PointCylinderPullbackLaw (V := V) (H := H) (p := p) pt}
    (Int : KernelFiberIntersectionLaw
      (V := V) (H := H) (d := d) (p := p) P kappa Cyl) where
  gysin_class :
    ∀ x : CodimensionPoint V.X p,
      P.gysinTheory.sndGysin (2 * p) (Int.fiberIntersectionClass x) =
        GeometricCycleClass (V := V) (H := H) (p := p) pt
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativePointImage p x)

/-- Complete low-level packet, factored into the three independent standard
intersection-theory laws above. -/
structure GeometricIncidencePrimitives
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (kappa : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p) where
  cylinder : PointCylinderPullbackLaw (V := V) (H := H) (p := p) pt
  intersection : KernelFiberIntersectionLaw
    (V := V) (H := H) (d := d) (p := p) P kappa cylinder
  projection : ProperProjectionFiberLaw
    (V := V) (H := H) (d := d) (p := p) P K intersection

namespace GeometricIncidencePrimitives

variable
    {P : RationalBettiIntersectionPrimitives H.analytification d}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {kappa : MiddleBettiCorrespondenceKernel H.analytification d K}
    {pt : PointClass (V := V) (H := H) p}

/-- Derived intersection identity with the actual pullback of the point
fundamental class. -/
theorem kernel_cup_pointPullback
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (x : CodimensionPoint V.X p) :
    P.cupTheory.cup (2 * d) (2 * p) kappa.kernelClass
        (fstCohomologyPullback H.analytification (2 * p) (pt x)) =
      I.intersection.fiberIntersectionClass x := by
  rw [← I.cylinder.class_eq_fstPullback x]
  exact (I.intersection.class_eq_kernel_cup_cylinder x).symm

/-- **LOW-LEVEL POINT TRANSFER THEOREM.**
The actual ambient kernel action on a genuine point fundamental class is the
geometric cycle class of the actual finite incidence image.  This is proved,
not stored, from point-cylinder pullback + intersection + proper pushforward. -/
theorem kernelAction_point
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (x : CodimensionPoint V.X p) :
    kernelAction H.analytification P kappa (2 * p) (pt x) =
      GeometricCycleClass (V := V) (H := H) (p := p) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) := by
  rw [kernelAction_apply]
  rw [I.kernel_cup_pointPullback x]
  exact I.projection.gysin_class x

/-- The same theorem with the geometrically generated class of the point
cycle written explicitly. -/
theorem geometric_cycleClass_point_natural
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K kappa pt)
    (x : CodimensionPoint V.X p) :
    GeometricCycleClass (V := V) (H := H) (p := p) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) =
      kernelAction H.analytification P kappa (2 * p)
        (GeometricCycleClass (V := V) (H := H) (p := p) pt
          (codimensionPointCycle V.X p x)) := by
  rw [cycleClassFromPointGeometry_point]
  exact (I.kernelAction_point x).symm

#check PointCylinderPullbackLaw
#check KernelFiberIntersectionLaw
#check ProperProjectionFiberLaw
#check GeometricIncidencePrimitives
#check GeometricIncidencePrimitives.kernel_cup_pointPullback
#check GeometricIncidencePrimitives.kernelAction_point
#check GeometricIncidencePrimitives.geometric_cycleClass_point_natural

#print axioms GeometricIncidencePrimitives.kernelAction_point
#print axioms GeometricIncidencePrimitives.geometric_cycleClass_point_natural

end GeometricIncidencePrimitives

end GSTClassicalHodgeCycleClassIntersectionPrimitives
