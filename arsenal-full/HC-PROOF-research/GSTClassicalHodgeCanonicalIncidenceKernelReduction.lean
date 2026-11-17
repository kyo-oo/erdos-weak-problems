import GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — CANONICAL INCIDENCE / KERNEL REDUCTION

Several historical low-level correspondence packets stored data which were
already uniquely forced by their own equations.  This file removes those fake
degrees of freedom.

* A middle Betti kernel needs only its forward class.  The transpose class is
  canonically factor-swap pullback.
* A point cylinder needs no supplied class: it is definitionally the first
  pullback of the point class.
* A fiber intersection needs no supplied class: it is definitionally cup of
  the correspondence kernel with that point-cylinder pullback.

After those eliminations, the complete point-incidence packet is equivalent to
ONE direct geometric law: second-projection Gysin of the canonical kernel/cup
expression equals the geometrically generated cycle class of the actual finite
incidence image.

Thus the old three-layer incidence structure is reconstructed as a theorem from
one irreducible projection law.  No Hodge conclusion or target basis direction
appears anywhere in this reduction.
-/

set_option maxHeartbeats 160000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalIncidenceKernelReduction

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
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeStrictCorrespondenceTransferFromPrimitives
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- A reduced middle Betti kernel contains only the forward correspondence
class.  Factor-swap determines its transpose class uniquely. -/
structure CanonicalMiddleBettiKernel
    (A : AnalytificationData V)
    (d : Nat)
    (K : SchemeBiFiniteClosedCorrespondence V) where
  kernelClass : ProductCohomology A (2 * d)

namespace CanonicalMiddleBettiKernel

/-- Manufacture the historical kernel packet with canonical transpose class. -/
noncomputable def toMiddleBettiCorrespondenceKernel
    {A : AnalytificationData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : CanonicalMiddleBettiKernel A d K) :
    MiddleBettiCorrespondenceKernel A d K where
  kernelClass := κ.kernelClass
  transposeClass := swapCohomologyPullback A (2 * d) κ.kernelClass
  transposeClass_eq_swap := rfl

@[simp]
theorem toMiddle_class
    {A : AnalytificationData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : CanonicalMiddleBettiKernel A d K) :
    κ.toMiddleBettiCorrespondenceKernel.kernelClass = κ.kernelClass := rfl

@[simp]
theorem toMiddle_transposeClass
    {A : AnalytificationData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : CanonicalMiddleBettiKernel A d K) :
    κ.toMiddleBettiCorrespondenceKernel.transposeClass =
      swapCohomologyPullback A (2 * d) κ.kernelClass := rfl

/-- Every historical kernel forgets to the reduced packet. -/
def ofMiddle
    {A : AnalytificationData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : MiddleBettiCorrespondenceKernel A d K) :
    CanonicalMiddleBettiKernel A d K :=
  ⟨κ.kernelClass⟩

/-- Re-expansion changes no operational content: forward class is identical and
transpose class is propositionally the historical one. -/
theorem canonicalization_preserves_transpose
    {A : AnalytificationData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : MiddleBettiCorrespondenceKernel A d K) :
    (ofMiddle κ).toMiddleBettiCorrespondenceKernel.transposeClass =
      κ.transposeClass := by
  exact κ.transposeClass_eq_swap.symm

end CanonicalMiddleBettiKernel

abbrev GeometricCycleClass
    (pt : PointClass (V := V) (H := H) p) :=
  cycleClassFromPointGeometry (V := V) p H.analytification pt

/-- Canonical point-cylinder packet: there is no independent cylinder-class
choice. -/
noncomputable def canonicalPointCylinder
    (pt : PointClass (V := V) (H := H) p) :
    PointCylinderPullbackLaw (V := V) (H := H) (p := p) pt where
  pointCylinderClass := fun x =>
    fstCohomologyPullback H.analytification (2 * p) (pt x)
  class_eq_fstPullback := by
    intro x
    rfl

/-- Canonical fiber-intersection packet: there is no independent intersection
class choice once cup and the kernel class are fixed. -/
noncomputable def canonicalKernelFiberIntersection
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    {K : SchemeBiFiniteClosedCorrespondence V}
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p) :
    KernelFiberIntersectionLaw
      (V := V) (H := H) (d := d) (p := p)
      P κ (canonicalPointCylinder pt) where
  fiberIntersectionClass := fun x =>
    P.cupTheory.cup (2 * d) (2 * p) κ.kernelClass
      (fstCohomologyPullback H.analytification (2 * p) (pt x))
  class_eq_kernel_cup_cylinder := by
    intro x
    rfl

/-- The one irreducible point-incidence equation left after canonicalizing the
intermediate witnesses. -/
def DirectIncidenceProjectionLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    P.gysinTheory.sndGysin (2 * p)
      (P.cupTheory.cup (2 * d) (2 * p) κ.kernelClass
        (fstCohomologyPullback H.analytification (2 * p) (pt x))) =
      GeometricCycleClass (V := V) (H := H) (p := p) pt
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x)

/-- The direct law manufactures the full historical three-layer incidence
packet with both intermediate classes canonically chosen. -/
noncomputable def geometricIncidencePrimitivesOfDirectLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p)
    (h : DirectIncidenceProjectionLaw
      (V := V) (H := H) (d := d) (p := p) P K κ pt) :
    GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K κ pt := by
  let Cyl := canonicalPointCylinder (V := V) (H := H) (p := p) pt
  let Int := canonicalKernelFiberIntersection
    (V := V) (H := H) (d := d) (p := p) P κ pt
  exact {
    cylinder := Cyl
    intersection := Int
    projection := {
      gysin_class := by
        intro x
        exact h x
    }
  }

/-- Any historical incidence packet implies the canonical direct law; its
stored cylinder/intersection witnesses disappear from the statement. -/
theorem directLaw_of_geometricIncidencePrimitives
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p)
    (I : GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K κ pt) :
    DirectIncidenceProjectionLaw
      (V := V) (H := H) (d := d) (p := p) P K κ pt := by
  intro x
  have hcup := I.kernel_cup_pointPullback x
  have hproj := I.projection.gysin_class x
  rw [hcup]
  exact hproj

/-- **EXACT INCIDENCE AXIOM REDUCTION.**
The old `GeometricIncidencePrimitives` packet exists iff the single canonical
direct projection law holds. -/
theorem geometricIncidencePrimitives_nonempty_iff_directLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p) :
    Nonempty (GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p) P K κ pt) ↔
      DirectIncidenceProjectionLaw
        (V := V) (H := H) (d := d) (p := p) P K κ pt := by
  constructor
  · rintro ⟨I⟩
    exact directLaw_of_geometricIncidencePrimitives P K κ pt I
  · intro h
    exact ⟨geometricIncidencePrimitivesOfDirectLaw P K κ pt h⟩

/-- The global strict correspondence transfer follows directly from the single
canonical incidence projection law; the historical intermediate witness
structures are reconstructed internally. -/
theorem supplied_cycleClass_nativeOperator_of_directLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (pt : PointClass (V := V) (H := H) p)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (h : DirectIncidenceProjectionLaw
      (V := V) (H := H) (d := d) (p := p) P K κ pt)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      kernelAction H.analytification P κ (2 * p)
        (H.cycleClass p Z) := by
  exact supplied_cycleClass_nativeOperator
    P K κ pt hpoint
    (geometricIncidencePrimitivesOfDirectLaw P K κ pt h) Z

#check CanonicalMiddleBettiKernel
#check CanonicalMiddleBettiKernel.toMiddleBettiCorrespondenceKernel
#check canonicalPointCylinder
#check canonicalKernelFiberIntersection
#check DirectIncidenceProjectionLaw
#check geometricIncidencePrimitivesOfDirectLaw
#check geometricIncidencePrimitives_nonempty_iff_directLaw
#check supplied_cycleClass_nativeOperator_of_directLaw

#print axioms CanonicalMiddleBettiKernel.toMiddleBettiCorrespondenceKernel
#print axioms geometricIncidencePrimitives_nonempty_iff_directLaw
#print axioms supplied_cycleClass_nativeOperator_of_directLaw

end GSTClassicalHodgeCanonicalIncidenceKernelReduction
