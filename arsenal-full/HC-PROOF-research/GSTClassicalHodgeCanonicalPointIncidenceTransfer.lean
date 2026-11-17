import GSTClassicalHodgeCanonicalIncidenceKernelReduction
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — CANONICAL POINT INCIDENCE TRANSFER

For correspondence naturality relative to the currently supplied Stage-2G
cycle-class map, a separate point-Betti-class witness is unnecessary.  The
canonical point class is simply the cycle class of the genuine point atom.
Its compatibility equation is definitional.

This does NOT claim that the supplied Stage-2G map has already been identified
with an independently constructed geometric fundamental-class theory.  That
stronger identification is exactly the semantic rigidity law required to rule
out the zero-map copy.  The purpose here is narrower: remove an unnecessary
parameter from the correspondence-transfer frontier and expose the single
pointwise incidence equation actually consumed.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalPointIncidenceTransfer

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
open GSTClassicalHodgeCanonicalIncidenceKernelReduction
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- Canonical point-class assignment attached to the currently supplied
Stage-2G cycle class. -/
noncomputable def suppliedPointBettiClass :
    PointBettiClass (V := V) p H.analytification :=
  fun x => H.cycleClass p (codimensionPointCycle V.X p x)

@[simp]
theorem suppliedPointBettiClass_apply
    (x : CodimensionPoint V.X p) :
    suppliedPointBettiClass (V := V) (H := H) (p := p) x =
      H.cycleClass p (codimensionPointCycle V.X p x) := rfl

/-- The point-compatibility theorem needed by point rigidity is now
canonical. -/
theorem suppliedPointBettiClass_compatibility
    (x : CodimensionPoint V.X p) :
    H.cycleClass p (codimensionPointCycle V.X p x) =
      suppliedPointBettiClass (V := V) (H := H) (p := p) x := rfl

/-- Reconstructing cycle class from its own point values recovers the supplied
map exactly. -/
theorem suppliedCycleClass_eq_from_own_points :
    H.cycleClass p =
      cycleClassFromPointGeometry (V := V) p H.analytification
        (suppliedPointBettiClass (V := V) (H := H) (p := p)) := by
  exact suppliedCycleClass_eq_geometric
    (V := V) p H
    (suppliedPointBettiClass (V := V) (H := H) (p := p))
    suppliedPointBettiClass_compatibility

/-- Direct incidence law with no independently supplied point-class witness. -/
def SuppliedPointDirectIncidenceLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K) : Prop :=
  DirectIncidenceProjectionLaw
    (V := V) (H := H) (d := d) (p := p)
    P K κ (suppliedPointBettiClass (V := V) (H := H) (p := p))

/-- Expanded form: the single substantive point equation is exactly that the
ambient kernel formula on a genuine point cycle class equals the supplied
cycle class of the actual finite incidence image. -/
theorem suppliedPointDirectIncidenceLaw_iff
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K) :
    SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ ↔
    (∀ x : CodimensionPoint V.X p,
      P.gysinTheory.sndGysin (2 * p)
        (P.cupTheory.cup (2 * d) (2 * p) κ.kernelClass
          (fstCohomologyPullback H.analytification (2 * p)
            (H.cycleClass p (codimensionPointCycle V.X p x)))) =
        H.cycleClass p
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.nativePointImage p x)) := by
  have hclass : H.cycleClass p =
      cycleClassFromPointGeometry (V := V) p H.analytification
        (suppliedPointBettiClass (V := V) (H := H) (p := p)) :=
    suppliedCycleClass_eq_from_own_points
  constructor
  · intro h x
    have hx := h x
    have hpt : suppliedPointBettiClass (V := V) (H := H) (p := p) x =
        H.cycleClass p (codimensionPointCycle V.X p x) := rfl
    have hgeo : GSTClassicalHodgeCanonicalIncidenceKernelReduction.GeometricCycleClass (V := V) (H := H) (p := p)
        (suppliedPointBettiClass (V := V) (H := H) (p := p))
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) =
      H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) := by rw [hclass]
    rw [hpt, hgeo] at hx
    exact hx
  · intro h x
    have hpt : suppliedPointBettiClass (V := V) (H := H) (p := p) x =
        H.cycleClass p (codimensionPointCycle V.X p x) := rfl
    have hgeo : GSTClassicalHodgeCanonicalIncidenceKernelReduction.GeometricCycleClass (V := V) (H := H) (p := p)
        (suppliedPointBettiClass (V := V) (H := H) (p := p))
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) =
      H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativePointImage p x) := by rw [hclass]
    rw [hpt, hgeo]
    exact h x

/-- The canonical direct law manufactures the complete old incidence packet
without a point-class parameter or point-identification premise. -/
noncomputable def geometricIncidenceOfSuppliedPointDirectLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (h : SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ) :
    GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p)
      P K κ (suppliedPointBettiClass (V := V) (H := H) (p := p)) :=
  geometricIncidencePrimitivesOfDirectLaw
    P K κ (suppliedPointBettiClass (V := V) (H := H) (p := p)) h

/-- **GLOBAL TRANSFER FROM THE ONE CANONICAL POINT LAW.** -/
theorem supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (h : SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      kernelAction H.analytification P κ (2 * p)
        (H.cycleClass p Z) := by
  exact supplied_cycleClass_nativeOperator_of_directLaw
    P K κ
    (suppliedPointBettiClass (V := V) (H := H) (p := p))
    suppliedPointBettiClass_compatibility h Z

/-- The single point-incidence law is exactly the pointwise realization
predicate consumed by the finite-closed-correspondence operator engine. -/
theorem suppliedPointDirectLaw_implies_realizesOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (h : SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
      |>.RealizesAmbientOnPoints
        (H := H) (kernelAction H.analytification P κ (2 * p)) := by
  intro x
  have hx := supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
    P K κ h (codimensionPointCycle V.X p x)
  rw [K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
    |>.nativeOperator_point p x] at hx
  exact hx

#check suppliedPointBettiClass
#check suppliedCycleClass_eq_from_own_points
#check SuppliedPointDirectIncidenceLaw
#check suppliedPointDirectIncidenceLaw_iff
#check geometricIncidenceOfSuppliedPointDirectLaw
#check supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
#check suppliedPointDirectLaw_implies_realizesOnPoints

#print axioms suppliedCycleClass_eq_from_own_points
#print axioms suppliedPointDirectIncidenceLaw_iff
#print axioms supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
#print axioms suppliedPointDirectLaw_implies_realizesOnPoints

end GSTClassicalHodgeCanonicalPointIncidenceTransfer
