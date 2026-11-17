import GSTClassicalHodgeCanonicalPointIncidenceTransfer

/-!
# GST CLASSICAL HODGE — INCIDENCE / POINT-REALIZATION EQUIVALENCE

After canonicalizing the point class, point cylinder, intersection class, and
transpose kernel, the remaining direct incidence law is not another mysterious
axiom.  For a fixed actual correspondence kernel and fixed cup/Gysin
operations, it is EXACTLY the pointwise realization predicate used by the
finite closed-correspondence operator engine.

Thus the historical geometric-incidence packet, the direct Gysin/incidence
equation, and generatorwise cycle-class naturality are three presentations of
the same remaining low-level statement.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeIncidenceRealizationEquivalence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeAmbientIntersectionFromPrimitives
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeCycleClassIntersectionPrimitives
open GSTClassicalHodgeCanonicalIncidenceKernelReduction
open GSTClassicalHodgeCanonicalPointIncidenceTransfer

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- Generatorwise realization of the canonical ambient kernel formula implies
the direct Gysin/incidence equation simply by unfolding that formula. -/
theorem suppliedPointDirectLaw_of_realizesOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (hreal :
      K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
        |>.RealizesAmbientOnPoints
          (H := H) (kernelAction H.analytification P κ (2 * p))) :
    SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ := by
  apply (suppliedPointDirectIncidenceLaw_iff P K κ).2
  intro x
  have hx := hreal x
  simpa [kernelAction_apply] using hx.symm

/-- **DIRECT INCIDENCE = GENERATORWISE REALIZATION.** -/
theorem suppliedPointDirectLaw_iff_realizesOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K) :
    SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ ↔
    (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence).RealizesAmbientOnPoints
        (H := H) (kernelAction H.analytification P κ (2 * p)) := by
  constructor
  · exact suppliedPointDirectLaw_implies_realizesOnPoints P K κ
  · exact suppliedPointDirectLaw_of_realizesOnPoints P K κ

/-- **OLD INCIDENCE PACKET = GENERATORWISE REALIZATION.**
The historical three-layer incidence packet carries no additional logical
strength after canonicalization. -/
theorem geometricIncidencePrimitives_nonempty_iff_realizesOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K) :
    Nonempty (GeometricIncidencePrimitives
      (V := V) (H := H) (d := d) (p := p)
      P K κ
      (suppliedPointBettiClass (V := V) (H := H) (p := p))) ↔
    (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence).RealizesAmbientOnPoints
        (H := H) (kernelAction H.analytification P κ (2 * p)) := by
  rw [geometricIncidencePrimitives_nonempty_iff_directLaw]
  exact suppliedPointDirectLaw_iff_realizesOnPoints P K κ

/-- Once generatorwise realization is known, the global native/cohomology
commuting square is forced by the exact finite point normal form. -/
theorem globalTransfer_of_realizesOnPoints
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (hreal :
      K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
        |>.RealizesAmbientOnPoints
          (H := H) (kernelAction H.analytification P κ (2 * p)))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.nativeOperator p Z) =
      kernelAction H.analytification P κ (2 * p)
        (H.cycleClass p Z) := by
  exact supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
    P K κ
    (suppliedPointDirectLaw_of_realizesOnPoints P K κ hreal)
    Z

#check suppliedPointDirectLaw_of_realizesOnPoints
#check suppliedPointDirectLaw_iff_realizesOnPoints
#check geometricIncidencePrimitives_nonempty_iff_realizesOnPoints
#check globalTransfer_of_realizesOnPoints

#print axioms suppliedPointDirectLaw_iff_realizesOnPoints
#print axioms geometricIncidencePrimitives_nonempty_iff_realizesOnPoints
#print axioms globalTransfer_of_realizesOnPoints

end GSTClassicalHodgeIncidenceRealizationEquivalence
