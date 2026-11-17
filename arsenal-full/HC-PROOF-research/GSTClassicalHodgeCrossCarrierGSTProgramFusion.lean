import GSTClassicalHodgeCrossCarrierObstruction
import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgeNativeExecutablePlane

/-!
# Cross-carrier realization of the ACTUAL GST graded program engine

This formalizes the fusion between the pre-existing exact projective
correspondence/cut program language and the new geometric transport
between distinct algebraic carriers.

It works with EXISTING `GradedCycleClassOperatorPair` and
`GradedCorrespondenceProgram` objects.  This is not an independent toy
algebra replacing HC-PROOF's geometry: the native and Betti operators of an
existing GST geometric program become the two sides of a cross-carrier
natural transformation.

With any genuine incoming/outgoing geometric correspondences, a full
surface/CM/Gale -> GST cuts/correspondences -> Hodge destination
three-stage program is constructed by composition, and its naturality
equation follows from the primitive squares.

No existence of the incoming/outgoing correspondences is assumed
globally, and no universal Hodge algebraicity is asserted.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 12000000
set_option maxRecDepth 500000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeNativeExecutablePlane

namespace GSTClassicalHodgeCrossCarrierGSTProgramFusion

variable {V S T : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {D : HodgeBigradedBettiData S}
variable {J : HodgeBigradedBettiData T}
variable {p q s r : Nat}

/-- Every existing genuinely realized GST graded cycle/cohomology pair
instantiates the new cross-carrier square on one underlying variety,
with possibly DIFFERENT input/output codimensions. -/
noncomputable def crossCarrierOfGradedPair
    (R : GradedCycleClassOperatorPair V H p q) :
    CrossCarrierTransfer V V H H p q where
  native := R.cycleOperator
  betti := R.cohomologyOperator
  naturality := R.cycleClass_natural

/-- Full existing GST geometric programs are executable morphisms in the
new cross-carrier cycle/Betti correspondence calculus. -/
noncomputable def crossCarrierOfGSTProgram
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q) :
    CrossCarrierTransfer V V H H p q :=
  crossCarrierOfGradedPair (P.toPair G)

@[simp]
theorem crossCarrierOfGSTProgram_native
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q) :
    (crossCarrierOfGSTProgram G P).native = P.cycleEval G := rfl

@[simp]
theorem crossCarrierOfGSTProgram_betti
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q) :
    (crossCarrierOfGSTProgram G P).betti = P.cohomologyEval G := rfl

/-- Exact naturality of an original GST correspondence/cut program,
now expressed in the common multicarrier interface. -/
theorem crossCarrierOfGSTProgram_naturality
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q)
    (Z : codimensionCycles V.X p) :
    H.cycleClass q ((crossCarrierOfGSTProgram G P).native Z) =
      (crossCarrierOfGSTProgram G P).betti (H.cycleClass p Z) :=
  (crossCarrierOfGSTProgram G P).naturality Z

/-- Splice in a REAL incoming cycle correspondence from an auxiliary
algebraic variety before a GST cut/correspondence program. -/
noncomputable def incomingGeometricGSTProgram
    (R : CrossCarrierTransfer S V D H s p)
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q) :
    CrossCarrierTransfer S V D H s q :=
  (crossCarrierOfGSTProgram G P).compose R

/-- Insert an outgoing geometric map to a THIRD algebraic variety after
the entire native GST correspondence/cut program. -/
noncomputable def fullGeometricCarrierSandwich
    (R : CrossCarrierTransfer S V D H s p)
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q)
    (Tmap : CrossCarrierTransfer V T H J q r) :
    CrossCarrierTransfer S T D J s r :=
  Tmap.compose (incomingGeometricGSTProgram R G P)

/-- FULL THREE-STAGE BETTI AND NATIVE NATURALITY.
The source native cycle is geometrically transported to the final
target cycle after auxiliary -> GST -> target composition.  Nothing is
postulated about the image: the final witness is the explicit native
cycle computed by the composite transport. -/
theorem fullGeometricCarrierSandwich_naturality
    (R : CrossCarrierTransfer S V D H s p)
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q)
    (Tmap : CrossCarrierTransfer V T H J q r)
    (Z : codimensionCycles S.X s) :
    J.cycleClass r
      ((fullGeometricCarrierSandwich R G P Tmap).native Z) =
      Tmap.betti (P.cohomologyEval G (R.betti (D.cycleClass s Z))) := by
  exact (fullGeometricCarrierSandwich R G P Tmap).naturality Z

/-- The native output of any three-stage genuine geometric program
necessarily has a rational algebraic-cycle representative on the
destination.  This is an unconditional CONSEQUENCE of the supplied
actual geometry, not Hodge surjectivity. -/
theorem sandwich_output_algebraic
    (R : CrossCarrierTransfer S V D H s p)
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q)
    (Tmap : CrossCarrierTransfer V T H J q r)
    (Z : codimensionCycles S.X s) :
    Tmap.betti (P.cohomologyEval G (R.betti (D.cycleClass s Z))) ∈
      LinearMap.range (J.cycleClass r) := by
  refine ⟨(fullGeometricCarrierSandwich R G P Tmap).native Z, ?_⟩
  exact fullGeometricCarrierSandwich_naturality R G P Tmap Z

/-- The true geometric sandwich can reach a prescribed destination Hodge
vector when a NONZERO period identity is proved. Its normalized native
cycle is then an actual algebraic cycle.  The period identity is stated
explicitly and must be derived from geometry, e.g. a surface-switch or
Kuga--Satake/Gale correspondence construction. -/
theorem normalized_sandwich_target
    (R : CrossCarrierTransfer S V D H s p)
    (G : GeometricCycleClassSpine V H)
    (P : GradedCorrespondenceProgram V H p q)
    (Tmap : CrossCarrierTransfer V T H J q r)
    (Z : codimensionCycles S.X s)
    (target : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber T J r)
    (k : ℚ) (hk : k ≠ 0)
    (hperiod :
      Tmap.betti (P.cohomologyEval G (R.betti (D.cycleClass s Z))) =
        k • target.1) :
    ∃ W : codimensionCycles T.X r, J.cycleClass r W = target.1 := by
  exact
    (fullGeometricCarrierSandwich R G P Tmap).native_target_of_nonzero_geometric_period
      Z target k hk hperiod

#check crossCarrierOfGSTProgram
#check fullGeometricCarrierSandwich
#check fullGeometricCarrierSandwich_naturality
#check sandwich_output_algebraic
#check normalized_sandwich_target
#print axioms sandwich_output_algebraic

end GSTClassicalHodgeCrossCarrierGSTProgramFusion
