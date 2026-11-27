import Mathlib
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTFiniteLineCycleCorrespondenceOperators

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GATE-L — THE TWO M-CYCLE LETTERS (wave 4-C)

The M-cycle automorphism's graphs as genuine realized closed
correspondences on the honest Hodge data:

* the residue-degree receipt — the M-cycle is an isomorphism, so its
  residue field maps are bijective (the composition roundtrips through
  `residueFieldMap_id`/`residueFieldMap_comp`), and the residue weight is
  one (the green finrank pattern of the finite-point lane);
* the point-action receipt — the M-cycle acts on the generic points by
  `cyclicPred` (the comap of the graded rotation permutes the block
  ideals);
* the two letters `finiteLineCycleLetterOne` (weight one) and
  `finiteLineCycleLetterZero` (weight zero): the graph correspondence of the
  M-cycle endomorphism with the transported sphere-cycle pullback (letter one)/the
  component-iso conjugate of the index shift (letter zero) as the
  cohomological operator, rotating the honest point/component families.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000
set_option trace.profiler true

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineOverBase
open GSTFiniteLineGeneralMLaw
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTComponentCohomologyZero
open GSTFiniteLineAnalytification

namespace GSTFiniteLineCycleCorrespondence
/-! ## §3c The weight-one letter -/

/-- **THE WEIGHT-ONE M-CYCLE LETTER** — the graph correspondence of the
M-cycle endomorphism (the geometry: the graph, a closed immersion with
singleton left fibers — GSTClassicalHodgeFiniteClosedCorrespondence
.lean:231-244) with the M-cycle pullback as the cohomological operator,
realized on points: the class of the graph's native image of any closed
point is the pullback of the point's class.  The realization chain: the
graph's native image is the native point pushforward
(`graphCorrespondence_nativePointImage_eq`); the pushforward of a
codimension-one point under the cycle is its image atom (§1's residue
weight one + §2b's coheight preservation inside
`nativePointPushforward_eq`); the honest atom formula at weight one
evaluates the image atom's class as the point class of its line; L6
rotates the line index; the world bridge lands the honest family; on the
other side, the same atom formula and bridge evaluate the source point's
class, and the operator's rotation
(`finiteLineCycleLetterOpOne_rotate`) closes the equation. -/
noncomputable def finiteLineCycleLetterOne (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) 1 where
  geometry := FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)
  cohomologyOperator := finiteLineCycleLetterOpOne M gate
  realizes_on_points := by
    intro x
    -- the coheight of the image (L5 + the packaging's own proof)
    have hco : Order.coheight ((finiteLineCycle M) x.1) = 1 :=
      (finiteLineCycle_coheight M x.1).trans x.2
    -- the graph's native image is the pushforward, then the image atom
    have himg : (FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 1 x =
        nativePointPushforward (finiteLineCycle M) 1 x :=
      FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq
        (finiteLineCycleEndo M) 1 x
    have hpush : nativePointPushforward (finiteLineCycle M) 1 x =
        pointResidueWeight (finiteLineCycle M) x.1 •
          codimensionPointCycle (finiteLineWorld M).X 1 ⟨(finiteLineCycle M) x.1, hco⟩ :=
      nativePointPushforward_eq (finiteLineCycle M) 1 x hco
    have hw : pointResidueWeight (finiteLineCycle M) x.1 = 1 :=
      finiteLineCycle_pointResidueWeight M x.1
    -- the honest atom formulas at the image and at the source
    have hatomImg := honestCycleClassOne_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      ⟨(finiteLineCycle M) x.1, hco⟩
    have hatom := honestCycleClassOne_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω x
    -- L6: the image's line index is the predecessor of the source's
    have hidx := finiteLineCycle_componentIndex M x
    -- the honest world bridges at both indices
    have hbridgeImg := honest_pointClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)))
    have hbridge := honest_pointClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (lineIndexOfGeneric M (lineComponentOf M x))
    -- the operator's rotation at the source's index
    have hrot := finiteLineCycleLetterOpOne_rotate M gate ω
      (lineIndexOfGeneric M (lineComponentOf M x))
    -- the goal, restated at the honest data's unfolded cycle-class maps
    show honestCycleClassOne M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω
        ((FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 1 x) =
      finiteLineCycleLetterOpOne M gate
        (honestCycleClassOne M (finiteLineWorld M)
          (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω
          (codimensionPointCycle (finiteLineWorld M).X 1 x))
    simp only [himg, hpush, hw, one_smul, hatomImg, hidx, hbridgeImg, hatom,
      hbridge, hrot]
    exact (congrArg (fun i => finiteLinePointClass M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω i) hidx).trans hbridgeImg

/-! ## §3d The weight-zero letter -/

/-- **THE WEIGHT-ZERO M-CYCLE LETTER** — the graph correspondence of the
M-cycle endomorphism with the component-iso index shift as the
cohomological operator, realized on points: the class of the graph's
native image of any generic point is the operator's value at the point's
class.  The realization chain mirrors the weight-one letter's: the graph
pushforward and the residue weight reduce the image to the image atom;
the honest atom formula at weight zero evaluates it as the component
class of its line; L3's generic-point action (read through
`lineIndexOfGeneric_spec`) rotates the line index; the world bridge and
the operator's rotation (`finiteLineCycleLetterOpZero_rotate`) close the
equation on the other side. -/
noncomputable def finiteLineCycleLetterZero (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) 0 where
  geometry := FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)
  cohomologyOperator := finiteLineCycleLetterOpZero M gate
  realizes_on_points := by
    intro η
    -- the coheight of the image (L5 + the packaging's own proof)
    have hco : Order.coheight ((finiteLineCycle M) η.1) = 0 :=
      (finiteLineCycle_coheight M η.1).trans η.2
    -- the graph's native image is the pushforward, then the image atom
    have himg : (FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 0 η =
        nativePointPushforward (finiteLineCycle M) 0 η :=
      FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq
        (finiteLineCycleEndo M) 0 η
    have hpush : nativePointPushforward (finiteLineCycle M) 0 η =
        pointResidueWeight (finiteLineCycle M) η.1 •
          codimensionPointCycle (finiteLineWorld M).X 0 ⟨(finiteLineCycle M) η.1, hco⟩ :=
      nativePointPushforward_eq (finiteLineCycle M) 0 η hco
    have hw : pointResidueWeight (finiteLineCycle M) η.1 = 1 :=
      finiteLineCycle_pointResidueWeight M η.1
    -- the honest atom formulas at the image and at the source
    have hatomImg := honestCycleClassZero_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate)
      ⟨(finiteLineCycle M) η.1, hco⟩
    have hatom := honestCycleClassZero_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) η
    -- L3 read through the spec: the image's line index is the
    -- predecessor of the source's
    have hspecImg := lineIndexOfGeneric_spec M
      ⟨(finiteLineCycle M) η.1, hco⟩
    have hspec := lineIndexOfGeneric_spec M η
    have hpt : (finiteLineCycle M) η.1 =
        lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M η)) := by
      rw [← hspec]
      exact finiteLineCycle_genericPoint M (lineIndexOfGeneric M η)
    have hidx : lineIndexOfGeneric M
        ⟨(finiteLineCycle M) η.1, hco⟩ =
        cyclicPred M (lineIndexOfGeneric M η) :=
      lineGenericPoint_injective M (hspecImg.trans hpt)
    -- the honest world bridges at both indices
    have hbridgeImg := honest_componentClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (cyclicPred M (lineIndexOfGeneric M η))
    have hbridge := honest_componentClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (lineIndexOfGeneric M η)
    -- the operator's rotation at the source's index
    have hrot := finiteLineCycleLetterOpZero_rotate M gate ω
      (lineIndexOfGeneric M η)
    -- the goal, restated at the honest data's unfolded cycle-class maps
    show honestCycleClassZero M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate)
        ((FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 0 η) =
      finiteLineCycleLetterOpZero M gate
        (honestCycleClassZero M (finiteLineWorld M)
          (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate)
          (codimensionPointCycle (finiteLineWorld M).X 0 η))
    simp only [himg, hpush, hw, one_smul, hatomImg, hidx, hbridgeImg, hatom,
      hbridge, hrot]
    exact (congrArg (fun i => finiteLineComponentClass M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) i) hidx).trans hbridgeImg

/-! ## §3e The rotation equations in the engine's spelling -/

/-- **THE WEIGHT-ONE ROTATION, LETTER-SPELLED** — the letter's own
cohomology operator rotates the world point-class family by the cyclic
predecessor (the engine's `hR₁` form: the field projection is
definitionally the operator). -/
theorem finiteLineCycleLetterOne_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    (finiteLineCycleLetterOne M gate ω).cohomologyOperator
      (spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (finiteLineAnalytificationOfGate_space M gate) ω j) =
    spherePointClassWorld (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (finiteLineAnalytificationOfGate_space M gate) ω (cyclicPred M j) :=
  finiteLineCycleLetterOpOne_rotate M gate ω j

/-- **THE WEIGHT-ZERO ROTATION, LETTER-SPELLED** — the letter's own
cohomology operator rotates the world component-class family by the
cyclic predecessor (the engine's `hR₀` form). -/
theorem finiteLineCycleLetterZero_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    (finiteLineCycleLetterZero M gate ω).cohomologyOperator
      (sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j) =
    sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate)
        (cyclicPred M j) :=
  finiteLineCycleLetterOpZero_rotate M gate ω j

/-! ## §3 Receipts -/

#check finiteLineGate_cohomology_two_defeq
#check finiteLineCycleLetterOpOne
#check finiteLineCycleLetterOpOne_transport
#check finiteLineCycleLetterOpOne_rotate
#check finiteLineCycleLetterOne
#check finiteLineCycleLetterOne_rotate
#check finiteLineCyclePrecompSucc
#check finiteLineCyclePrecompSucc_single
#check finiteLineCycleLetterOpZero
#check finiteLineCycleLetterOpZero_rotate
#check finiteLineCycleLetterZero
#check finiteLineCycleLetterZero_rotate

#print axioms finiteLineCycleLetterOpOne_rotate
#print axioms finiteLineCycleLetterOne
#print axioms finiteLineCycleLetterZero
#print axioms finiteLineCycleLetterOne_rotate
#print axioms finiteLineCycleLetterZero_rotate

end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
