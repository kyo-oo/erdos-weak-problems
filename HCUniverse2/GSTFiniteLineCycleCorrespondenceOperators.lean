import Mathlib
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTFiniteLineCycleCorrespondenceAction
/- SPLIT PIECE of GSTFiniteLineCycleCorrespondence.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

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

set_option maxHeartbeats 2000000
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
/-! ## §3 The two M-cycle letters (GATE-L, wave 7-A)

The two genuine realized closed correspondences of the M-cycle endomorphism,
stated at the GATE-FORM analytification (`finiteLineAnalytificationOfGate`,
whose space `finiteLineSpace M` is definitionally `TopCat.of (sphereUnionSpace
M)` — GSTFiniteLineAnalytification.lean:111-112, the space receipt :423-426
an `rfl`): at this analytification every type-level transport between the
world's `RationalSingularCohomology` and the raw sphere-union's
`singularCohomologyOf` is definitional (the delta chain
`finiteLineAnalytificationOfGate` → the record's `space` field →
`finiteLineSpace` → `TopCat.of`), so the letter operators ARE the green
corpus operators, definitionally:

* **the weight-one letter** `finiteLineCycleLetterOne` — its cohomology
  operator IS `cohomologyPullbackOf (sphereCycle M) 2` (the M-cycle
  pullback at the live degree, GSTSingularCohomologyMaps.lean:133-135),
  the rotation equation rides the green derived letter equation
  `spherePointClassWorld_rotate_of_pullback`
  (GSTPositiveDimensionalLawLanding.lean:148-161) through the definitional
  transport receipt, and the pointwise realization rides the graph
  machinery (`graphCorrespondence_nativePointImage_eq`,
  GSTClassicalHodgeFiniteClosedCorrespondenceOperator.lean:191-198) with
  §1's residue-weight-one and §2b's coheight preservation feeding
  `nativePointPushforward_eq` (GSTClassicalHodgeProjectivePointTransport
  .lean:141-151), the honest atom formula at weight one
  (GSTFiniteLineHonestHodgeData.lean:170-193), L6's component-index
  rotation (:508-536), and the honest world bridge
  `honest_pointClass_eq_world` (:255-265);

* **the weight-zero letter** `finiteLineCycleLetterZero` — its cohomology
  operator is the component-iso index shift (the component H⁰ machine
  `componentCohomologyZeroEquivFinM`,
  GSTComponentCohomologyZero.lean:500-506, precomposed with the cyclic
  successor — the degree-0 rotation is pure linear algebra, no cohomology
  machinery: the singleton-vector rotation `Pi.single j ↦ Pi.single
  (cyclicPred j)` closes by `cyclicSucc_cyclicPred`/
  `cyclicPred_cyclicSucc`), the pointwise realization rides the same
  graph-pushforward chain with the honest atom formula at weight zero
  (:120-140), L3's generic-point action (:378-383) read through
  `lineIndexOfGeneric_spec` (GSTFiniteLinePointAlgebra.lean:1321-1324),
  and the honest world bridge `honest_componentClass_eq_world` (:241-252).

The letters are gate-formed: `FiniteLinePointsGate M`
(GSTFiniteLineAnalytification.lean:403-404) stays a parameter — the frozen
architecture's own discipline (the unconditional
`finiteLineAnalytification` name stays reserved for the gate-discharge
wave; the letters need ONLY the gate-form's space, which is
definitionally the sphere-union regardless of the gate's content).

Honesty ledger: every statement is proved unconditionally given the gate
parameter.  No `sorry`, no new axioms, no `native_decide`.  The GitHub CI
lane `gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

/-! ## §3a The weight-one operator and its rotation -/

/-- **THE DEFEQ RECEIPT** — at the gate form, the world's degree-two
rational singular cohomology IS the raw sphere-union's (the delta chain:
the record's `space` field is `finiteLineSpace M`, which is
`TopCat.of (sphereUnionSpace M)`; `RationalSingularCohomology` is
abbrev-transparent to `singularCohomologyOf A.space` — the `rfl` at
GSTSingularCohomologyMaps.lean:79-81).  THE designated CI repair point of
§3: if the elaborator stalls on any §3 unification, this receipt is the
contract every other proof rides. -/
theorem finiteLineGate_cohomology_two_defeq (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 =
      singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 := by
  rw [← singularCohomologyOf_eq (finiteLineAnalytificationOfGate M gate) 2,
    finiteLineAnalytificationOfGate_space M gate]

/-- **THE WEIGHT-ONE LETTER OPERATOR** — the M-cycle pullback at the live
degree, definitionally: at the gate-form analytification the operator's
declared type (the world's `RationalSingularCohomology`) unifies with the
pullback's own type (the sphere-union's `singularCohomologyOf`) by the
delta chain of `finiteLineGate_cohomology_two_defeq`. -/
noncomputable def finiteLineCycleLetterOpOne (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 →ₗ[ℚ]
      RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 :=
  cohomologyPullbackOf (sphereCycle M) 2

/-- **THE TRANSPORT RECEIPT** — the operator applied at a
`sphereUnionCoe`-transported value is the transport of the pullback's
value: at the gate form the cast transports ride `rfl`-provable type
equalities (the space receipt :423-426 is `rfl`), so the equation is
definitional.  This is exactly the `hRop` hypothesis the green derived
letter equation consumes. -/
theorem finiteLineCycleLetterOpOne_transport (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (u : singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2) :
    finiteLineCycleLetterOpOne M gate
        (sphereUnionCoe (V := finiteLineWorld M)
          (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
            (finiteLineAnalytificationOfGate_space M gate) ω)
          M (finiteLineAnalytificationOfGate_space M gate) u) =
      sphereUnionCoe (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (finiteLineAnalytificationOfGate_space M gate)
        ((cohomologyPullbackOf (sphereCycle M) 2) u) := by
  unfold sphereUnionCoe
  rw [show rationalSingularCohomology_two_eq M (finiteLineAnalytificationOfGate_space M gate)
        = (rfl : RationalSingularCohomology (finiteLineHodgeDataHonest M
            (finiteLineAnalytificationOfGate M gate)
            (finiteLineAnalytificationOfGate_space M gate) ω).analytification 2 =
            singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2) from
      rfl]
  rfl

/-- **THE WEIGHT-ONE ROTATION** — the operator rotates the honest world
point-class family by the cyclic predecessor: the green derived letter
equation (`spherePointClassWorld_rotate_of_pullback`, whose proof is
`cycle_pointClass` — GSTSphereUnionPointClassGate.lean:140-148 — consumed
through the transport receipt). -/
theorem finiteLineCycleLetterOpOne_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    finiteLineCycleLetterOpOne M gate
      (spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (finiteLineAnalytificationOfGate_space M gate) ω j) =
    spherePointClassWorld (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (finiteLineAnalytificationOfGate_space M gate) ω (cyclicPred M j) := by
  have h1 := finiteLineCycleLetterOpOne_transport M gate ω (spherePointClass M ω j)
  rw [cycle_pointClass M ω j] at h1
  exact h1

/-! ## §3b The weight-zero operator and its rotation -/

/-- **THE INDEX-SHIFT OPERATOR** — the precomposition with the cyclic
successor on the free rank-M function space (the degree-0 rotation as
pure linear algebra). -/
noncomputable def finiteLineCyclePrecompSucc (M : ℕ) [NeZero M] :
    (Fin M → ℚ) →ₗ[ℚ] (Fin M → ℚ) where
  toFun := fun v k => v (cyclicSucc M k)
  map_add' := by
    intro v w
    funext k
    show (v + w) (cyclicSucc M k) =
      v (cyclicSucc M k) + w (cyclicSucc M k)
    rfl
  map_smul' := by
    intro q v
    funext k
    show (q • v) (cyclicSucc M k) = q • v (cyclicSucc M k)
    rfl

/-- **THE SINGLETON ROTATION** — the index-shift operator carries the
j-th indicator vector to the `cyclicPred j`-th one (the two if-conditions
are the same equation: `cyclicSucc k = j` iff `k = cyclicPred j`, by the
green successor/predecessor roundtrips). -/
theorem finiteLineCyclePrecompSucc_single (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCyclePrecompSucc M (Pi.single j (1 : ℚ)) =
      Pi.single (cyclicPred M j) (1 : ℚ) := by
  have hcoe : ∀ (v : Fin M → ℚ) (k : Fin M),
      ⇑(finiteLineCyclePrecompSucc M) v k = v (cyclicSucc M k) :=
    fun _ _ => rfl
  funext k
  rw [hcoe (Pi.single j (1 : ℚ)) k, Pi.single_apply, Pi.single_apply]
  by_cases hk : cyclicSucc M k = j
  · rw [if_pos hk]
    have hk' : k = cyclicPred M j := by
      have h := congrArg (cyclicPred M) hk
      rwa [cyclicPred_cyclicSucc M k] at h
    rw [if_pos hk']
  · rw [if_neg hk, if_neg (fun hcon =>
      hk (by rw [hcon, cyclicSucc_cyclicPred M j]))]

/-- **THE WEIGHT-ZERO LETTER OPERATOR** — the component-iso conjugate of
the index shift: through the component H⁰ machine, conjugate by the
degree-zero iso, the operator is the precomposition with the cyclic
successor (the honest degree-0 action of the M-cycle). -/
noncomputable def finiteLineCycleLetterOpZero (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 0 →ₗ[ℚ]
      RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 0 :=
  { toFun := fun u =>
      (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
        (finiteLineCyclePrecompSucc M
          ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
            (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))) u))
    map_add' := by
      intro u v
      show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
          (finiteLineCyclePrecompSucc M
            ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
              (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
              (u + v))) = _ + _
      rw [LinearEquiv.map_add, LinearMap.map_add, LinearEquiv.map_add]
    map_smul' := by
      intro q u
      show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
          (finiteLineCyclePrecompSucc M
            ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
              (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
              (q • u))) = _
      rw [LinearEquiv.map_smul, LinearMap.map_smul, LinearEquiv.map_smul]
      rfl }

/-- **THE WEIGHT-ZERO ROTATION** — the operator rotates the honest world
component-class family by the cyclic predecessor: the component-class
family IS the component iso's inverse of the indicator vectors
(definitionally — `sphereComponentClass`,
GSTPositiveDimensionalLawLanding.lean:168-173, whose `H`-dependence is
only through `H.analytification`, definitionally the gate form here),
the operator conjugates the indicator rotation, and the singleton
rotation is `finiteLineCyclePrecompSucc_single`. -/
theorem finiteLineCycleLetterOpZero_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    finiteLineCycleLetterOpZero M gate
      (sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j) =
    sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate)
        (cyclicPred M j) := by
  have hEq : sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j =
      (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
        (Pi.single j (1 : ℚ)) := rfl
  show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
      (finiteLineCyclePrecompSucc M
        ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
          (sphereComponentClass (V := finiteLineWorld M)
            (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
              (finiteLineAnalytificationOfGate_space M gate) ω)
            M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j))) = _
  rw [hEq, LinearEquiv.apply_symm_apply, finiteLineCyclePrecompSucc_single M j]
  rfl


end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
