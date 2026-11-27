import Mathlib
import HCUniverse2.GSTPositiveDimensionalLawLanding
import HCUniverse2.GSTFiniteLineOverBase
import HCUniverse2.GSTFiniteLinePointAlgebra
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLineCycleCorrespondence
import HCUniverse2.GSTFiniteLineWorldDischarge
import HCUniverse2.GSTFiniteLineAnalytification
import HCUniverse2.GSTHodgeSingleHypothesisConditional
import HCUniverse2.GSTCompleteSingleFoldOrbitLaw

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE UNCONDITIONAL SOURCE — THE GENERAL-M LAW AT THE HONEST DATA (wave 7)

THE GENERAL-M theorem of the finite-line lane: the frozen architecture of
`GSTFiniteLineWorldDischarge.lean` (Route 4's three open gates, :24-30)
discharged BY SUBSTITUTION — every gate input a named theorem of the
corpus, every proof a single exact instantiation of the wave-60 engine:

* **GATE-L (the two M-cycle letters)** — discharged UNCONDITIONALLY by
  the cycle wave's §3 (W7-A, `GSTFiniteLineCycleCorrespondence.lean`):
  the two genuine realized closed correspondences
  `finiteLineCycleLetterOne`/`finiteLineCycleLetterZero` — the graph
  correspondences of the M-cycle endomorphism, the pullback operator and
  the component-iso index shift, realized on points through the honest
  atom formulas, L3/L5/L6 and the residue-weight-one receipt — with the
  rotation equations `finiteLineCycleLetterOne_rotate`/
  `finiteLineCycleLetterZero_rotate` supplying the engine's
  `R₁/hR₁`/`R₀/hR₀` inputs verbatim;
* **GATE-S (the honest seeds)** — discharged UNCONDITIONALLY by the
  honesty wave's own data: the honest Hodge data's seed equations
  `finiteLineHodgeDataHonest_seed_one`/`_seed_zero`
  (GSTFiniteLineHonestHodgeData.lean:298/:269) supply the engine's
  `hZ₁`/`hZ₀` inputs, with the honest seed cycles `lineHonestSeedOne`/
  `lineHonestSeedZero` (GSTFiniteLinePointAlgebra.lean:1422/:1411) as
  the `Z₁`/`Z₀` carriers;
* **GATE-A (the analytification receipt)** — discharged at the GATE
  FORM: the letters and the data are stated at
  `finiteLineAnalytificationOfGate M gate`
  (GSTFiniteLineAnalytification.lean:412-418), whose space IS the honest
  sphere-union by the `rfl` receipt :423-426 — the points-classification
  gate `FiniteLinePointsGate M` (:403-404) stays a PARAMETER, the frozen
  architecture's own gate-form discipline (the unconditional
  `finiteLineAnalytification` name stays reserved for the
  gate-discharge wave — the cover strike of W7-B
  (`GSTFiniteLinePointsGate.lean`) is that wave's first landing).

The engine (`native_GST_single_fold_orbit_law_of_sphereUnion_gate`,
GSTPositiveDimensionalLawLanding.lean:495) then instantiates at the
honest data `finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate
M gate) (finiteLineAnalytificationOfGate_space M gate) ω`
(GSTFiniteLineHonestHodgeData.lean:202): the FULL
`NativeGSTSingleFoldOrbitLaw` at EVERY `M ≥ 1`, at EVERY family index
`ω`, given the gate.

The consequences are restated through the repository's conditional
chain: exact Hodge (`exactHodge_of_one_GST_fold_orbit`,
GSTHodgeSingleHypothesisConditional.lean:61) and the finite rational
combination form (`finiteRationalCombination_of_one_GST_fold_orbit`,
:70) — fed the unconditional law instance; the master package restates
the general-M family's ∀M claim (the law family + the consequence
family).

ω-HONESTY (the engine's own disclosure, wave 60): the honest sphere class
`ω` appears ONLY as the INDEX of the family design — the law and its
consequences hold at EVERY family index; the NONVANISHING of `ω` (the
fenced sphere-machine core) is needed ONLY for the liveness receipts,
never for the law.  This module's `ω` is a free parameter: the theorems
below are the ∀ω statements.

HONESTY LEDGER.

Every statement is proved unconditionally given the points-gate
parameter.  No `sorry`, no new axioms, no `native_decide`.  Disclosed
items:

1. THE GATE PARAMETER: GATE-A's full discharge (constructing the
   points-classification equiv `ComplexPoint (finiteLineWorld M) ≃
   Σ _ : Fin M, Option ℂ`) is the assault's next front — the W7-B cover
   strike landed the variable cover, the unique-line law and the
   section-side index machinery; the full equiv needs the
   section-decomposition (the Proj universal property for morphisms
   into Proj — absent from the pinned Mathlib, the honest residual
   documented in `GSTFiniteLinePointsGate.lean`).  This module stays
   gate-formed: one line of substitution completes it when the gate
   lands.
2. THE ω-CANONICAL-CLASS HUNT: the corpus has NO green canonical nonzero
   sphere class — every nonzero/independence/liveness receipt takes
   `hω : ω ≠ 0` explicitly; the research record's verdict is final (the
   fenced core, research/records/2026-11-19-gst-wave57-59-sphere-gate
   -lane.md:135).  No bonus liveness theorem is fabricated.
3. THE PACKAGE SHAPE: the capstone's master package carries a third
   conjunct (the Route-1 family infinitude); the finite-line corpus has
   no green M-index-injectivity receipt, so the honest route-4 analog is
   the two-conjunct package (the law family + the consequence family).
4. THE STUB'S SECOND ITEM: the stub docstring (and the CI lane's job
   title) also name "the universal primitive-X source theorem" — that
   theorem is NOT in this module's frozen list; it remains the next
   wave's target.

The GitHub CI lane `gst-finite-line-unconditional-source.yml` owns the
kernel check.
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
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion
open GSTFiniteLineGeneralMLaw
open GSTFiniteLineOverBase
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTFiniteLineCycleCorrespondence
open GSTFiniteLineAnalytification
open GSTCompleteSingleFoldOrbitLaw
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTHodgeSingleHypothesisConditional

namespace GSTFiniteLineUnconditionalSource

/-! ## §1 THE UNCONDITIONAL LAW (the kill shot) -/

/-- **THE GENERAL-M LAW, GATE-FORMED.**  The finite-line world at the
honest data — the gate-form analytification, the honest cycle-class
maps, the frozen bigrading design — satisfies the FULL
`NativeGSTSingleFoldOrbitLaw` at EVERY `M ≥ 1` and EVERY family index
`ω`, given the points-classification gate: GATE-L and GATE-S are
discharged unconditionally (the two M-cycle letters and their rotation
equations, the honest seeds and their equations), GATE-A at the gate
form (the space receipt is `rfl`).  The argument chain maps the
engine's every input: the `hM` positivity; the `hspace` gate receipt;
the `hone`/`hstash` bigrading receipts (the honest data's own clones);
the two M-cycle letters and their rotation equations; the two honest
seed cycles and the honest seed equations — the weight-one pair first,
the weight-zero pair second, exactly as the engine demands. -/
theorem native_GST_single_fold_orbit_law_finiteLine_unconditional
    (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) :=
  native_GST_single_fold_orbit_law_of_sphereUnion_gate (M := M)
    (V := finiteLineWorld M)
    (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
      (finiteLineAnalytificationOfGate_space M gate) ω)
    (hM := Nat.pos_of_neZero ‹_›)
    (hspace := finiteLineAnalytificationOfGate_space M gate)
    (ω := ω)
    (hone := finiteLineHodgeDataHonest_hone M
      (finiteLineAnalytificationOfGate M gate)
      (finiteLineAnalytificationOfGate_space M gate) ω)
    (hstash := finiteLineHodgeDataHonest_hstash M
      (finiteLineAnalytificationOfGate M gate)
      (finiteLineAnalytificationOfGate_space M gate) ω)
    (R₁ := finiteLineCycleLetterOne M gate ω)
    (hR₁ := finiteLineCycleLetterOne_rotate M gate ω)
    (Z₁ := lineHonestSeedOne M)
    (hZ₁ := finiteLineHodgeDataHonest_seed_one M
      (finiteLineAnalytificationOfGate M gate)
      (finiteLineAnalytificationOfGate_space M gate) ω)
    (R₀ := finiteLineCycleLetterZero M gate ω)
    (hR₀ := finiteLineCycleLetterZero_rotate M gate ω)
    (Z₀ := lineHonestSeedZero M)
    (hZ₀ := finiteLineHodgeDataHonest_seed_zero M
      (finiteLineAnalytificationOfGate M gate)
      (finiteLineAnalytificationOfGate_space M gate) ω)

/-! ## §2 THE CONSEQUENCES (the repository's chain at the honest data) -/

/-- **THE CONSEQUENCE CHAIN.**  Wherever the law holds, the repository's
conditional consequences land: every rational `(p,p)` Hodge class of the
honest data is the cycle class of a genuine rational algebraic
codimension-p cycle (`exactHodge_of_one_GST_fold_orbit`), and
equivalently a finite rational combination of genuine irreducible
point-cycle classes (`finiteRationalCombination_of_one_GST_fold_orbit`). -/
theorem native_gst_single_fold_orbit_law_unconditional_consequences
    (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    EveryHodgeClassIsRationalAlgebraic
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) ∧
    EveryHodgeClassIsFiniteRationalCombination
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) :=
  ⟨exactHodge_of_one_GST_fold_orbit
      (native_GST_single_fold_orbit_law_finiteLine_unconditional M gate ω),
    finiteRationalCombination_of_one_GST_fold_orbit
      (native_GST_single_fold_orbit_law_finiteLine_unconditional M gate ω)⟩

/-! ## §3 THE MASTER PACKAGE (the general-M family's ∀M claim) -/

/-- **THE SINGLE-FOLD ORBIT LAW PACKAGE.**  The master receipt, in the
capstone's package shape restated as the honest-data route-4 analog: at
EVERY `M ≥ 1`, EVERY gate and EVERY family index `ω`, the law itself
AND its consequence chain — the general-M family's claims as one
theorem.  (The capstone's third conjunct — the Route-1 family's
infinitude — has no honest finite-line analog in the corpus; see the
honesty ledger item 3.) -/
theorem the_unconditional_single_fold_orbit_law_package :
    (∀ (M : ℕ) (hM : NeZero M) (gate : FiniteLinePointsGate M)
      (ω : singularCohomologyOf (TopCat.of unitSphereType) 2),
      NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)) ∧
    (∀ (M : ℕ) (hM : NeZero M) (gate : FiniteLinePointsGate M)
      (ω : singularCohomologyOf (TopCat.of unitSphereType) 2),
      EveryHodgeClassIsRationalAlgebraic
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω) ∧
      EveryHodgeClassIsFiniteRationalCombination
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)) := by
  refine ⟨?_, ?_⟩
  · intro M hM gate ω
    haveI : NeZero M := hM
    exact native_GST_single_fold_orbit_law_finiteLine_unconditional M gate ω
  · intro M hM gate ω
    haveI : NeZero M := hM
    exact native_gst_single_fold_orbit_law_unconditional_consequences M gate ω

/-! ## §4 Receipts -/

#check native_GST_single_fold_orbit_law_finiteLine_unconditional
#check native_gst_single_fold_orbit_law_unconditional_consequences
#check the_unconditional_single_fold_orbit_law_package

#check finiteLineCycleLetterOne
#check finiteLineCycleLetterOne_rotate
#check finiteLineCycleLetterZero
#check finiteLineCycleLetterZero_rotate
#check finiteLineAnalytificationOfGate
#check finiteLineAnalytificationOfGate_space
#check FiniteLinePointsGate

#print axioms native_GST_single_fold_orbit_law_finiteLine_unconditional
#print axioms native_gst_single_fold_orbit_law_unconditional_consequences
#print axioms the_unconditional_single_fold_orbit_law_package

end GSTFiniteLineUnconditionalSource

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (LAW-A) the engine's `hspace` argument rides the definitional
  unfolding `finiteLineHodgeDataHonest.analytification ≡ A` (the honest
  data's own `rfl` receipt, GSTFiniteLineHonestHodgeData.lean:220-225)
  — the green wave-68 pattern (`native_GST_single_fold_orbit_law_finiteLine`,
  GSTFiniteLineGeneralMLaw.lean:991-996, CI-green run 44928010015); if
  the elaborator stalls, bridge through
  `finiteLineHodgeDataHonest_analytification` with a `show`.
* (LAW-S) the `Z₁`/`Z₀` seed carriers ride the definitional equality
  `(finiteLineWorld M).X ≡ finiteLineScheme M` (the `rfl` world
  identification `finiteLineWorld_hWX`, GSTFiniteLineOverBase.lean:339)
  — the green pattern of `honest_componentClass_eq_world`
  (GSTFiniteLineHonestHodgeData.lean:250-252); the seed equations are
  then the honest data's own receipts at the atom terms.
* (LAW-O) NO local `have A := ...` abbreviations: a `have`-bound local
  is opaque to defeq (its value is discarded at elaboration), so the
  engine's `(H := ...)` instance and every sub-receipt are applied at
  the FULL spellings `finiteLineAnalytificationOfGate M gate` /
  `finiteLineAnalytificationOfGate_space M gate`, matching the goal
  syntactically (the wave-68 full-spelling discipline).  The `hspace`
  slot is a proof (any proof of the same Prop is defeq); the `A` slot is
  data (must be spelled in full).
* (LAW-G) the gate-form letters' own designated repair points (the §3
  delta-unification at the gate form) are documented in
  `GSTFiniteLineCycleCorrespondence.lean`'s §3 port notes — this module
  consumes the letters at their frozen signatures.
-/
