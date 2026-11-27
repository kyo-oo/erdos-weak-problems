import Mathlib
import HCUniverse2.GSTFiniteLinePointsGateDischarge
import HCUniverse2.GSTFiniteLineUnconditionalSource
import HCUniverse2.GSTFiniteLineHonestHodgeData
import HCUniverse2.GSTFiniteLineGeneralMLaw
import HCUniverse2.GSTFiniteLinePointAlgebra
/- SPLIT PIECE of GSTFiniteLinePrimitiveXSource.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE UNIVERSAL PRIMITIVE-X SOURCE — THE SOURCE-BASIS PACKAGE (wave 9)

THE FINAL MODULE of the finite-line unconditional round: the lane's second
promise ("THE UNCONDITIONAL LAW + universal primitive-X source"), executed
from the frozen statement design
`research/campaign/wave9-universal-source-battle-map.md`.

The mathematics (the classical content, at the honest data of
`GSTFiniteLineHonestHodgeData`): the finite-line world is `M` disjoint
projective lines; its rational Hodge sectors are carried by TWO EXPLICIT
families of honest atoms:

* weight zero — the component family: the generic-point atoms
  `finiteLineSourceZero M i` (the `R₀`-orbit of the honest seed), whose
  classes are the component classes — a ℚ-BASIS of the whole free weight-0
  fiber `H⁰ ≃ (Fin M → ℚ)` (independent unconditionally, spanning the whole
  sector, the compiler with the EXPLICIT coordinate readout);
* weight one — the closed-point family: the closed-point atoms
  `finiteLineSourceOne M i` (the `R₁`-orbit of the honest seed), whose
  classes are the honest point classes — independent at the fenced family
  index (`hω : ω ≠ 0`, the corpus's own liveness discipline) and spanning
  the weight-1 rational Hodge fiber (the span bigrading's own design);
* weights `p ≥ 2` — the honest vacuity: the fiber is the stash design's
  dead fiber (`⊥` by construction — NO cohomology vanishing is claimed or
  used), so every rational Hodge class there is zero.

The COMPILER: the uniform witness map — weight zero takes the EXPLICIT
coordinates (the `componentCohomologyZeroEquivFinM` readout, the honest
component H⁰ machine); weight one takes the §2-witness coordinates (the
Classical choice of the span certificate — the honest noncomputable
construction); the correctness receipts hold for EVERY class of the honest
data.  THE UNIVERSALITY: one recipe at every `M ≥ 1` — the ∀M master
package, conjoined with the gate-free law itself (the lane's first promise,
`native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`), at
the constructed unconditional analytification.

HONESTY LEDGER.

Every statement is proved unconditionally (the one disclosed fence: the
weight-one INDEPENDENCE carries `hω : ω ≠ 0` — the corpus has NO green
canonical nonvanishing sphere class, and at `ω = 0` the family is
identically zero, so the unguarded statement is false; the fence is the
campaign's own liveness discipline).  No `sorry`, no new axioms, no
`native_decide`.  Disclosed items:

1. THE ω-FENCE (as above): the span, the compiler and the master package
   are ∀ω; ONLY the weight-one independence demands the nonzero family
   index.
2. THE VACUITY'S HONEST SHAPE: the `p ≥ 2` sector's emptiness is the
   STASH design's dead fiber (the kit's `rationalHodgeSubspace_stash_eq_bot`
   engine — the complexification injectivity), NOT a positive-degree
   vanishing theorem (the sphere machine stays fenced).
3. THE COMPILER'S COORDINATES: weight zero = the explicit E-readout
   (computable content); weight one = the Classical-choice witness of §2
   (noncomputable — the corpus has no green degree-two dual-basis machine);
   the expected `Classical.choice` axiom receipt is the designated honesty
   marker.
4. THE PACKAGE'S LAW CONJUNCT: stated at the CONSTRUCTED unconditional
   analytification (`finiteLineAnalytificationUnconditional M` at the
   constructed gate) — no arbitrary-A claim is smuggled in (the campaign's
   acceptance discipline).

The GitHub CI lane `gst-finite-line-primitive-x-source.yml` owns the kernel
check.
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
open GSTComponentCohomologyZero
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTFinitePointHodgeData
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
open GSTFiniteLinePointsGateDischarge

namespace GSTFiniteLinePrimitiveXSource

/-! ## §0 The local instance bridges (the wave-63 §0 discipline) -/

local instance (priority := high) instHModule
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))

local instance (priority := high) instHAddCommGroup
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))

/-! ## §1 The source families (the explicit carriers) -/

/-- **THE WEIGHT-ZERO SOURCE FAMILY** — the generic-point atom of line `i`
(the `R₀`-orbit of the honest seed `lineHonestSeedZero M`, at the honest
prime lattice's own atom): the unit codimension-zero cycle at the `i`-th
generic point. -/
noncomputable def finiteLineSourceZero (M : ℕ) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineWorld M).X 0 :=
  codimensionPointCycle (finiteLineWorld M).X 0
    ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩

/-- **THE WEIGHT-ONE SOURCE FAMILY** — the closed-point atom of line `i`
(the `R₁`-orbit of the honest seed `lineHonestSeedOne M`): the unit
codimension-one cycle at the `i`-th line's closed point. -/
noncomputable def finiteLineSourceOne (M : ℕ) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineWorld M).X 1 :=
  codimensionPointCycle (finiteLineWorld M).X 1
    ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩

/-! ## §2 The class equations (the atom formulas at every index) -/

/-- **THE CLASS EQUATION AT WEIGHT ZERO** — the `i`-th source carrier's
class under the honest data's cycle-class map IS the `i`-th component class
(the honest atom formula + the prime-lattice index receipt, the honest
data's own seed equation at general `i`). -/
theorem finiteLineSourceZero_class (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (i : Fin M) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i) =
      finiteLineComponentClass M (finiteLineWorld M) A hspace i := by
  show honestCycleClassZero M (finiteLineWorld M) A hspace
      (codimensionPointCycle (finiteLineWorld M).X 0
        ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩) = _
  have hatom := honestCycleClassZero_atom M (finiteLineWorld M) A hspace
    ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩
  rw [hatom]
  exact congrArg (finiteLineComponentClass M (finiteLineWorld M) A hspace)
    (lineIndexOfGeneric_lineGenericPoint M i)

/-- **THE CLASS EQUATION AT WEIGHT ONE** — the `i`-th source carrier's
class under the honest data's cycle-class map IS the `i`-th point class
(the honest atom formula + the component receipt + the index receipt, the
honest data's own seed equation at general `i`). -/
theorem finiteLineSourceOne_class (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (i : Fin M) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i) =
      finiteLinePointClass M (finiteLineWorld M) A hspace ω i := by
  show honestCycleClassOne M (finiteLineWorld M) A hspace ω
      (codimensionPointCycle (finiteLineWorld M).X 1
        ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩) = _
  have hatom := honestCycleClassOne_atom M (finiteLineWorld M) A hspace ω
    ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩
  rw [hatom]
  have hcomp : lineComponentOf M
      ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩ =
      ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ :=
    lineClosedPointAt_component M i
  have hidx : lineIndexOfGeneric M
      (lineComponentOf M
        ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩) = i := by
    rw [hcomp]
    exact lineIndexOfGeneric_lineGenericPoint M i
  exact congrArg (finiteLinePointClass M (finiteLineWorld M) A hspace ω) hidx

/-! ## §3 The independence (the basis certificates) -/

/-- **THE WEIGHT-ZERO INDEPENDENCE** — the component source family's
classes are linearly independent UNCONDITIONALLY: the transported standard
basis (the `Pi.basisFun` singles under the component H⁰ machine's linear
equiv — the green corpus's own route, `GSTPositiveDimensionalLiveCoreLaw`
§2's independence bullet verbatim). -/
theorem finiteLineSourceZero_independent (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    LinearIndependent ℚ (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i)) := by
  have hfun : (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i))
      = (fun i : Fin M =>
        finiteLineComponentClass M (finiteLineWorld M) A hspace i) :=
    funext fun i => finiteLineSourceZero_class M A hspace ω i
  rw [hfun]
  set E := componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace) with hE
  have hbasis : LinearIndependent ℚ
      (fun i => Pi.single i (1 : ℚ) : Fin M → (Fin M → ℚ)) := by
    have hbf : LinearIndependent ℚ
        (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ)) :=
      (Pi.basisFun ℚ (Fin M)).linearIndependent
    rwa [show (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ))
        = fun i => Pi.single i (1 : ℚ) from by
      funext i
      exact Pi.basisFun_apply ℚ (Fin M) i] at hbf
  exact hbasis.map'
    (↑E.symm : (Fin M → ℚ) →ₗ[ℚ] RationalSingularCohomology A 0)
    (LinearMap.ker_eq_bot.mpr (EquivLike.injective E.symm))

/-- **THE WEIGHT-ONE INDEPENDENCE** — the closed-point source family's
classes are linearly independent at the FENCED family index: the green
`finiteLinePointClass_indep` receipt (the transported honest point-class
family) at `hω : ω ≠ 0`.  This is the campaign's disclosed liveness fence
(the corpus has no unconditional nonvanishing sphere class; at `ω = 0` the
family is identically zero). -/
theorem finiteLineSourceOne_independent (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    LinearIndependent ℚ (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i)) := by
  have hfun : (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i))
      = (fun i : Fin M =>
        finiteLinePointClass M (finiteLineWorld M) A hspace ω i) :=
    funext fun i => finiteLineSourceOne_class M A hspace ω i
  rw [hfun]
  exact finiteLinePointClass_indep M (finiteLineWorld M) A hspace ω hω

/-! ## §4 The decomposition machinery (the weight-zero readout) -/

/-- The function-space decomposition: the standard basis expansion on
`Fin M → ℚ` (the single-evaluator identity). -/
private theorem pi_single_sum_eq (M : ℕ) (f : Fin M → ℚ) :
    ∑ i, f i • Pi.single i (1 : ℚ) = f := by
  funext j
  simp [Pi.single_apply]

/-- **THE E-READOUT DECOMPOSITION** — every degree-zero class is the
explicit combination of the component source family with its OWN
`componentCohomologyZeroEquivFinM` coordinates: the transported
standard-basis expansion (the machine's linearity both ways, the
`symm_apply_apply` round trip).  This is the weight-zero compiler's
correctness engine. -/
theorem finiteLineComponentClass_decompose (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (α : RationalSingularCohomology A 0) :
    ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
      finiteLineComponentClass M (finiteLineWorld M) A hspace i = α := by
  set E := componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace) with hE
  have hper : ∀ i : Fin M, E (finiteLineComponentClass M
      (finiteLineWorld M) A hspace i) = Pi.single i (1 : ℚ) := by
    intro i
    show E (E.symm (Pi.single i (1 : ℚ))) = _
    exact E.apply_symm_apply (Pi.single i (1 : ℚ))
  have hfwd : E (∑ i, E α i •
      finiteLineComponentClass M (finiteLineWorld M) A hspace i) = E α := by
    calc E (∑ i, E α i •
          finiteLineComponentClass M (finiteLineWorld M) A hspace i)
        = ∑ i, E (E α i •
            finiteLineComponentClass M (finiteLineWorld M) A hspace i) := by
          rw [map_sum]
         _ = ∑ i, E α i • E (finiteLineComponentClass M
            (finiteLineWorld M) A hspace i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]
         _ = ∑ i, E α i • Pi.single i (1 : ℚ) :=
          Finset.sum_congr rfl fun i _ => by rw [hper i]
         _ = E α := pi_single_sum_eq M (E α)
  calc ∑ i, E α i • finiteLineComponentClass M (finiteLineWorld M) A hspace i
      = E.symm (E (∑ i, E α i •
          finiteLineComponentClass M (finiteLineWorld M) A hspace i)) := by
        rw [E.symm_apply_apply]
       _ = E.symm (E α) := by rw [hfwd]
       _ = α := by rw [E.symm_apply_apply]


end GSTFiniteLinePrimitiveXSource

end -- noncomputable section
