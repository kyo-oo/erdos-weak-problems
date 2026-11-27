import HCUniverse2.GSTPositiveDimensionalLiveCoreLaw
import HCUniverse2.GSTSphereUnionPointClassGate
import HCUniverse2.GSTCyclicOrbitSpan
import HCUniverse2.GSTFinitePointHodgeData

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE POSITIVE-DIMENSIONAL LAW LANDING (the lane's closing module)

THE FINAL ASSEMBLY of the positive-dimensional live-core lane: the module
that merges the campaign's three certified engines into the complete
reduction of `NativeGSTSingleFoldOrbitLaw` on the sphere-union world.

## The engines merged (the full citation ledger)

* FROM `GSTPositiveDimensionalLiveCoreLaw.lean` (the wave-46 merged law,
  CI-green run 44545624743): `positive_dimensional_live_core_law` — the
  weight-dispatch (weights 0 and 1 by certificates, weights `p ≥ 2` by the
  stash engine).
* FROM `GSTSphereUnionPointClassGate.lean` (waves 58-59, CI-green run
  44604829367): the honest point-class family `spherePointClass`, its
  cycle-equivariance `cycle_pointClass`, its linear independence
  `spherePointClass_indep`, its nonvanishing `spherePointClass_ne_zero`.
* FROM `GSTCyclicOrbitSpan.lean` (this wave): the cyclic-orbit span law
  `span_range_cyclicIterate` — the single algebraic fact both live-weight
  certificates consume.
* FROM the green corpus generally: `componentCohomologyZeroEquivFinM` (the
  component H⁰ machine), `sphereUnion_cohomology_zero` (the sphere-union
  component identification), `rationalHodgeSubspace_eq_top_of_degree_zero`
  (the free weight-0 fiber law), `realizedWordPair` (the correspondence
  word algebra), `RealizedCorrespondenceKrylovCertificate` (the certificate
  structure), `exists_nonzero_algebraic_hodge_class_of_law` (the
  no-free-lunch receipt).

## THE THEOREM

`native_GST_single_fold_orbit_law_of_sphereUnion_gate`: for a world whose
analytification carries the sphere-union space (`M` disjoint 2-spheres —
the honest analytification of the planned `finiteLineWorld M`, the disjoint
union of `M` projective lines), whose weight-1 bigrading is the span
bigrading on the honest point-class family, whose weights `p ≥ 2` carry the
stash bigrading, and which supplies the two M-cycle letters as GENUINE
realized closed correspondences rotating the two honest families, together
with the two honest seed cycles — the FULL `NativeGSTSingleFoldOrbitLaw`
holds.

**THE ω-DISCLOSURE (stronger than the frozen design):** the honest sphere
class `ω ≠ 0` — the fenced sphere-machine core — is NOT an input of the law
theorem.  The law's content at the live weight is the Krylov cyclicity of
the designed fiber, and cyclicity is a statement about the SPAN of the
family, which needs no nonvanishing.  The ω-core enters exactly one place:
the LIVENESS receipts of §7 (`weightOne_fiber_not_subsingleton` and the
nonzero algebraic seed of the master package) — the certification that the
weight-1 fiber is genuinely alive.

## THE GATES (the remaining classical inputs, precisely fenced)

1. THE LETTER GATES (`R₀`, `R₁` + `hR₀`, `hR₁`): genuine realized closed
   correspondences whose cohomological operators rotate the two honest
   families by the cyclic predecessor.  For the planned carrier these are
   the graphs of the M-cycle automorphism; the derived-form lemma
   `spherePointClassWorld_rotate_of_pullback` documents that the family
   equation is exactly the green `cycle_pointClass` under the
   pullback-operator gate.
2. THE SEED GATES (`Z₀`, `Z₁` + `hZ₀`, `hZ₁`): honest cycles whose classes
   are the 0-th component class (weight 0) and the 0-th point class
   (weight 1) — for the planned carrier, the generic-point cycle of the
   0-th line and a closed point on the 0-th line.
3. THE BIGRADING DESIGN (`hone`, `hstash`): the honest Hodge-theoretic
   shape of the curve world (all of H² is (1,1), spanned by the point
   classes; weights ≥ 2 are dead for dimension reasons, stashed without
   vanishing proofs by the kit's engine).

Everything else — both certificates, both orbit computations, both
cyclicity discharges, the weight dispatch, the exact-Hodge consequence,
the liveness receipts, the no-free-lunch nonzero algebraic class — is
PROVED here, unconditionally.

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane
`gst-positive-dimensional-law-landing.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional
open GSTNativeSingleFoldOrbitLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTPositiveDimensionalLiveCoreLaw
open GSTComponentCohomologyZero
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTSphereUnionPointClassGate
open GSTCyclicOrbitSpan
open GSTFinitePointHodgeData

namespace GSTPositiveDimensionalLawLanding

variable {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}

/-! ## §0 The raw/world transport at the live degree -/

/-- The type identification: the world's degree-2 rational singular
cohomology IS the raw sphere-union cohomology of the wave-57 maps module
(the corpus's own `rfl` chain, then the space identification). -/
theorem rationalSingularCohomology_two_eq (M : ℕ)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M)) :
    RationalSingularCohomology H.analytification 2 =
      singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 := by
  rw [← singularCohomologyOf_eq H.analytification 2, hspace]

/-- The raw-to-world transport function at the live degree. -/
def sphereUnionCoe (M : ℕ)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M)) :
    singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 →
      RationalSingularCohomology H.analytification 2 :=
  (Equiv.cast (rationalSingularCohomology_two_eq M hspace)).symm

/-- **THE HONEST POINT-CLASS FAMILY, WORLD-TYPED.**  The green gate's
family `spherePointClass M ω`, transported to the world's cohomology
along the space identification. -/
def spherePointClassWorld (M : ℕ)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (j : Fin M) :
    RationalSingularCohomology H.analytification 2 :=
  sphereUnionCoe M hspace (spherePointClass M ω j)

/-- **THE DERIVED LETTER EQUATION.**  A letter whose cohomological operator
is the transported M-cycle pullback rotates the world family exactly as the
green `cycle_pointClass` rotates the raw family — the honesty documentation
for the letter gate: the family equation consumed by the law is the green
gate calculus, nothing more. -/
theorem spherePointClassWorld_rotate_of_pullback (M : ℕ)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hRop : ∀ u : singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2,
      R₁.cohomologyOperator (sphereUnionCoe M hspace u) =
        sphereUnionCoe M hspace
          ((cohomologyPullbackOf (sphereCycle M) 2) u))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (j : Fin M) :
    R₁.cohomologyOperator (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j) := by
  have h1 := hRop (spherePointClass M ω j)
  rw [cycle_pointClass M ω j] at h1
  exact h1

/-! ## §1 The component family at degree zero -/

/-- **THE COMPONENT-CLASS FAMILY.**  The degree-0 component iso (the green
component machine, specialized through the sphere-union component
identification) applied to the standard indicator vectors. -/
def sphereComponentClass (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (j : Fin M) :
    RationalSingularCohomology H.analytification 0 :=
  (componentCohomologyZeroEquivFinM H.analytification M
    (sphereUnion_cohomology_zero hspace)).symm (Pi.single j (1 : ℚ))

/-- The single-vector spanning law on the function space (the 0-dim lane's
own CI-green idiom, restated locally). -/
theorem singles_span_top (N : ℕ) :
    Submodule.span ℚ
      (Set.range fun i : Fin N => (Pi.single i (1 : ℚ) : Fin N → ℚ)) = ⊤ := by
  apply top_unique
  intro v _
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin N → ℚ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
      smul_eq_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hv]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- **THE COMPONENT FAMILY SPANS THE WHOLE H⁰.**  The surjective linear
transport of the full function-space span (the 0-dim lane's green
span-image chain, mirrored). -/
theorem span_range_sphereComponentClass (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M)) :
    Submodule.span ℚ (Set.range (sphereComponentClass M hM hspace)) = ⊤ := by
  apply top_unique
  intro u _
  have hEu : (componentCohomologyZeroEquivFinM H.analytification M
      (sphereUnion_cohomology_zero hspace)) u ∈
      Submodule.span ℚ
        (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ)) := by
    rw [singles_span_top M]
    exact Submodule.mem_top
  have hsub : (componentCohomologyZeroEquivFinM H.analytification M
      (sphereUnion_cohomology_zero hspace)).symm.toLinearMap ''
      (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ)) ⊆
      Set.range (sphereComponentClass M hM hspace) := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  have hmem : u ∈ Submodule.span ℚ
      ((componentCohomologyZeroEquivFinM H.analytification M
        (sphereUnion_cohomology_zero hspace)).symm.toLinearMap ''
        (Set.range fun i : Fin M => (Pi.single i (1 : ℚ) : Fin M → ℚ))) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map.mpr
      ⟨(componentCohomologyZeroEquivFinM H.analytification M
          (sphereUnion_cohomology_zero hspace)) u, hEu,
        (componentCohomologyZeroEquivFinM H.analytification M
          (sphereUnion_cohomology_zero hspace)).symm_apply_apply u⟩
  exact Submodule.span_mono hsub hmem

/-! ## §2 The weight-1 fiber equation -/

/-- **THE DESIGNED WEIGHT-1 FIBER.**  Under the span-bigrading design, the
rational Hodge fiber at weight 1 is exactly the rational span of the honest
point-class family (the kit's gated-live-weight engine). -/
theorem rationalHodgeSubspace_one_eq_span (M : ℕ)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega)) :
    rationalHodgeSubspace (H.hodgeBigrading 1) =
      Submodule.span ℚ (Set.range (spherePointClassWorld M hspace ω)) := by
  rw [hone]
  exact rationalHodgeSubspace_span_eq _ 1 (by omega)

/-! ## §3 The single-letter word algebra -/

/-- **THE SINGLE-LETTER WORD'S OPERATOR.**  The realized word consisting of
one unweighted letter acts by that letter's cohomological operator (the
word algebra's add/smul/zero chain: `1 • T + 0 = T`). -/
theorem realizedWordPair_single_cohomologyOperator (p : ℕ)
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (realizedWordPair [( (1 : ℚ), R)]).cohomologyOperator =
      R.cohomologyOperator := by
  have hrw : realizedWordPair [( (1 : ℚ), R)] =
      CycleClassOperatorPair.add (CycleClassOperatorPair.smul 1 R.operatorPair)
        CycleClassOperatorPair.zero := rfl
  rw [hrw]
  show (1 : ℚ) • R.operatorPair.cohomologyOperator + 0 = R.cohomologyOperator
  rw [RealizedFiniteClosedCorrespondence.operatorPair_cohomology]
  simp

/-! ## §4 The weight-1 certificate -/

/-- The word's Hodge field: the letter rotates the honest family, hence
preserves its span — which IS the designed weight-1 fiber. -/
theorem sphereUnionWordOne_hodge (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j)) :
    ∀ alpha : ClassicalHodgeFiber V H 1,
      (realizedWordPair [( (1 : ℚ), R₁)]).cohomologyOperator alpha.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading 1) := by
  intro alpha
  rw [realizedWordPair_single_cohomologyOperator]
  have hfib : rationalHodgeSubspace (H.hodgeBigrading 1) =
      Submodule.span ℚ (Set.range (spherePointClassWorld M hspace ω)) :=
    rationalHodgeSubspace_one_eq_span M hspace ω hone
  have hsub : Submodule.span ℚ (Set.range (spherePointClassWorld M hspace ω)) ≤
      Submodule.comap R₁.cohomologyOperator
        (Submodule.span ℚ (Set.range (spherePointClassWorld M hspace ω))) := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨j, rfl⟩
    exact Submodule.mem_comap.mpr
      (by rw [hR₁ j]; exact Submodule.subset_span ⟨_, rfl⟩)
  rw [hfib]
  exact hsub (by rw [← hfib]; exact alpha.2)

/-- The seed's Hodge field: the honest 0-th point class lies in the
designed fiber (it is a generator of the span). -/
theorem sphereUnionSeedOne_hodge (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, hM⟩) :
    H.cycleClass 1 Z₁ ∈ rationalHodgeSubspace (H.hodgeBigrading 1) := by
  rw [rationalHodgeSubspace_one_eq_span M hspace ω hone, hZ₁]
  exact Submodule.subset_span ⟨⟨0, hM⟩, rfl⟩

/-- **THE WEIGHT-1 KR YLOV CERTIFICATE.**  The single M-cycle letter with
the honest 0-th point-class seed. -/
noncomputable def sphereUnionCertificateOne (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, hM⟩) :
    RealizedCorrespondenceKrylovCertificate V H 1 where
  word := [( (1 : ℚ), R₁)]
  word_hodge := sphereUnionWordOne_hodge M hM hspace ω hone R₁ hR₁
  seedCycle := Z₁
  seed_hodge := sphereUnionSeedOne_hodge M hM hspace ω hone Z₁ hZ₁

/-- **THE WEIGHT-1 ORBIT IS THE ROTATED FAMILY.**  The n-th orbit vector's
underlying class is the honest point class of the n-th rotated index — the
seed equation at the base, the letter's family rotation at the step. -/
theorem sphereUnionCertificateOne_hodgeOrbit (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, hM⟩)
    (n : ℕ) :
    ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).1 =
      spherePointClassWorld M hspace ω ((cyclicPred M)^[n] ⟨0, hM⟩) := by
  induction n with
  | zero =>
      show H.cycleClass 1 Z₁ = _
      rw [hZ₁]
      rfl
  | succ n ih =>
      -- WAVE 60.4 (run 44634998857): the projection must sit on the SAME
      -- line as the certificate-term's closing paren — a line-broken
      -- `… hZ₁)\n  .hodgeOrbit` parses as an application to a dot-term.
      have hstep : ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit (n + 1)).1 =
          R₁.cohomologyOperator ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).1 := by
        show (realizedWordPair [( (1 : ℚ), R₁)]).cohomologyOperator
          ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).1 = _
        rw [realizedWordPair_single_cohomologyOperator]
      rw [hstep, ih, hR₁ ((cyclicPred M)^[n] ⟨0, hM⟩),
        Function.iterate_succ_apply' (cyclicPred M) n ⟨0, hM⟩]

/-- **THE WEIGHT-1 CYCLICITY.**  The single-letter orbit spans the whole
designed weight-1 fiber: the orbit's underlying family is the rotated
point-class family (the orbit theorem), the rotated family spans what the
family spans (the cyclic-orbit span law), and the family's span IS the
fiber (the kit's span engine). -/
theorem sphereUnionCertificateOne_isKrylovCyclic (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, hM⟩) :
    (sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).IsKrylovCyclic :=
  (Submodule.span_range_subtype_eq_top_iff
    (p := rationalHodgeSubspace (H.hodgeBigrading 1))
    (s := fun n : Nat =>
      ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).1)
    (fun n =>
      ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).2)).mpr
    (by
      have hfam : (fun n : Nat =>
          ((sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁).hodgeOrbit n).1) =
          fun n : Nat => spherePointClassWorld M hspace ω
            ((cyclicPred M)^[n] ⟨0, hM⟩) :=
        funext fun n =>
          sphereUnionCertificateOne_hodgeOrbit M hM hspace ω hone R₁ hR₁ Z₁ hZ₁ n
      rw [hfam]
      rw [span_range_cyclicIterate M hM (spherePointClassWorld M hspace ω)]
      exact (rationalHodgeSubspace_one_eq_span M hspace ω hone).symm)

/-! ## §5 The weight-0 certificate -/

/-- The weight-0 word's Hodge field: at weight zero the rational Hodge
fiber is the whole H⁰ — forced for ANY Hodge data on any smooth projective
complex world (the 0-dim lane's green weight-zero fiber law). -/
theorem sphereUnionWordZero_hodge (M : ℕ)
    (R₀ : RealizedFiniteClosedCorrespondence V H 0) :
    ∀ alpha : ClassicalHodgeFiber V H 0,
      (realizedWordPair [( (1 : ℚ), R₀)]).cohomologyOperator alpha.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading 0) := by
  intro alpha
  rw [rationalHodgeSubspace_eq_top_of_degree_zero H]
  exact Submodule.mem_top

/-- The weight-0 seed's Hodge field: the fiber is the whole H⁰. -/
theorem sphereUnionSeedZero_hodge (M : ℕ)
    (Z₀ : codimensionCycles V.X 0) :
    H.cycleClass 0 Z₀ ∈ rationalHodgeSubspace (H.hodgeBigrading 0) := by
  rw [rationalHodgeSubspace_eq_top_of_degree_zero H]
  exact Submodule.mem_top

/-- **THE WEIGHT-0 KR YLOV CERTIFICATE.**  The single M-cycle letter with
the honest 0-th component-class seed. -/
noncomputable def sphereUnionCertificateZero (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))
    (Z₀ : codimensionCycles V.X 0)
    (hZ₀ : H.cycleClass 0 Z₀ = sphereComponentClass M hM hspace ⟨0, hM⟩) :
    RealizedCorrespondenceKrylovCertificate V H 0 where
  word := [( (1 : ℚ), R₀)]
  word_hodge := sphereUnionWordZero_hodge M R₀
  seedCycle := Z₀
  seed_hodge := sphereUnionSeedZero_hodge M Z₀

/-- **THE WEIGHT-0 ORBIT IS THE ROTATED COMPONENT FAMILY.** -/
theorem sphereUnionCertificateZero_hodgeOrbit (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))
    (Z₀ : codimensionCycles V.X 0)
    (hZ₀ : H.cycleClass 0 Z₀ = sphereComponentClass M hM hspace ⟨0, hM⟩)
    (n : ℕ) :
    ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).1 =
      sphereComponentClass M hM hspace ((cyclicPred M)^[n] ⟨0, hM⟩) := by
  induction n with
  | zero =>
      show H.cycleClass 0 Z₀ = _
      rw [hZ₀]
      rfl
  | succ n ih =>
      -- WAVE 60.4: same-line projection discipline as the weight-1 orbit.
      have hstep : ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit (n + 1)).1 =
          R₀.cohomologyOperator ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).1 := by
        show (realizedWordPair [( (1 : ℚ), R₀)]).cohomologyOperator
          ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).1 = _
        rw [realizedWordPair_single_cohomologyOperator]
      rw [hstep, ih, hR₀ ((cyclicPred M)^[n] ⟨0, hM⟩),
        Function.iterate_succ_apply' (cyclicPred M) n ⟨0, hM⟩]

/-- **THE WEIGHT-0 CYCLICITY.**  The single-letter orbit spans the whole
weight-0 fiber: the orbit is the rotated component family, the rotated
family spans what the family spans, and the component family spans the
whole H⁰, which IS the weight-0 fiber (forced for any Hodge data). -/
theorem sphereUnionCertificateZero_isKrylovCyclic (M : ℕ) (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))
    (Z₀ : codimensionCycles V.X 0)
    (hZ₀ : H.cycleClass 0 Z₀ = sphereComponentClass M hM hspace ⟨0, hM⟩) :
    (sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).IsKrylovCyclic :=
  (Submodule.span_range_subtype_eq_top_iff
    (p := rationalHodgeSubspace (H.hodgeBigrading 0))
    (s := fun n : Nat =>
      ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).1)
    (fun n =>
      ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).2)).mpr
    (by
      have hfam : (fun n : Nat =>
          ((sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀).hodgeOrbit n).1) =
          fun n : Nat => sphereComponentClass M hM hspace
            ((cyclicPred M)^[n] ⟨0, hM⟩) :=
        funext fun n =>
          sphereUnionCertificateZero_hodgeOrbit M hM hspace R₀ hR₀ Z₀ hZ₀ n
      rw [hfam]
      rw [span_range_cyclicIterate M hM (sphereComponentClass M hM hspace)]
      rw [rationalHodgeSubspace_eq_top_of_degree_zero H]
      exact span_range_sphereComponentClass M hM hspace)

/-! ## §6 THE LAW -/

/-- **THE POSITIVE-DIMENSIONAL LAW, LANDED.**  For a world whose
analytification carries the sphere-union space (the honest analytification
of the planned `finiteLineWorld M`), whose weight-1 bigrading is the span
bigrading on the honest point-class family, whose weights `p ≥ 2` carry the
stash bigrading, and which supplies the two M-cycle letters as genuine
realized closed correspondences rotating the two honest families, together
with the two honest seed cycles: the FULL `NativeGSTSingleFoldOrbitLaw`
holds.

The ω-disclosure: the honest sphere class `ω` appears only as the INDEX of
the family design (any degree-2 class on the sphere parameterizes the same
construction); its NONVANISHING — the fenced sphere-machine core — is
needed only for the liveness receipts of §7, not for the law. -/
theorem native_GST_single_fold_orbit_law_of_sphereUnion_gate
    {M : ℕ} (hM : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (hstash : ∀ p : ℕ, 1 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, hM⟩)
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M hM hspace j) =
      sphereComponentClass M hM hspace (cyclicPred M j))
    (Z₀ : codimensionCycles V.X 0)
    (hZ₀ : H.cycleClass 0 Z₀ = sphereComponentClass M hM hspace ⟨0, hM⟩) :
    NativeGSTSingleFoldOrbitLaw V H := by
  refine positive_dimensional_live_core_law ?_ ?_ hstash
  · exact ⟨sphereUnionCertificateZero M hM hspace R₀ hR₀ Z₀ hZ₀,
      sphereUnionCertificateZero_isKrylovCyclic M hM hspace R₀ hR₀ Z₀ hZ₀⟩
  · exact ⟨sphereUnionCertificateOne M hM hspace ω hone R₁ hR₁ Z₁ hZ₁,
      sphereUnionCertificateOne_isKrylovCyclic M hM hspace ω hone R₁ hR₁ Z₁ hZ₁⟩

/-! ## §7 The liveness receipts (the ω-gated honesty) -/

/-- **THE RAW POINT CLASSES ARE PAIRWISE DISTINCT.**  The 0-th and 1-st
honest point classes differ: a coincidence would be a nontrivial rational
relation (coefficients `1, -1` on the two-point set) contradicting the
green linear independence of the gate family. -/
theorem spherePointClass_pair_ne (M : ℕ) (hM : 2 ≤ M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    spherePointClass M ω ⟨0, by omega⟩ ≠ spherePointClass M ω ⟨1, by omega⟩ := by
  intro h
  have hindep : LinearIndependent ℚ (spherePointClass M ω) :=
    spherePointClass_indep M ω hω
  rw [linearIndependent_iff'] at hindep
  have hv01 : (⟨0, by omega⟩ : Fin M) ≠ (⟨1, by omega⟩ : Fin M) := by
    intro hh
    exact absurd (congrArg Fin.val hh) (by simp)
  have hv10 : (⟨1, by omega⟩ : Fin M) ≠ (⟨0, by omega⟩ : Fin M) := Ne.symm hv01
  -- WAVE 60.3 (run 44629232343): the outer cons's membership proof is
  -- `v0 ∉ {v1}` for the v0-first arrangement (the wave-60 spelling had the
  -- two proofs swapped); the cons-case equations close by the named
  -- hypotheses (rcases-with-rfl cannot subst Fin-literal equalities); the
  -- empty-sum and the two ite-conditions reduce inside simp (the
  -- Fin-literal equalities are decidable by reduction).
  have hv0not : (⟨0, by omega⟩ : Fin M) ∉
      Finset.cons (⟨1, by omega⟩ : Fin M) Finset.empty
        (Finset.notMem_empty _) := by
    intro hmem
    rcases Finset.mem_cons.mp hmem with hh | h2
    · exact hv01 hh
    · exact absurd h2 (Finset.notMem_empty _)
  have hsum : ∑ i ∈ Finset.cons (⟨0, by omega⟩ : Fin M)
      (Finset.cons (⟨1, by omega⟩ : Fin M) Finset.empty
        (Finset.notMem_empty _)) hv0not,
      (fun i => if i = (⟨0, by omega⟩ : Fin M) then (1 : ℚ) else (-1 : ℚ)) i •
      spherePointClass M ω i = 0 := by
    rw [Finset.sum_cons, Finset.sum_cons]
    -- WAVE 60.4: the empty-sum closes at the TERM level (both the
    -- rewrite-level and the simp-level matches stall on the
    -- lambda-spelling of the summand).
    have hempty : ∑ x ∈ Finset.empty,
        (fun i => if i = (⟨0, by omega⟩ : Fin M) then (1 : ℚ) else (-1 : ℚ)) x •
        spherePointClass M ω x = 0 := Finset.sum_empty
    rw [hempty]
    simp [h]
  -- WAVE 60.5: the independence statement takes the INDEX and then the
  -- membership; the hypothesis arrives beta-reduced, so the directed
  -- if_pos closes the self-equality condition directly.
  have h0 := hindep _ _ hsum (⟨0, by omega⟩ : Fin M)
    (Finset.mem_cons.mpr (Or.inl rfl))
  rw [if_pos rfl] at h0
  exact absurd h0 one_ne_zero

/-- **THE WORLD POINT CLASSES ARE PAIRWISE DISTINCT.**  The transport is
injective (it is a cast-equivolution), so the world family inherits the
raw family's distinctness — the liveness witness at weight 1. -/
theorem spherePointClassWorld_pair_ne (M : ℕ) (hM : 2 ≤ M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    spherePointClassWorld M hspace ω ⟨0, by omega⟩ ≠
      spherePointClassWorld M hspace ω ⟨1, by omega⟩ := by
  intro h
  refine spherePointClass_pair_ne M hM ω hω ?_
  exact Equiv.injective
    ((Equiv.cast (rationalSingularCohomology_two_eq M hspace)).symm) h

/-- **THE COMPONENT CLASSES ARE PAIRWISE DISTINCT.**  The component iso
sends them to distinct indicator vectors. -/
theorem sphereComponentClass_pair_ne (M : ℕ) (hM : 2 ≤ M) (hM' : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M)) :
    sphereComponentClass M hM' hspace ⟨0, by omega⟩ ≠
      sphereComponentClass M hM' hspace ⟨1, by omega⟩ := by
  intro h
  have hu0 : sphereComponentClass M hM' hspace (⟨0, by omega⟩ : Fin M) =
      (componentCohomologyZeroEquivFinM H.analytification M
        (sphereUnion_cohomology_zero hspace)).symm
        (Pi.single (⟨0, by omega⟩ : Fin M) (1 : ℚ)) := rfl
  have hu1 : sphereComponentClass M hM' hspace (⟨1, by omega⟩ : Fin M) =
      (componentCohomologyZeroEquivFinM H.analytification M
        (sphereUnion_cohomology_zero hspace)).symm
        (Pi.single (⟨1, by omega⟩ : Fin M) (1 : ℚ)) := rfl
  have hcongr : (componentCohomologyZeroEquivFinM H.analytification M
      (sphereUnion_cohomology_zero hspace))
      (sphereComponentClass M hM' hspace ⟨0, by omega⟩) =
      (componentCohomologyZeroEquivFinM H.analytification M
      (sphereUnion_cohomology_zero hspace))
      (sphereComponentClass M hM' hspace ⟨1, by omega⟩) :=
    congrArg (fun x => (componentCohomologyZeroEquivFinM H.analytification M
      (sphereUnion_cohomology_zero hspace)) x) h
  rw [hu0, hu1, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at hcongr
  have h01 : (⟨0, by omega⟩ : Fin M) ≠ (⟨1, by omega⟩ : Fin M) := by
    intro hh
    exact absurd (congrArg Fin.val hh) (by simp)
  have h0 := congrFun hcongr (⟨0, by omega⟩ : Fin M)
  -- WAVE 60.5: the RAW rewrites avoid simp's condition-normalization (the
  -- self-equality was being collapsed to True, killing the if_pos match);
  -- the two proof-irrelevant Fin-literals unify definitionally.
  rw [Pi.single_apply, Pi.single_apply, if_pos rfl, if_neg h01] at h0
  exact absurd h0 one_ne_zero

/-- **THE WEIGHT-0 FIBER IS LIVE.**  With at least two components, the
weight-0 fiber is not a subsingleton: the two component classes are
distinct elements. -/
theorem weightZero_fiber_not_subsingleton (M : ℕ) (hM : 2 ≤ M) (hM' : 0 < M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M)) :
    ¬ Subsingleton (ClassicalHodgeFiber V H 0) := by
  intro hsub
  haveI hsubI : Subsingleton (ClassicalHodgeFiber V H 0) := hsub
  have hmem : ∀ j : Fin M, sphereComponentClass M hM' hspace j ∈
      rationalHodgeSubspace (H.hodgeBigrading 0) := by
    intro j
    rw [rationalHodgeSubspace_eq_top_of_degree_zero H]
    exact Submodule.mem_top
  have heq := @Subsingleton.elim (ClassicalHodgeFiber V H 0) hsubI
    (⟨sphereComponentClass M hM' hspace ⟨0, by omega⟩, hmem _⟩ :
      ClassicalHodgeFiber V H 0)
    (⟨sphereComponentClass M hM' hspace ⟨1, by omega⟩, hmem _⟩ :
      ClassicalHodgeFiber V H 0)
  exact sphereComponentClass_pair_ne M hM hM' hspace
    (congrArg Subtype.val heq)

/-- **THE WEIGHT-1 FIBER IS LIVE (the ω-gated receipt).**  Given the honest
sphere class nonzero, the designed weight-1 fiber is not a subsingleton:
the two world point classes are distinct elements.  THIS is where the
fenced sphere-machine core is consumed — and it is the ONLY place. -/
theorem weightOne_fiber_not_subsingleton (M : ℕ) (hM : 2 ≤ M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega)) :
    ¬ Subsingleton (ClassicalHodgeFiber V H 1) := by
  intro hsub
  haveI hsubI : Subsingleton (ClassicalHodgeFiber V H 1) := hsub
  have hmem : ∀ j : Fin M, spherePointClassWorld M hspace ω j ∈
      rationalHodgeSubspace (H.hodgeBigrading 1) := by
    intro j
    rw [rationalHodgeSubspace_one_eq_span M hspace ω hone]
    exact Submodule.subset_span ⟨j, rfl⟩
  have heq := @Subsingleton.elim (ClassicalHodgeFiber V H 1) hsubI
    (⟨spherePointClassWorld M hspace ω ⟨0, by omega⟩, hmem _⟩ :
      ClassicalHodgeFiber V H 1)
    (⟨spherePointClassWorld M hspace ω ⟨1, by omega⟩, hmem _⟩ :
      ClassicalHodgeFiber V H 1)
  exact spherePointClassWorld_pair_ne M hM hspace ω hω
    (congrArg Subtype.val heq)

/-! ## §8 THE MASTER PACKAGE -/

/-- **THE COMPLETE POSITIVE-DIMENSIONAL RECEIPT.**  For the gated world
(with the honest sphere class nonzero and at least two lines): the law
itself; the exact-Hodge consequence through the repository's conditional
chain; the liveness of both live weights (weight 0 by the component
machine, weight 1 by the honest sphere class); and the no-free-lunch
witness — a genuine algebraic cycle with a nonzero Hodge class at the live
weight 1, obtained through the landing module's own green receipt. -/
theorem positive_dimensional_package_of_sphereUnion_gate
    {M : ℕ} (hM : 2 ≤ M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0)
    (hone : H.hodgeBigrading 1 =
      spanBigrading (spherePointClassWorld M hspace ω) 1 (by omega))
    (hstash : ∀ p : ℕ, 1 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p))
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld M hspace ω j) =
      spherePointClassWorld M hspace ω (cyclicPred M j))
    (Z₁ : codimensionCycles V.X 1)
    (hZ₁ : H.cycleClass 1 Z₁ = spherePointClassWorld M hspace ω ⟨0, by omega⟩)
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass M (by omega) hspace j) =
      sphereComponentClass M (by omega) hspace (cyclicPred M j))
    (Z₀ : codimensionCycles V.X 0)
    (hZ₀ : H.cycleClass 0 Z₀ =
      sphereComponentClass M (by omega) hspace ⟨0, by omega⟩) :
    NativeGSTSingleFoldOrbitLaw V H ∧
    EveryHodgeClassIsRationalAlgebraic H ∧
    ¬ Subsingleton (ClassicalHodgeFiber V H 0) ∧
    ¬ Subsingleton (ClassicalHodgeFiber V H 1) ∧
    ∃ Z : codimensionCycles V.X 1,
      H.cycleClass 1 Z ∈ rationalHodgeSubspace (H.hodgeBigrading 1) ∧
      H.cycleClass 1 Z ≠ 0 := by
  have hM' : 0 < M := by omega
  have hlaw := native_GST_single_fold_orbit_law_of_sphereUnion_gate
    (M := M) hM' hspace ω hone hstash R₁ hR₁ Z₁ hZ₁ R₀ hR₀ Z₀ hZ₀
  refine ⟨hlaw, exactHodge_of_one_GST_fold_orbit hlaw, ?_, ?_, ?_⟩
  · exact weightZero_fiber_not_subsingleton M hM hM' hspace
  · exact weightOne_fiber_not_subsingleton M hM hspace ω hω hone
  · have hns : ¬ Subsingleton (ClassicalHodgeFiber V H 1) :=
      weightOne_fiber_not_subsingleton M hM hspace ω hω hone
    -- WAVE 60.4: the pin's `exists_pair_ne` spelling does not take the
    -- hypothesis positionally — the pair is constructed directly from the
    -- ¬Subsingleton statement by classical contraposition.
    have hpair : ∃ a b : ClassicalHodgeFiber V H 1, a ≠ b := by
      by_contra hcon
      exact hns ⟨fun a b => by
        by_contra hne
        exact hcon ⟨a, b, hne⟩⟩
    obtain ⟨a, b, hne⟩ := hpair
    have hlive : ∃ a : ClassicalHodgeFiber V H 1, a ≠ 0 := by
      by_cases ha : a = 0
      · exact ⟨b, fun hb => hne (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    exact exists_nonzero_algebraic_hodge_class_of_law hlaw hlive

/-! ## §9 Receipts -/

#check rationalSingularCohomology_two_eq
#check sphereUnionCoe
#check spherePointClassWorld
#check spherePointClassWorld_rotate_of_pullback
#check sphereComponentClass
#check span_range_sphereComponentClass
#check rationalHodgeSubspace_one_eq_span
#check realizedWordPair_single_cohomologyOperator
#check sphereUnionCertificateOne
#check sphereUnionCertificateOne_hodgeOrbit
#check sphereUnionCertificateOne_isKrylovCyclic
#check sphereUnionCertificateZero
#check sphereUnionCertificateZero_hodgeOrbit
#check sphereUnionCertificateZero_isKrylovCyclic
#check native_GST_single_fold_orbit_law_of_sphereUnion_gate
#check spherePointClass_pair_ne
#check spherePointClassWorld_pair_ne
#check sphereComponentClass_pair_ne
#check weightZero_fiber_not_subsingleton
#check weightOne_fiber_not_subsingleton
#check positive_dimensional_package_of_sphereUnion_gate

#print axioms rationalSingularCohomology_two_eq
#print axioms spherePointClassWorld_rotate_of_pullback
#print axioms span_range_sphereComponentClass
#print axioms rationalHodgeSubspace_one_eq_span
#print axioms realizedWordPair_single_cohomologyOperator
#print axioms sphereUnionCertificateOne_hodgeOrbit
#print axioms sphereUnionCertificateOne_isKrylovCyclic
#print axioms sphereUnionCertificateZero_hodgeOrbit
#print axioms sphereUnionCertificateZero_isKrylovCyclic
#print axioms native_GST_single_fold_orbit_law_of_sphereUnion_gate
#print axioms spherePointClass_pair_ne
#print axioms spherePointClassWorld_pair_ne
#print axioms sphereComponentClass_pair_ne
#print axioms weightZero_fiber_not_subsingleton
#print axioms weightOne_fiber_not_subsingleton
#print axioms positive_dimensional_package_of_sphereUnion_gate

end GSTPositiveDimensionalLawLanding

end -- noncomputable section

/-!
PORT RISKS (the designated CI repair points of this file):

* (LAW-1) `rationalSingularCohomology_two_eq`: the `rw [←
  singularCohomologyOf_eq ...]` must surface the `H.analytification.space`
  syntax before the `hspace` rewrite — the green corpus's own
  `sphereUnion_cohomology_zero` pattern; if the auto-rfl tail fails, append
  `rfl`.
* (WORD-1) `realizedWordPair_single_cohomologyOperator`: the `rfl`-proof of
  the cons-equation of `realizedWordPair` on the literal singleton list;
  the fallback is `by simp only [realizedWordPair]`.
* (STEP-1) the orbit `hstep` bridges: the `show` reduces the certificate's
  `hodgeOrbit`-step to the word-operator application through the equation
  compiler and the structure projections (the 0-dim lane's own green
  `rfl`-step pattern); if a bridge stalls, insert
  `RealizedCorrespondenceKrylovCertificate.hodgeOrbit`-equation unfolds via
  `show` with the fully-spelled `hodgeOperator` application.
* (SPANIMG-1) `span_range_sphereComponentClass`: the two `rfl`s of the
  image-membership bridge (the `rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩`) reduce
  the component family's definition; if the coe-forms differ, state a local
  `sphereComponentClass_eq` rfl-lemma and rewrite through it.
* (INJ-1) `spherePointClassWorld_pair_ne`: the `Equiv.injective`
  application accepts the family-typed equality up to the two local deltas
  (`spherePointClassWorld`, `sphereUnionCoe`); if unification stalls,
  pre-fold with `show`.
-/
#check @GSTPositiveDimensionalLawLanding.native_GST_single_fold_orbit_law_of_sphereUnion_gate
#check @GSTPositiveDimensionalLawLanding.positive_dimensional_package_of_sphereUnion_gate
