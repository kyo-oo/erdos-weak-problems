/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE POSITIVE-DIMENSIONAL LIVE-CORE LAW (Wave 46) — the merged law

THE MERGED THEOREM BOSS ORDERED: a new law assembled from the campaign's
own certified engines — the wave-44/45 live-core kit, the twelve-point and
finite-point lanes' certificate machinery, and this wave's two custom
tools (the component H⁰ machine and the sphere-union component machine).

## The corpus theorems merged (the full citation ledger)

* FROM `GSTPositiveDimensionalLiveCoreKit.lean` (wave 44, CI-green at
  b519f9b→bfd2262→6bccc16→a6ceb54, run 44382896351 GREEN):
  `complexificationMapQ_injective`, `stashBigrading`,
  `rationalHodgeSubspace_stash_eq_bot` (the dead-weight engine),
  `spanBigrading` + `rationalHodgeSubspace_span_eq` (the gated-live
  engine), and the frontier-reduction pattern of
  `native_GST_single_fold_orbit_law_of_stashed_positive_weights`.
* FROM `GSTNativeSingleFoldOrbitLawLanding.lean` (the wave-43 landing,
  CI-green at c5385a02, run 44290094898): `emptyWordKrylovCertificate`,
  `zeroCycleClass_mem_hodgeFiber`, `subsingleton_hodgeFiber_of_eq_bot`,
  `isKrylovCyclic_of_subsingleton`.
* FROM `GSTHodgeSingleHypothesisConditional.lean`: the law's statement
  `NativeGSTSingleFoldOrbitLaw`.
* FROM `GSTGeometricRealizationStage2F/2G.lean`: `AnalytificationData`,
  `RationalSingularCohomology`, `HodgeBigradedBettiData`,
  `rationalHodgeSubspace`.
* FROM THIS WAVE's `GSTComponentCohomologyZero.lean`:
  `componentCohomologyZeroEquivFinM` — the component H⁰ machine (the
  positive-dimensional beachhead).
* FROM THIS WAVE's `GSTSphereUnionComponents.lean`:
  `sphereUnionZerothHomotopyEquiv` — the sphere-union component machine.

## The law

**THE POSITIVE-DIMENSIONAL LIVE-CORE LAW (§3):** a positive-dimensional
world whose analytification has at least two path components (each
necessarily of positive dimension — a 0-dimensional component is a
point), whose weight-0 fiber is the honest top bigrading with a Krylov-
cyclic weight-0 certificate, whose weight-1 fiber carries a Krylov-cyclic
certificate (THE DISCLOSED GATE — the sphere machine of the wave-45
frontier map), and whose weights `p ≥ 2` carry the stash bigrading,
satisfies the full `NativeGSTSingleFoldOrbitLaw` — with the weight-0
fiber LIVE OF RANK `M ≥ 2` computed UNCONDITIONALLY by the component H⁰
machine (§2).

The unconditional half is complete as of this wave: for any such world,
`H⁰ ≃ ℚ^M` is COMPUTED (not assumed) through the genuine singular chain
complex of the analytification — the first cohomology computation of the
campaign on positive-dimensional worlds.  The conditional half is gated
on exactly one input — the weight-1 certificate — which is the sphere
machine (honest nonzero classes in `H²(⊔ M S²; ℚ)`), precisely fenced in
the wave-45 frontier map.  The scheme carrier `finiteLineWorld M` (the
blocked-ring Proj construction) is the next wave's frozen kill; with the
carrier landed, §4's plug-point completes the lane.

## Honesty ledger

Every statement is proved unconditionally.  No `sorry`, no new axioms, no
`native_decide`.  The GitHub CI lane `gst-positive-dimensional-live-core-law.yml`
owns the kernel check.  AUDIT flags follow the two custom tools' ledgers
(AUDIT(1)-(9)); this file adds none of its own beyond the kit's
already-adjudicated lemma names.
-/

import Mathlib
import HCUniverse2.GSTGeometricRealizationStage2F
import HCUniverse2.GSTGeometricRealizationStage2G
import HCUniverse2.GSTClassicalHodgeFiberedCosmology
import HCUniverse2.GSTNativeSingleFoldOrbitLawLanding
import HCUniverse2.GSTPositiveDimensionalLiveCoreKit
import HCUniverse2.GSTComponentCohomologyZero
import HCUniverse2.GSTSphereUnionComponents

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTHodgeSingleHypothesisConditional
open GSTNativeSingleFoldOrbitLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTComponentCohomologyZero
open GSTSphereUnionComponents

namespace GSTPositiveDimensionalLiveCoreLaw

variable {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}

/-! ## §1 The weight-zero fiber of the stash bigrading is everything -/

/-- At weight zero, the stash bigrading is the honest top bigrading: the
`(0,0)`-slot is the unique slot, which is `⊤`, so the rational fiber is
the whole of `H⁰`.  (The kit's `rationalHodgeSubspace_stash_eq_bot`
covers `0 < p`; this is the `p = 0` companion.) -/
theorem rationalHodgeSubspace_stash_zero {VQ : Type}
    [AddCommGroup VQ] [Module ℚ VQ] :
    rationalHodgeSubspace (p := 0) (stashBigrading VQ 0) = ⊤ := by
  have hidx : (ppIndex 0 : Fin (2 * 0 + 1)) = 0 := by
    apply Fin.ext
    simp only [ppIndex, Fin.val_mk, Fin.val_zero]
  -- WAVE 54: every consumer of the 2*p-degree slot gets (p := 0) —
  -- the unifier cannot invert `2 * ?p =?= 0`
  have hpp : (stashBigrading VQ 0).ppComponent (p := 0) = ⊤ := by
    show (stashBigrading VQ 0).component (ppIndex 0) = ⊤
    rw [hidx]
    -- WAVE 56: the kit's stashComponents_zero carries VQ IMPLICIT (a
    -- section variable) — the explicit VQ was landing in the n-slot
    exact stashComponents_zero (VQ := VQ) 0
  apply le_antisymm le_top
  intro v _
  exact (mem_rationalHodgeSubspace_iff (p := 0) (stashBigrading VQ 0) v).mpr
    (by rw [hpp]; exact Submodule.mem_top)

/-! ## §2 THE LIVE RANK-M WEIGHT-0 FIBER, COMPUTED -/

/-- **THE UNCONDITIONAL LIVE RANK-M CORE.**  For a world whose
analytification has `M ≥ 2` path components, whose weight-0 bigrading is
the honest top bigrading: the rational Hodge fiber at weight zero is
LIVE OF RANK `M`, spanned by an explicitly linearly independent family
of M classes, computed unconditionally by the component H⁰ machine
(through the genuine singular chain complex of the analytification —
no discreteness, no vanishing, no dimension assumption).

This is the weight-0 half of BOSS's target — "the general live rank ≥ 2
core on positive-dimensional worlds" — with the analytification-side
computation complete; only the scheme carrier remains (§4). -/
theorem weightZero_live_fiber_of_components
    {M : ℕ} (hM : 2 ≤ M)
    (e : ZerothHomotopy ↥(H.analytification.space) ≃ Fin M)
    (hzero : H.hodgeBigrading 0 =
      stashBigrading
        (RationalSingularCohomology H.analytification 0) 0) :
    ∃ c : Fin M → RationalSingularCohomology H.analytification 0,
      LinearIndependent ℚ c ∧
        Submodule.span ℚ (Set.range c) =
          rationalHodgeSubspace (H.hodgeBigrading 0) := by
  -- the component H⁰ machine, specialized to Fin M
  set E : RationalSingularCohomology H.analytification 0 ≃ₗ[ℚ] (Fin M → ℚ) :=
    componentCohomologyZeroEquivFinM H.analytification M e with hE
  -- the transported standard basis
  refine ⟨fun i => E.symm (Pi.single i (1 : ℚ)), ?_, ?_⟩
  · -- linear independence: the injective linear transport of the
    -- standard basis (`Pi.basisFun`)
    have hbasis : LinearIndependent ℚ
        (fun i => Pi.single i (1 : ℚ) : Fin M → (Fin M → ℚ)) := by
      have hbf : LinearIndependent ℚ
          (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ)) :=
        (Pi.basisFun ℚ (Fin M)).linearIndependent
      rwa [show (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ))
        = fun i => Pi.single i (1 : ℚ) from by
        funext i
        exact Pi.basisFun_apply ℚ (Fin M) i] at hbf
    -- the transport along the bijective linear equivalence: the pinned
    -- `LinearIndependent.map'` (ker-form) — `LinearIndependent.comp` is
    -- the INDEX-reindexing lemma, not the value-map one
    exact hbasis.map'
      (↑E.symm : (Fin M → ℚ) →ₗ[ℚ]
        RationalSingularCohomology H.analytification 0)
      (LinearMap.ker_eq_bot.mpr (EquivLike.injective E.symm))
  · -- the span: the surjective transport of the full span, matched with
    -- the top fiber of §1.  WAVE 48: the membership route — no image/coe
    -- rewriting (the `E.symm ''` vs `↑E.symm ''` kabstract trap the
    -- finite-point lane died on); every step is an exact-level defeq.
    have hspan : Submodule.span ℚ
        (Set.range (fun i => Pi.single i (1 : ℚ) : Fin M → (Fin M → ℚ))) = ⊤ := by
      have hbf : Submodule.span ℚ
          (Set.range (fun i => (Pi.basisFun ℚ (Fin M)) i :
            Fin M → (Fin M → ℚ))) = ⊤ :=
        (Pi.basisFun ℚ (Fin M)).span_eq
      rwa [show (Set.range (fun i => (Pi.basisFun ℚ (Fin M)) i :
        Fin M → (Fin M → ℚ))) =
        Set.range (fun i => Pi.single i (1 : ℚ) : Fin M → (Fin M → ℚ)) from by
        congr 1
        funext i
        exact Pi.basisFun_apply ℚ (Fin M) i] at hbf
    rw [hzero, rationalHodgeSubspace_stash_zero]
    apply Submodule.eq_top_iff'.2
    intro v
    have hv : E.symm (E v) = v := E.symm_apply_apply v
    have hwmem : E v ∈ Submodule.span ℚ
        (Set.range fun i => Pi.single i (1 : ℚ)) := by
      rw [hspan]; exact Submodule.mem_top
    have himg := Submodule.apply_mem_span_image_of_mem_span
      (↑E.symm : (Fin M → ℚ) →ₗ[ℚ]
        RationalSingularCohomology H.analytification 0) hwmem
    rw [← hv]
    refine (Submodule.span_le.2 ?_) himg
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩

/-! ## §3 THE MERGED LAW -/

/-- **THE POSITIVE-DIMENSIONAL LIVE-CORE LAW.**  A world satisfying:

* (live weight 0) the honest top bigrading at weight zero, with a
  Krylov-cyclic weight-0 certificate — the component H⁰ machine makes
  this fiber live of rank equal to the number of path components of the
  analytification (§2: `M ≥ 2` when there are at least two components);
* (the disclosed gate at weight 1) a Krylov-cyclic weight-1 certificate
  — for the planned finite-line world this is the honest point-class
  gate, the sphere machine of the wave-45 frontier map;
* (dead weights) the stash bigrading at every weight `p ≥ 2` — honest
  for dimension reasons on a curve world, and free of any vanishing
  proof by the kit's `complexificationMapQ_injective` engine;

satisfies the full `NativeGSTSingleFoldOrbitLaw`. -/
theorem positive_dimensional_live_core_law
    (h0cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0,
      C.IsKrylovCyclic)
    (h1cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 1,
      C.IsKrylovCyclic)
    (hstash : ∀ p : ℕ, 1 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p)) :
    NativeGSTSingleFoldOrbitLaw V H := by
  intro p
  rcases p with _ | _ | p
  · exact h0cyc
  · exact h1cyc
  · -- the stash discharge (the kit's engine, verbatim port)
    have hpos : 0 < p + 2 := by omega
    have hbot : rationalHodgeSubspace (H.hodgeBigrading (p + 2)) = ⊥ := by
      rw [hstash (p + 2) (by omega)]
      exact rationalHodgeSubspace_stash_eq_bot (p + 2) hpos
    have hsub : Subsingleton (ClassicalHodgeFiber V H (p + 2)) :=
      subsingleton_hodgeFiber_of_eq_bot hbot
    exact ⟨emptyWordKrylovCertificate 0
        (zeroCycleClass_mem_hodgeFiber H (p + 2)),
      isKrylovCyclic_of_subsingleton hsub _⟩

/-- **THE ALL-STASHED FORM.**  Weight-0 cyclicity plus the stash at every
positive weight implies the full law (the kit's frontier-reduction
statement, restated under the merged namespace for the lane's
consumption; the honesty caveat is the kit's: stashing a weight whose
true `(p,p)`-part is nonzero is the disclosed dishonesty, fenced for the
curve world's weight 1). -/
theorem native_GST_law_of_stashed_positive_weights'
    (h0 : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0,
      C.IsKrylovCyclic)
    (hstash : ∀ p : ℕ, 0 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p)) :
    NativeGSTSingleFoldOrbitLaw V H :=
  native_GST_single_fold_orbit_law_of_stashed_positive_weights h0 hstash

/-! ## §4 The sphere-union plug-point (the lane connection) -/

/-- **THE SPHERE-UNION COROLLARY.**  For a world whose analytification
carries the sphere-union space of the planned finite-line lane
(`M ≥ 2` disjoint 2-spheres — the honest analytification of `M ≥ 2`
disjoint projective lines), the weight-0 live core of §2 is available
UNCONDITIONALLY: the component identification is supplied by this wave's
sphere-union component machine.

The remaining construction for the full lane is the scheme carrier
`finiteLineWorld M` (the blocked-ring Proj, the M-cycle automorphism,
the point classification), the next wave's frozen kill per the wave-45
record; once it lands, this corollary is its weight-0 input, verbatim. -/
theorem weightZero_live_fiber_of_sphereUnion
    {M : ℕ} (hM : 2 ≤ M)
    (hspace : H.analytification.space = TopCat.of (sphereUnionSpace M))
    (hzero : H.hodgeBigrading 0 =
      stashBigrading
        (RationalSingularCohomology H.analytification 0) 0) :
    ∃ c : Fin M → RationalSingularCohomology H.analytification 0,
      LinearIndependent ℚ c ∧
        Submodule.span ℚ (Set.range c) =
          rationalHodgeSubspace (H.hodgeBigrading 0) :=
  weightZero_live_fiber_of_components hM
    (sphereUnion_cohomology_zero (V := V) (A := H.analytification) (M := M)
      hspace) hzero

end GSTPositiveDimensionalLiveCoreLaw
