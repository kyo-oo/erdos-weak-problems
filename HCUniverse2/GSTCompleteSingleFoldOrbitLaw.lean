import HCUniverse2.GSTUnifiedNativeWorldFamilyLaw
import HCUniverse2.GSTPositiveDimensionalLiveWeightLaw
import HCUniverse2.GSTFiniteLineGeneralMLaw

/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.

# THE COMPLETE SINGLE-FOLD ORBIT LAW — THE FINAL COMPOSITION CAPSTONE

THE LAW: `NativeGSTSingleFoldOrbitLaw` — the owner's single GST fold orbit
law (GSTHodgeSingleHypothesisConditional.lean:50) — ONE genuinely realized
native/cohomological correspondence word and ONE genuine algebraic native
seed at every Hodge weight, with a cyclic orbit.

This module is the FINAL COMPOSITION: the four certified discharge routes
of the campaign merged into one complete law, one complete consequence
chain, and one master package.  Every route below is a kernel-certified
theorem of the corpus; the composition adds the union — the complete
domain on which the law is discharged today, stated as one theorem family.

## THE FOUR ROUTES (the complete-domain ledger)

ROUTE 1 — THE UNIFIED NATIVE WORLD FAMILY (UNCONDITIONAL, INFINITE).
  Every member of `NativeGSTWorld` satisfies the law: the `n + 1`-point
  world at every `n` (the general-N lane, CI-green run 44290094898) and
  the twelve-point fold world (CI-green run 44182950667), unified by the
  Wave-62 capstone (CI-green run 44756915591 at 4188c31).  The family is
  infinite (`NativeGSTWorld_fin_injective`, axiom-free).  The certificates
  are explicit: the cyclic shift word with the 0-th point-cycle seed (the
  orbit IS the indicator family; the live weight-0 fiber of rank N is
  spanned), the 26-letter twelve-cell fold word (Krylov determinant
  -1149656584000 ≠ 0), and the empty word at every dead weight.

ROUTE 2 — THE LIVE-CORE EXTENSION (ANY WORLD, TWO CERTIFICATES + STASH).
  The Wave-46 merged law (CI-green run 44545624743), restated by Wave-62:
  ANY smooth projective complex world carrying a Krylov-cyclic certificate
  at each live weight (0 and 1) and the stash bigrading at every weight
  p ≥ 2 satisfies the SAME law.  The family law is not a cage — the law
  and the gated worlds share one statement.

ROUTE 3 — THE ONE-LINE POSITIVE-DIMENSIONAL WORLD (THE LIVE WEIGHT BORNE).
  The Wave-63 law (CI-green run 44844378079 at 1cfb58f): a smooth
  projective complex world whose analytification carries the honest
  one-sphere space (the Riemann sphere), with the honest nonzero
  degree-two sphere class and the honest nonzero 0- and codimension-1
  seeds, ASSEMBLES a genuine Hodge datum satisfying the FULL law — the
  weight-one fiber LIVE of the honest sphere class (the
  positive-dimensional live weight), weight zero live of rank one, every
  weight p ≥ 2 honestly dead — with the exact-Hodge consequence.

ROUTE 4 — THE GENERAL-M FINITE-LINE WORLD (EVERY M ≥ 1, THE FROZEN
  PLUG-IN GATES).  The Wave-68 capstone body (CI-green run 44928010015 at
  dc31a62): the finite-line world — M disjoint projective lines with the
  M-cycle fold — carries the FULL law at every M ≥ 1, with the assembled
  Hodge data (span@1 / stash@0 / stash@p≥2) and the two M-cycle letters
  rotating the two honest families.  The world carrier, the
  analytification receipt, and the letter realizations are the frozen
  plug-in inputs of the certified body (the campaign's own doctrine: each
  landing gate discharges one hypothesis of THIS body).

## THE CONSEQUENCE CHAIN (complete domain)

Wherever the law holds, the repository's conditional chain lands:
`EveryHodgeClassIsRationalAlgebraic` and
`EveryHodgeClassIsFiniteRationalCombination` through
`exactHodge_of_one_GST_fold_orbit`; the exact-Hodge consequence, the
native⇒typed FS bridge at every family member and every weight, and the
no-free-lunch receipt — a genuine algebraic 0-cycle with nonzero Hodge
class at the live weight of every family member.

## Honesty ledger

Every statement is proved UNCONDITIONALLY given the named inputs of each
route (Route 1 has none; Routes 2-4 carry their route's certified gate
inputs verbatim from their green modules).  No `sorry`, no new axioms, no
`native_decide`.  Every proof is an exact composition of kernel-certified
corpus theorems (the Wave-62 discipline).  The GitHub CI lane
`gst-complete-single-fold-orbit-law.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional
open GSTNativeSingleFoldOrbitLawLanding
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLiveCoreKit
open GSTPositiveDimensionalLiveCoreLaw
open GSTFinitePointHodgeData
open GSTPositiveDimensionalLawLanding
open GSTPositiveDimensionalLiveWeightLaw
open GSTCyclicOrbitSpan
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion
open GSTFiniteLineGeneralMLaw
open GSTUnifiedNativeWorldFamilyLaw

namespace GSTCompleteSingleFoldOrbitLaw

/-! ## §1 THE FOUR ROUTES -/

/-- **ROUTE 1 — THE UNIFIED NATIVE WORLD FAMILY LAW.**  Every member of
the campaign's world family satisfies the owner's single-fold orbit law
(the Wave-62 capstone, consumed verbatim). -/
theorem complete_route_one_family :
    ∀ w : NativeGSTWorld,
      NativeGSTSingleFoldOrbitLaw
        (NativeGSTWorld.carrier w) (NativeGSTWorld.hodgeData w) :=
  native_gst_unified_world_family_orbit_law

/-- **ROUTE 2 — THE LIVE-CORE EXTENSION.**  Any world carrying the two
Krylov-cyclic live certificates (weights 0 and 1) and the stash bigrading
at every weight `p ≥ 2` satisfies the SAME law (the Wave-46 merged law
through the Wave-62 restatement, consumed verbatim). -/
theorem complete_route_two_live_core
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V)
    (h0cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0,
      C.IsKrylovCyclic)
    (h1cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 1,
      C.IsKrylovCyclic)
    (hstash : ∀ p : ℕ, 1 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p)) :
    NativeGSTSingleFoldOrbitLaw V H :=
  native_gst_unified_family_live_core_extension h0cyc h1cyc hstash

/-- **ROUTE 3 — THE ONE-LINE POSITIVE-DIMENSIONAL WORLD.**  A world whose
analytification carries the honest one-sphere space, with the honest
nonzero sphere class and the honest nonzero seeds, assembles a genuine
Hodge datum satisfying the FULL law with the live weight-one witness and
the exact-Hodge consequence (the Wave-63 law, consumed verbatim). -/
theorem complete_route_three_one_line
    (V : SmoothProjectiveComplexScheme)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace 1))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    ∃ H : HodgeBigradedBettiData V,
      NativeGSTSingleFoldOrbitLaw V H ∧
      (∃ x ∈ rationalHodgeSubspace (H.hodgeBigrading 1), x ≠ 0) ∧
      EveryHodgeClassIsRationalAlgebraic H :=
  positive_dimensional_live_weight_law (V := V) A hspace ω hω Z₀ hZ₀ Z₁ hZ₁

/-- **ROUTE 4 — THE GENERAL-M FINITE-LINE WORLD.**  The finite-line world
— the gated carrier of the M disjoint projective lines with the M-cycle
fold, the honest sphere-union analytification, the assembled Hodge data,
and the two M-cycle letters — satisfies the FULL law at EVERY M ≥ 1 (the
Wave-68 capstone body, consumed verbatim). -/
theorem complete_route_four_general_M (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme)
    (hWX : V.X = finiteLineScheme M)
    (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
      (spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω j) =
      spherePointClassWorld (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M hspace ω
        (cyclicPred M j))
    (R₀ : RealizedFiniteClosedCorrespondence V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
      (sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace j) =
      sphereComponentClass (V := V)
        (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
        (Nat.pos_of_neZero ‹_›) hspace (cyclicPred M j)) :
    NativeGSTSingleFoldOrbitLaw V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) :=
  native_GST_single_fold_orbit_law_finiteLine M V hWX hWmap A hspace ω
    Z₀ hZ₀ Z₁ hZ₁ R₁ hR₁ R₀ hR₀

/-! ## §2 THE COMPLETE-DOMAIN PROPOSITIONS -/

/-- **THE COMPLETE-DOMAIN LAW PROPOSITION.**  The owner's law holds on
all four certified routes: the infinite unified world family
(unconditionally), the live-core extension (any world with the two cyclic
live certificates and the stash bigrading), the one-line
positive-dimensional world (the honest one-sphere shape with the honest
sphere class and seeds), and the general-M finite-line world at every
`M ≥ 1` (the frozen plug-in gates of the Wave-68 certified body). -/
def NativeGSTCompleteLawDomain : Prop :=
  (∀ w : NativeGSTWorld,
    NativeGSTSingleFoldOrbitLaw
      (NativeGSTWorld.carrier w) (NativeGSTWorld.hodgeData w)) ∧
  (∀ (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V)
      (h0cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0,
        C.IsKrylovCyclic)
      (h1cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 1,
        C.IsKrylovCyclic)
      (hstash : ∀ p : ℕ, 1 < p →
        H.hodgeBigrading p =
          stashBigrading
            (RationalSingularCohomology H.analytification (2 * p)) (2 * p)),
    NativeGSTSingleFoldOrbitLaw V H) ∧
  (∀ (V : SmoothProjectiveComplexScheme) (A : AnalytificationData V)
      (hspace : A.space = TopCat.of (sphereUnionSpace 1))
      (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
      (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
      (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0),
    ∃ H : HodgeBigradedBettiData V,
      NativeGSTSingleFoldOrbitLaw V H ∧
      (∃ x ∈ rationalHodgeSubspace (H.hodgeBigrading 1), x ≠ 0) ∧
      EveryHodgeClassIsRationalAlgebraic H) ∧
  (∀ (M : ℕ) (hM : NeZero M) (V : SmoothProjectiveComplexScheme)
      (hWX : V.X = finiteLineScheme M)
      (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M)
      (A : AnalytificationData V)
      (hspace : A.space = TopCat.of (sphereUnionSpace M))
      (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
      (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
      (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0)
      (R₁ : RealizedFiniteClosedCorrespondence V
        (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 1)
      (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator
        (spherePointClassWorld (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
            hspace ω j) =
        spherePointClassWorld (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
            hspace ω (cyclicPred M j))
      (R₀ : RealizedFiniteClosedCorrespondence V
        (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) 0)
      (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator
        (sphereComponentClass (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
            (Nat.pos_of_neZero ‹_›) hspace j) =
        sphereComponentClass (V := V)
          (H := finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁) M
            (Nat.pos_of_neZero ‹_›) hspace (cyclicPred M j)),
    NativeGSTSingleFoldOrbitLaw V
      (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁))

/-- **THE COMPLETE-DOMAIN CONSEQUENCE PROPOSITION.**  The repository's
conditional chain over the complete domain: exact Hodge and the finite
rational combination form for ANY world carrying the law; the exact-Hodge
consequence at every family member; the native⇒typed FS bridge at every
family member and weight; the no-free-lunch nonzero algebraic seed at
every family member. -/
def NativeGSTCompleteConsequence : Prop :=
  (∀ (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V),
    NativeGSTSingleFoldOrbitLaw V H →
    EveryHodgeClassIsRationalAlgebraic H ∧
      EveryHodgeClassIsFiniteRationalCombination H) ∧
  (∀ w : NativeGSTWorld,
    EveryHodgeClassIsRationalAlgebraic (NativeGSTWorld.hodgeData w)) ∧
  (∀ w : NativeGSTWorld, ∀ p : Nat,
    ∃ D : GSTHypothesisComplete.GSTHypothesisData
        (codimensionCycles (NativeGSTWorld.carrier w).X p)
        (RationalSingularCohomology
          (NativeGSTWorld.hodgeData w).analytification (2 * p)),
      GSTHypothesisComplete.GSTHypothesisComplete D ∧
      D.hodgeFiber = rationalHodgeSubspace
        ((NativeGSTWorld.hodgeData w).hodgeBigrading p)) ∧
  (∀ w : NativeGSTWorld,
    ∃ Z : codimensionCycles (NativeGSTWorld.carrier w).X 0,
      (NativeGSTWorld.hodgeData w).cycleClass 0 Z ∈
        rationalHodgeSubspace
          ((NativeGSTWorld.hodgeData w).hodgeBigrading 0) ∧
        (NativeGSTWorld.hodgeData w).cycleClass 0 Z ≠ 0)

/-! ## §3 THE COMPLETE LAW — the discharge -/

/-- **THE COMPLETE SINGLE-FOLD ORBIT LAW.**  The complete domain of the
owner's law, as one theorem: the law holds on every member of the
infinite unified world family (unconditionally), on any world carrying
the live-core certificates (two cyclic certificates + the stash
bigrading), on any world carrying the honest one-sphere analytification
with the honest sphere class and seeds (the positive-dimensional live
weight borne), and on the general-M finite-line world with its frozen
plug-in gates at every `M ≥ 1`. -/
theorem native_gst_single_fold_orbit_law_complete :
    NativeGSTCompleteLawDomain := by
  refine ⟨complete_route_one_family, ?_, ?_, ?_⟩
  · intro V H h0cyc h1cyc hstash
    exact complete_route_two_live_core V H h0cyc h1cyc hstash
  · intro V A hspace ω hω Z₀ hZ₀ Z₁ hZ₁
    exact complete_route_three_one_line V A hspace ω hω Z₀ hZ₀ Z₁ hZ₁
  · intro M hM V hWX hWmap A hspace ω Z₀ hZ₀ Z₁ hZ₁ R₁ hR₁ R₀ hR₀
    haveI : NeZero M := hM
    exact complete_route_four_general_M M V hWX hWmap A hspace ω Z₀ hZ₀ Z₁ hZ₁
      R₁ hR₁ R₀ hR₀

/-- **THE COMPLETE CONSEQUENCE CHAIN.**  Wherever the law holds, the
repository's conditional consequences land: exact Hodge and the finite
rational combination form for ANY world carrying the law; the exact-Hodge
consequence, the native⇒typed FS bridge (every member, every weight), and
the no-free-lunch nonzero algebraic seed for every family member. -/
theorem native_gst_single_fold_orbit_law_complete_consequences :
    NativeGSTCompleteConsequence :=
  ⟨fun V H hlaw =>
      ⟨exactHodge_of_one_GST_fold_orbit hlaw,
        finiteRationalCombination_of_one_GST_fold_orbit hlaw⟩,
    native_gst_unified_world_family_exactHodge,
    native_gst_unified_world_family_FS,
    native_gst_unified_world_family_nonzero_seed⟩

/-! ## §4 THE MASTER PACKAGE — the complete receipt -/

/-- **THE COMPLETE SINGLE-FOLD ORBIT LAW PACKAGE.**  The master receipt:
the complete law on all four routes, the complete consequence chain, and
the family's infinitude — one theorem. -/
theorem the_complete_single_fold_orbit_law_package :
    NativeGSTCompleteLawDomain ∧ NativeGSTCompleteConsequence ∧
      Function.Injective (NativeGSTWorld.fin) :=
  ⟨native_gst_single_fold_orbit_law_complete,
    native_gst_single_fold_orbit_law_complete_consequences,
    NativeGSTWorld_fin_injective⟩

/-! ## §5 Receipts -/

#check complete_route_one_family
#check complete_route_two_live_core
#check complete_route_three_one_line
#check complete_route_four_general_M
#check NativeGSTCompleteLawDomain
#check NativeGSTCompleteConsequence
#check native_gst_single_fold_orbit_law_complete
#check native_gst_single_fold_orbit_law_complete_consequences
#check the_complete_single_fold_orbit_law_package

#print axioms complete_route_one_family
#print axioms complete_route_two_live_core
#print axioms complete_route_three_one_line
#print axioms complete_route_four_general_M
#print axioms native_gst_single_fold_orbit_law_complete
#print axioms native_gst_single_fold_orbit_law_complete_consequences
#print axioms the_complete_single_fold_orbit_law_package

end GSTCompleteSingleFoldOrbitLaw

end -- noncomputable section
