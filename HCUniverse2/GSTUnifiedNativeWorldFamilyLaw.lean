/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTFinitePointLawLanding
import HCUniverse2.GSTTwelvePointLawLanding
import HCUniverse2.GSTPositiveDimensionalLiveCoreLaw
import HCUniverse2.GSTHodgeSingleHypothesisConditional

/-!
# THE UNIFIED NATIVE WORLD FAMILY LAW — THE COMBINATION CAPSTONE

THE NEW LAW of this module: `NativeGSTWorld` — the campaign's own type of
genuine CI-green geometric worlds — and the unified discharge: the owner's
`NativeGSTSingleFoldOrbitLaw` holds on EVERY member of the family.

This module COMBINES the branch's certified lanes (the corpus's own
combination law — the five-file merge, one new theorem family):

* FROM `GSTFinitePointLawLanding.lean` (the general-N lane, CI-green run
  44290094898): `finitePoint_law` at every `N ≥ 1`, the shift-word
  certificate, the point-0 seed, the dead-weight discipline;
* FROM `GSTTwelvePointLawLanding.lean` (the first genuine world): the
  twelve-point fold world — `twelvePoint_law`, the 26-letter fold word,
  the two-point seed;
* FROM `GSTPositiveDimensionalLiveCoreLaw.lean` (the wave-46 merged law,
  CI-green run 44545624743): the positive-dimensional live-core gate,
  restated here as this module's own extension clause — any world with two
  Krylov-cyclic live certificates and the stash bigrading joins the same
  law;
* FROM `GSTHodgeSingleHypothesisConditional.lean` (the law's statement and
  the exact-Hodge conditional chain);
* FROM `GSTNativeSingleFoldOrbitLawLanding.lean` (the native⇒typed FS
  bridge, consumed at the family level through the import chain).

## THE NEW THEOREM FAMILY

* `NativeGSTWorld` — the inductive family type: `fin n` (the `n + 1`-point
  world, the NeZero discipline for free) and `twelve` (the twelve-point
  fold world);
* `NativeGSTWorld.carrier` / `NativeGSTWorld.hodgeData` — the family's
  carrier and Hodge-data maps;
* `native_gst_unified_world_family_orbit_law` — THE LAW: every member
  satisfies `NativeGSTSingleFoldOrbitLaw`;
* `native_gst_unified_world_family_exactHodge` — every member's Hodge
  classes are rational algebraic (the repository's conditional chain,
  family-wide);
* `native_gst_unified_world_family_FS` — the typed FS law at every member
  and every weight;
* `native_gst_unified_world_family_dead_weight_one` — the dead-weight
  receipt at every member;
* `native_gst_unified_world_family_nonzero_seed` — the no-free-lunch
  receipt at every member (a genuine algebraic 0-cycle with nonzero Hodge
  class at the live weight);
* `NativeGSTWorld_fin_injective` — the family is infinite;
* `native_gst_unified_family_live_core_extension` — the positive
  dimensional live-core extension: the family law is not a cage;
* `the_unified_native_world_family_package` — the master capstone receipt.

## Scope (audit-accurate)

The family's members are zero-dimensional worlds with canonical discrete
Hodge data: the discharge's content is the genuine spanning cyclicity at
the live weight-0 fiber (rank `N` / rank 12), honestly earned.  The
positive-dimensional live weights (`p ≥ 1` with `H^{2p} ≠ 0`) remain the
gated frontier (the live-core extension clause + the sphere-union gate
lane); this is a restricted-class theorem, not the Hodge conjecture.
No `sorry`, no new axioms, no `native_decide`; the GitHub CI lane
`gst-unified-native-world-family.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional
open GSTNativeSingleFoldOrbitLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTPositiveDimensionalLiveCoreLaw
open GSTFinitePointWorldCarrier
open GSTFinitePointAnalytification
open GSTFinitePointCohomology
open GSTFinitePointHodgeData
open GSTFinitePointShiftWord
open GSTFinitePointLawLanding
open GSTTwelvePointWorldCarrier
open GSTTwelvePointAnalytification
open GSTTwelvePointCohomology
open GSTTwelvePointHodgeData
open GSTTwelvePointFoldWord
open GSTTwelvePointLawLanding

namespace GSTUnifiedNativeWorldFamilyLaw

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## §1 THE NATIVE GST WORLD FAMILY — the campaign's own world type -/

/-- **THE NATIVE GST WORLD FAMILY.**  The inductive type of the campaign's
CI-green genuine worlds: one member per finite point-count `n + 1` (the
NeZero discipline for free), plus the twelve-point fold world. -/
inductive NativeGSTWorld : Type where
  /-- The `(n + 1)`-point world (every finite point-count ≥ 1). -/
  | fin (n : ℕ) : NativeGSTWorld
  /-- The twelve-point fold world (the first genuine world). -/
  | twelve : NativeGSTWorld

/-- **THE CARRIER MAP.**  Every member IS a genuine smooth projective
complex scheme of the campaign. -/
noncomputable def NativeGSTWorld.carrier : NativeGSTWorld →
    SmoothProjectiveComplexScheme
  | .fin n => finitePointWorld (n + 1)
  | .twelve => twelvePointWorld

/-- **THE HODGE-DATA MAP.**  Every member carries its genuine canonical
discrete Hodge bigraded Betti data. -/
noncomputable def NativeGSTWorld.hodgeData : (w : NativeGSTWorld) →
    HodgeBigradedBettiData (NativeGSTWorld.carrier w)
  | .fin n => finitePointHodgeData (n + 1)
  | .twelve => twelvePointHodgeData

/-! ## §2 THE LAW — every member of the family -/

/-- **THE UNIFIED NATIVE WORLD FAMILY ORBIT LAW.**  The owner's single-fold
orbit law holds on EVERY member of the family — the general-N lane's
discharge at `fin n`, the twelve-point lane's discharge at `twelve`. -/
theorem native_gst_unified_world_family_orbit_law :
    ∀ w : NativeGSTWorld,
      NativeGSTSingleFoldOrbitLaw
        (NativeGSTWorld.carrier w) (NativeGSTWorld.hodgeData w) := by
  intro w
  cases w with
  | fin n =>
      show NativeGSTSingleFoldOrbitLaw
        (finitePointWorld (n + 1)) (finitePointHodgeData (n + 1))
      exact GSTFinitePointLawLanding.finitePoint_law (n + 1)
  | twelve =>
      show NativeGSTSingleFoldOrbitLaw twelvePointWorld twelvePointHodgeData
      exact GSTTwelvePointLawLanding.twelvePoint_law

/-! ## §3 THE CONSEQUENCE CHAIN — family-wide -/

/-- **EXACT HODGE, FAMILY-WIDE.**  Every member's prescribed rational Hodge
class is the class of an actual native codimension-p cycle — the
repository's conditional chain, applied at every member.  Honest scope:
on a zero-dimensional member every rational class is `(0,0)`-type and the
degree map is an iso, so this carries no transcendental content; the
content of the law it consumes is the N-cell spanning at weight 0. -/
theorem native_gst_unified_world_family_exactHodge :
    ∀ w : NativeGSTWorld,
      EveryHodgeClassIsRationalAlgebraic (NativeGSTWorld.hodgeData w) :=
  fun w => GSTHodgeSingleHypothesisConditional.exactHodge_of_one_GST_fold_orbit
    (native_gst_unified_world_family_orbit_law w)

/-- **THE TYPED FS LAW, FAMILY-WIDE.**  For every member and every weight: a
genuine typed `GSTHypothesisData` over the native cycle module and the
rational singular cohomology whose complete GST hypothesis holds with the
GENUINE rational Hodge fiber of that weight — the native⇒typed bridge,
fed at the family level. -/
theorem native_gst_unified_world_family_FS :
    ∀ w : NativeGSTWorld, ∀ p : Nat,
      ∃ D : GSTHypothesisComplete.GSTHypothesisData
          (codimensionCycles (NativeGSTWorld.carrier w).X p)
          (RationalSingularCohomology
            (NativeGSTWorld.hodgeData w).analytification (2 * p)),
        GSTHypothesisComplete.GSTHypothesisComplete D ∧
        D.hodgeFiber = rationalHodgeSubspace
          ((NativeGSTWorld.hodgeData w).hodgeBigrading p) :=
  fun w => GSTNativeSingleFoldOrbitLawLanding.gst_FS_of_native_law
    (native_gst_unified_world_family_orbit_law w)

/-- **THE DEAD-WEIGHT RECEIPT, FAMILY-WIDE.**  Weight 1 is dead at every
member (`H² = 0` by dimension) — the zero-dimensional honesty ledger. -/
theorem native_gst_unified_world_family_dead_weight_one :
    ∀ w : NativeGSTWorld,
      Subsingleton
        (ClassicalHodgeFiber (NativeGSTWorld.carrier w)
          (NativeGSTWorld.hodgeData w) 1) := by
  intro w
  cases w with
  | fin n =>
      show Subsingleton
        (ClassicalHodgeFiber (finitePointWorld (n + 1))
          (finitePointHodgeData (n + 1)) 1)
      exact GSTFinitePointHodgeData.deadFiber_subsingleton (n + 1) 1
        (by omega)
  | twelve =>
      show Subsingleton
        (ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData 1)
      exact GSTTwelvePointHodgeData.deadFiber_subsingleton 1 (by norm_num)

/-! ## §4 THE NO-FREE-LUNCH RECEIPT — family-wide -/

/-- **THE NO-FREE-LUNCH RECEIPT, FAMILY-WIDE.**  Every member carries a
genuine algebraic 0-cycle with nonzero Hodge class at the live weight —
the honest cyclicity witness (cyclicity at a live weight forces exactly
this). -/
theorem native_gst_unified_world_family_nonzero_seed :
    ∀ w : NativeGSTWorld,
      ∃ Z : codimensionCycles (NativeGSTWorld.carrier w).X 0,
        (NativeGSTWorld.hodgeData w).cycleClass 0 Z ∈
          rationalHodgeSubspace
            ((NativeGSTWorld.hodgeData w).hodgeBigrading 0) ∧
        (NativeGSTWorld.hodgeData w).cycleClass 0 Z ≠ 0 := by
  intro w
  cases w with
  | fin n =>
      show ∃ Z : codimensionCycles (finitePointWorld (n + 1)).X 0,
        (finitePointHodgeData (n + 1)).cycleClass 0 Z ∈
          rationalHodgeSubspace
            ((finitePointHodgeData (n + 1)).hodgeBigrading 0) ∧
        (finitePointHodgeData (n + 1)).cycleClass 0 Z ≠ 0
      exact ⟨GSTFinitePointLawLanding.finitePointSeedCycle (n + 1),
        GSTFinitePointLawLanding.finitePointSeed_hodge (n + 1),
        GSTFinitePointLawLanding.finitePointSeed_class_ne_zero (n + 1)⟩
  | twelve =>
      show ∃ Z : codimensionCycles twelvePointWorld.X 0,
        twelvePointHodgeData.cycleClass 0 Z ∈
          rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) ∧
        twelvePointHodgeData.cycleClass 0 Z ≠ 0
      exact ⟨GSTTwelvePointLawLanding.twelvePointSeedCycle,
        GSTTwelvePointLawLanding.twelvePointSeed_hodge,
        GSTTwelvePointLawLanding.twelvePointSeed_class_ne_zero⟩

/-! ## §5 THE FAMILY IS INFINITE -/

/-- **THE FAMILY IS INFINITE.**  One genuine member per natural number —
the constructor is injective, so the family hosts a distinct genuine world
at every finite point-count. -/
theorem NativeGSTWorld_fin_injective :
    Function.Injective (NativeGSTWorld.fin) := by
  intro a b h
  injection h with h'

/-! ## §6 THE LIVE-CORE EXTENSION — the family law is not a cage -/

/-- **THE POSITIVE-DIMENSIONAL LIVE-CORE EXTENSION.**  Any world carrying
the positive-dimensional live-core gates — a Krylov-cyclic certificate at
each live weight (0 and 1) and the stash bigrading at every weight `p ≥ 2` —
satisfies the SAME single-fold orbit law: the live-core lane's merged law,
restated as this module's own extension clause.  The family and the gated
frontier share one law. -/
theorem native_gst_unified_family_live_core_extension
    (h0cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0,
      C.IsKrylovCyclic)
    (h1cyc : ∃ C : RealizedCorrespondenceKrylovCertificate V H 1,
      C.IsKrylovCyclic)
    (hstash : ∀ p : ℕ, 1 < p →
      H.hodgeBigrading p =
        stashBigrading
          (RationalSingularCohomology H.analytification (2 * p)) (2 * p)) :
    NativeGSTSingleFoldOrbitLaw V H :=
  GSTPositiveDimensionalLiveCoreLaw.positive_dimensional_live_core_law
    h0cyc h1cyc hstash

/-! ## §7 THE MASTER CAPSTONE — THE UNIFIED FAMILY PACKAGE -/

/-- **THE UNIFIED NATIVE WORLD FAMILY PACKAGE.**  The complete receipt of
the combination: the law at every member, the exact-Hodge consequence at
every member, the typed FS law at every member and weight, the
dead-weight receipt at every member, the no-free-lunch nonzero algebraic
class at every member, and the family's infinitude. -/
theorem the_unified_native_world_family_package :
    (∀ w : NativeGSTWorld,
      NativeGSTSingleFoldOrbitLaw
        (NativeGSTWorld.carrier w) (NativeGSTWorld.hodgeData w)) ∧
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
      Subsingleton
        (ClassicalHodgeFiber (NativeGSTWorld.carrier w)
          (NativeGSTWorld.hodgeData w) 1)) ∧
    (∀ w : NativeGSTWorld,
      ∃ Z : codimensionCycles (NativeGSTWorld.carrier w).X 0,
        (NativeGSTWorld.hodgeData w).cycleClass 0 Z ∈
          rationalHodgeSubspace
            ((NativeGSTWorld.hodgeData w).hodgeBigrading 0) ∧
        (NativeGSTWorld.hodgeData w).cycleClass 0 Z ≠ 0) ∧
    Function.Injective (NativeGSTWorld.fin) :=
  ⟨native_gst_unified_world_family_orbit_law,
    native_gst_unified_world_family_exactHodge,
    native_gst_unified_world_family_FS,
    native_gst_unified_world_family_dead_weight_one,
    native_gst_unified_world_family_nonzero_seed,
    NativeGSTWorld_fin_injective⟩

/-! ## §8 Receipts -/

#check NativeGSTWorld.carrier
#check NativeGSTWorld.hodgeData
#check native_gst_unified_world_family_orbit_law
#check native_gst_unified_world_family_exactHodge
#check native_gst_unified_world_family_FS
#check native_gst_unified_world_family_dead_weight_one
#check native_gst_unified_world_family_nonzero_seed
#check NativeGSTWorld_fin_injective
#check native_gst_unified_family_live_core_extension
#check the_unified_native_world_family_package

#print axioms native_gst_unified_world_family_orbit_law
#print axioms native_gst_unified_world_family_exactHodge
#print axioms native_gst_unified_world_family_FS
#print axioms native_gst_unified_world_family_dead_weight_one
#print axioms native_gst_unified_world_family_nonzero_seed
#print axioms NativeGSTWorld_fin_injective
#print axioms native_gst_unified_family_live_core_extension
#print axioms the_unified_native_world_family_package

end GSTUnifiedNativeWorldFamilyLaw
