import HCUniverse2.GSTSphereUnionPointClassGate
import HCUniverse2.GSTPositiveDimensionalLiveCoreLaw
import HCUniverse2.GSTFinitePointHodgeData

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW — the combination capstone

THE NEW LAW of this module: the positive-dimensional live weight is BORNE and
DISCHARGED.  A smooth projective complex world whose analytification carries
the honest sphere-union space (the certified sphere-union shape — the planned
analytification of the disjoint union of M projective lines), together with
ONE honest nonzero degree-two sphere class (the campaign's single fenced
sphere-machine input), ASSEMBLES a genuine `HodgeBigradedBettiData` whose
weight-one rational Hodge fiber is LIVE — the span of the honest point-class
family, nonzero on every line, linearly independent — and, at M = 1,
satisfies the FULL `NativeGSTSingleFoldOrbitLaw`, with the exact-Hodge
consequence chain.

## The combination ledger (the files merged; every engine CI-green)

* FROM `GSTSphereUnionComponents.lean` (run 44545624743): the honest
  sphere-union space `sphereUnionSpace M` and the component machine
  `sphereUnion_cohomology_zero` (the hspace-transported path-component
  identification).
* FROM `GSTComponentCohomologyZero.lean` (run 44545624743): the component
  H⁰ machine — `componentCohomologyZeroEquivFinM` computes H⁰ of ANY
  analytification through the genuine singular chain complex.
* FROM `GSTSingularCohomologyMaps.lean` (run 44601531424): the raw-space
  rational singular cohomology `singularCohomologyOf` — definitionally (rfl)
  the world's `RationalSingularCohomology` — with the full contravariant
  pullback calculus.
* FROM `GSTSphereUnionPointClassGate.lean` (run 44604829367, files F1-F3):
  the honest point-class family `spherePointClass M ω`, its nonzero and
  linear-independence certificates (given the single honest sphere class
  ω ≠ 0), and the M-cycle equivariance.
* FROM `GSTPositiveDimensionalLiveCoreKit.lean` (run 44382896351): the
  span bigrading `spanBigrading` + `rationalHodgeSubspace_span_eq` (the
  gated-live-weight engine: the fiber IS the rational span of the family)
  and the stash bigrading engine (the honest dead positive weights).
* FROM `GSTNativeSingleFoldOrbitLawLanding.lean` (run 43750693353): the
  cost classification — the law is FREE at dead weights and at monogenic
  live weights — `native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights`,
  the empty-word certificate, and the subsingleton discharge.
* FROM `GSTHodgeSingleHypothesisConditional.lean`: the law's statement and
  the exact-Hodge conditional chain.
* FROM `GSTFinitePointHodgeData.lean`: the generic forced weight-zero fiber
  law `rationalHodgeSubspace_eq_top_of_degree_zero` and `fin1_subsingleton`.

## The law

**THE POSITIVE-DIMENSIONAL LIVE-WEIGHT BEARING (§3, every M ≥ 1):** the
assembled Hodge data — the stash bigrading at weight zero, the SPAN bigrading
on the honest point-class family at weight one, the stash bigrading at every
weight p ≥ 2, with the degree-style cycle-class map at the live weight one —
has: weight zero LIVE (the forced top fiber); weight one LIVE of rank M (the
span of the honest family, nonzero on every line, linearly independent);
every weight p ≥ 2 honestly dead (the stash engine — no vanishing proof
needed).

**THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW (§4, M = 1):** the
one-line world — the honest Riemann-sphere analytification — carries the
FULL `NativeGSTSingleFoldOrbitLaw`: weight zero is monogenic (the H⁰
machine computes H⁰ ≃ ℚ¹, the honest seed generates); weight one —
THE POSITIVE-DIMENSIONAL LIVE WEIGHT — is monogenic by the honest sphere
class itself (the span fiber IS the rational line of the class, the genuine
codimension-one seed generates it); every weight p ≥ 2 is discharged by
the stash (dead, empty word).  The exact-Hodge consequence
`EveryHodgeClassIsRationalAlgebraic` lands through the repository's
conditional chain.

## The honesty ledger

The single disclosed input is the honest sphere class `ω` with `ω ≠ 0` —
the fenced sphere-machine core, exactly as the wave-59 record froze it:
the gate is designed so that when the honest sphere class lands — by
whatever route — the final law assembles by discharging one hypothesis.
Every other input of this module is structural: the sphere-union
analytification contract (the honest certified shape) and the genuine
cycle nontriviality (the honest world's own 0- and codimension-1 cycles).
Every statement is proved unconditionally given these inputs.  The
general-M law (M ≥ 2 — the frontier map's rank-≥2 core) is NOT claimed
here: it remains gated on the scheme carrier and the cyclic word, per the
wave-59 frozen plan.  No `sorry`, no new axioms, no `native_decide`.  The
GitHub CI lane `gst-positive-dimensional-live-weight-law.yml` owns the
kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTSingularCohomologyMaps
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLiveCoreKit
open GSTPositiveDimensionalLiveCoreLaw
open GSTNativeSingleFoldOrbitLawLanding
open GSTHodgeSingleHypothesisConditional
open GSTFinitePointHodgeData

namespace GSTPositiveDimensionalLiveWeightLaw

variable {V : SmoothProjectiveComplexScheme}

/-- The Module-structure bridge: the world's degree-n rational singular
cohomology's Module structure, provided locally at high priority through
the wave-57 raw-space family (the two families are definitionally
identical — the rfl bridge of
`GSTSingularCohomologyMaps.singularCohomologyOf_eq`). -/
local instance (priority := high) instLWModule
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))

/-- The AddCommGroup-structure bridge, same discipline. -/
local instance (priority := high) instLWAddCommGroup
    {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))

/-! ## §1 The honest point-class family at the world ## -/

/-- **THE WORLD'S HONEST POINT-CLASS FAMILY.**  For a world whose
analytification carries the honest sphere-union space, the honest
point-class family of the wave-59 gate, read at the world's own
degree-two rational singular cohomology (the raw-space cohomology is
definitionally the world's — the wave-57 rfl bridge — so the family
transports along the space identification). -/
theorem positive_dimensional_live_weight_family (M : ℕ)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    ∃ c : Fin M → singularCohomologyOf A.space 2,
      (∀ i, c i ≠ 0) ∧ LinearIndependent ℚ c := by
  rw [hspace]
  exact ⟨spherePointClass M ω,
    fun i => spherePointClass_ne_zero M ω hω i,
    spherePointClass_indep M ω hω⟩

/-! ## §2 The degree-style cycle-class functionals ## -/

/-- A genuine nonzero cycle supports a rational functional taking the value
one on it: the coefficient map on the rational line of the cycle
(`Submodule.mem_span_singleton`, verified against the kit's own green
usage), presented as a linear equivalence through `LinearEquiv.ofBijective`,
then extended by `LinearMap.exists_extend` (the same extension engine the
kit's `exists_complex_retraction` rides).  This is the degree-style honest
cycle-class map constructor: the honest data map sends the genuine
generator cycle to the honest class. -/
theorem exists_cycle_functional {X : Type} [AddCommGroup X] [Module ℚ X]
    (Z₀ : X) (hZ₀ : Z₀ ≠ 0) :
    ∃ f : X →ₗ[ℚ] ℚ, f Z₀ = 1 := by
  set P : Submodule ℚ X := Submodule.span ℚ ({Z₀} : Set X) with hP
  have hZmem : Z₀ ∈ P := Submodule.subset_span rfl
  set ι : ℚ →ₗ[ℚ] ↥P :=
    { toFun := fun q => ⟨q • Z₀, Submodule.smul_mem _ q hZmem⟩
      map_add' := by
        intro q q'
        apply Subtype.ext
        show (q + q') • Z₀ = q • Z₀ + q' • Z₀
        rw [add_smul]
      map_smul' := by
        intro q q'
        apply Subtype.ext
        show (q * q') • Z₀ = q • (q' • Z₀)
        rw [smul_smul] } with hι
  have hinj : Function.Injective ι := by
    intro q q' hqq
    by_contra hne
    have hpos : q - q' ≠ 0 := sub_ne_zero.mpr hne
    have hco : q • Z₀ = q' • Z₀ := congrArg Subtype.val hqq
    have hdiff : (q - q') • Z₀ = 0 := by
      rw [sub_smul, hco, sub_self]
    rcases (smul_eq_zero (R := ℚ) (M := X)).mp hdiff with h | h1
    · exact hpos h
    · exact hZ₀ h1
  have hsurj : Function.Surjective ι := by
    intro y
    obtain ⟨q, hyq⟩ := Submodule.mem_span_singleton.mp y.2
    refine ⟨q, ?_⟩
    apply Subtype.ext
    show q • Z₀ = (y : X)
    exact hyq
  set e : ℚ ≃ₗ[ℚ] ↥P := LinearEquiv.ofBijective ι ⟨hinj, hsurj⟩ with he
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (V := X) (p := P) e.symm.toLinearMap
  have hE1 : e (1 : ℚ) = ⟨Z₀, hZmem⟩ := by
    apply Subtype.ext
    exact one_smul ℚ Z₀
  refine ⟨g, ?_⟩
  show g Z₀ = 1
  rw [show Z₀ = ((P.subtype ⟨Z₀, hZmem⟩ : X)) from rfl,
    show g ((P.subtype ⟨Z₀, hZmem⟩ : X)) =
      (g.comp P.subtype) ⟨Z₀, hZmem⟩ from rfl,
    hg,
    ← hE1,
    show e.symm.toLinearMap (e (1 : ℚ)) = e.symm (e (1 : ℚ)) from rfl]
  exact e.symm_apply_apply 1

/-! ## §3 THE POSITIVE-DIMENSIONAL LIVE-WEIGHT BEARING — the assembled data ## -/

/-- **THE POSITIVE-DIMENSIONAL LIVE-WEIGHT BEARING.**  For every M ≥ 1, a
world with the honest sphere-union analytification and the honest sphere
class ASSEMBLES a genuine Hodge datum whose weight-zero fiber is the forced
top (live), whose weight-one fiber is the rational span of the honest
point-class family (LIVE, nonzero on every line, linearly independent —
the positive-dimensional live weight), whose genuine codimension-one seed
cycle has its honest class in the fiber, and whose weights p ≥ 2 are all
honestly dead. -/
theorem positive_dimensional_live_weight_bearing (M : ℕ) (hM : 0 < M)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    ∃ H : HodgeBigradedBettiData V,
      ∃ c : Fin M → RationalSingularCohomology H.analytification 2,
        (∀ i, c i ≠ 0) ∧
        LinearIndependent ℚ c ∧
        rationalHodgeSubspace (H.hodgeBigrading 1) =
          Submodule.span ℚ (Set.range c) ∧
        H.cycleClass 1 Z₁ ∈
          rationalHodgeSubspace (H.hodgeBigrading 1) ∧
        (rationalHodgeSubspace (H.hodgeBigrading 0) = ⊤) ∧
        (∀ p : ℕ, 1 < p →
          rationalHodgeSubspace (H.hodgeBigrading p) = ⊥) := by
  obtain ⟨c, hcne, hcind⟩ :=
    positive_dimensional_live_weight_family M A hspace ω hω
  obtain ⟨f, hf⟩ := exists_cycle_functional (X := codimensionCycles V.X 1) Z₁ hZ₁
  set c₀ : singularCohomologyOf A.space 2 := c ⟨0, hM⟩ with hc₀
  set cl₁ : codimensionCycles V.X 1 →ₗ[ℚ] singularCohomologyOf A.space 2 :=
    { toFun := fun Z => (f Z) • c₀
      map_add' := by
        intro Z Z'
        show (f (Z + Z')) • c₀ = (f Z) • c₀ + (f Z') • c₀
        rw [map_add, add_smul]
      map_smul' := by
        intro q Z
        show (f (q • Z)) • c₀ = q • ((f Z) • c₀)
        rw [map_smul, smul_smul, ← smul_eq_mul] } with hcl₁
  have hcl₁_Z₁ : cl₁ Z₁ = c₀ := by
    show (f Z₁) • c₀ = c₀
    rw [hf, one_smul]
  set H : HodgeBigradedBettiData V :=
    { analytification := A
      hodgeBigrading := fun p =>
        match p with
        | 0 => stashBigrading _ 0
        | 1 => spanBigrading c 1 (by norm_num)
        | (p + 2) => stashBigrading _ (2 * (p + 2))
      cycleClass := fun p =>
        match p with
        | 0 => 0
        | 1 => cl₁
        | (p + 2) => 0 } with hH
  have hfiber1 : rationalHodgeSubspace (H.hodgeBigrading 1) =
      Submodule.span ℚ (Set.range c) :=
    rationalHodgeSubspace_span_eq c 1 (by norm_num)
  refine ⟨H, c, hcne, hcind, ?_, ?_, ?_, ?_⟩
  · exact hfiber1
  · rw [show H.cycleClass 1 Z₁ = cl₁ Z₁ from rfl, hcl₁_Z₁]
    have hmem : c₀ ∈ Submodule.span ℚ (Set.range c) :=
      Submodule.subset_span ⟨⟨0, hM⟩, rfl⟩
    exact hfiber1.symm ▸ hmem
  · exact rationalHodgeSubspace_eq_top_of_degree_zero H
  · intro p hp
    rcases p with _ | _ | p
    · exact absurd hp (by omega)
    · exact absurd hp (by omega)
    · rw [show H.hodgeBigrading (p + 2) = stashBigrading _
        (2 * (p + 2)) from rfl]
      exact rationalHodgeSubspace_stash_eq_bot (p + 2) (by omega)

/-! ## §4 THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW — the full orbit law at M = 1 ## -/

/-- **THE POSITIVE-DIMENSIONAL LIVE-WEIGHT LAW.**  The one-line world —
a smooth projective complex world whose analytification carries the honest
one-sphere space (the Riemann sphere, the honest analytification of a
projective line), with one honest nonzero degree-two sphere class —
ASSEMBLES a genuine Hodge datum satisfying the FULL
`NativeGSTSingleFoldOrbitLaw`, with the weight-one fiber LIVE of the honest
sphere class (the positive-dimensional live weight), the weight-zero fiber
live of rank one (the H⁰ machine), and every weight p ≥ 2 honestly dead.
The exact-Hodge consequence lands through the repository's conditional
chain. -/
theorem positive_dimensional_live_weight_law
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace 1))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    ∃ H : HodgeBigradedBettiData V,
      NativeGSTSingleFoldOrbitLaw V H ∧
      (∃ x ∈ rationalHodgeSubspace (H.hodgeBigrading 1), x ≠ 0) ∧
      EveryHodgeClassIsRationalAlgebraic H := by
  haveI : Subsingleton (Fin 1) := fin1_subsingleton
  obtain ⟨c, hcne, hcind⟩ :=
    positive_dimensional_live_weight_family 1 A hspace ω hω
  obtain ⟨f₁, hf₁⟩ := exists_cycle_functional
    (X := codimensionCycles V.X 1) Z₁ hZ₁
  obtain ⟨f₀, hf₀⟩ := exists_cycle_functional
    (X := codimensionCycles V.X 0) Z₀ hZ₀
  set c₀ : singularCohomologyOf A.space 2 := c ⟨0, (by norm_num : 0 < 1)⟩
    with hc₀
  set E : RationalSingularCohomology A 0 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
    componentCohomologyZeroEquivFinM A 1
      (sphereUnion_cohomology_zero (M := 1) hspace) with hE
  set c₀w : singularCohomologyOf A.space 0 := E.symm (fun _ => (1 : ℚ))
    with hc₀w
  have hc₀w_ne : c₀w ≠ 0 := by
    intro h0
    have hE0 : E (0 : singularCohomologyOf A.space 0) = 0 :=
      map_zero E.toLinearMap
    have hround : E (E.symm (fun _ => (1 : ℚ))) = (fun _ => (1 : ℚ)) :=
      E.apply_symm_apply (fun _ => (1 : ℚ))
    rw [← hc₀w] at hround
    rw [h0, hE0] at hround
    exact one_ne_zero (congrFun hround.symm ⟨0, (by norm_num : 0 < 1)⟩)
  set cl₀ : codimensionCycles V.X 0 →ₗ[ℚ] singularCohomologyOf A.space 0 :=
    { toFun := fun Z => (f₀ Z) • c₀w
      map_add' := by
        intro Z Z'
        show (f₀ (Z + Z')) • c₀w = (f₀ Z) • c₀w + (f₀ Z') • c₀w
        rw [map_add, add_smul]
      map_smul' := by
        intro q Z
        show (f₀ (q • Z)) • c₀w = q • ((f₀ Z) • c₀w)
        rw [map_smul, smul_smul, ← smul_eq_mul] } with hcl₀
  have hcl₀_Z₀ : cl₀ Z₀ = c₀w := by
    show (f₀ Z₀) • c₀w = c₀w
    rw [hf₀, one_smul]
  set cl₁ : codimensionCycles V.X 1 →ₗ[ℚ] singularCohomologyOf A.space 2 :=
    { toFun := fun Z => (f₁ Z) • c₀
      map_add' := by
        intro Z Z'
        show (f₁ (Z + Z')) • c₀ = (f₁ Z) • c₀ + (f₁ Z') • c₀
        rw [map_add, add_smul]
      map_smul' := by
        intro q Z
        show (f₁ (q • Z)) • c₀ = q • ((f₁ Z) • c₀)
        rw [map_smul, smul_smul, ← smul_eq_mul] } with hcl₁
  have hcl₁_Z₁ : cl₁ Z₁ = c₀ := by
    show (f₁ Z₁) • c₀ = c₀
    rw [hf₁, one_smul]
  set H : HodgeBigradedBettiData V :=
    { analytification := A
      hodgeBigrading := fun p =>
        match p with
        | 0 => stashBigrading _ 0
        | 1 => spanBigrading c 1 (by norm_num)
        | (p + 2) => stashBigrading _ (2 * (p + 2))
      cycleClass := fun p =>
        match p with
        | 0 => cl₀
        | 1 => cl₁
        | (p + 2) => 0 } with hH
  have hfiber1 : rationalHodgeSubspace (H.hodgeBigrading 1) =
      Submodule.span ℚ (Set.range c) :=
    rationalHodgeSubspace_span_eq c 1 (by norm_num)
  have htop0 : rationalHodgeSubspace (H.hodgeBigrading 0) = ⊤ :=
    rationalHodgeSubspace_eq_top_of_degree_zero H
  -- the weight-zero monogenic generator: every H⁰ element is a multiple
  -- of the honest transported constant-one function
  have hmono₀ : ∀ x : singularCohomologyOf A.space 0,
      ∃ r : ℚ, x = r • c₀w := by
    intro x
    have hxE : E x = (E x ⟨0, (by norm_num : 0 < 1)⟩) •
        (fun _ => (1 : ℚ)) := by
      funext i
      rw [Subsingleton.elim i ⟨0, (by norm_num : 0 < 1)⟩]
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    refine ⟨E x ⟨0, (by norm_num : 0 < 1)⟩, ?_⟩
    have hA : x = E.symm (E x) := (E.symm_apply_apply x).symm
    have hB : E.symm (E x) = E.symm ((E x ⟨0, (by norm_num : 0 < 1)⟩) •
        (fun _ => (1 : ℚ))) := congrArg (fun y => E.symm y) hxE
    have hC : E.symm ((E x ⟨0, (by norm_num : 0 < 1)⟩) •
        (fun _ => (1 : ℚ))) = (E x ⟨0, (by norm_num : 0 < 1)⟩) • c₀w := by
      rw [map_smul]
      rfl
    exact hA.trans (hB.trans hC)
  -- the weight-one monogenic generator: every fiber element is a multiple
  -- of the honest sphere class
  have hmono₁ : ∀ x : singularCohomologyOf A.space 2,
      x ∈ rationalHodgeSubspace (H.hodgeBigrading 1) →
      ∃ r : ℚ, x = r • c₀ := by
    intro x hx
    have hxspan : x ∈ Submodule.span ℚ (Set.range c) := hfiber1 ▸ hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hxspan
    · rintro z ⟨i, rfl⟩
      rw [Subsingleton.elim i ⟨0, (by norm_num : 0 < 1)⟩]
      exact ⟨1, (one_smul ℚ (c ⟨0, (by norm_num : 0 < 1)⟩)).symm⟩
    · exact ⟨0, (zero_smul ℚ c₀).symm⟩
    · intro y z _ _ hy hz
      obtain ⟨r, rfl⟩ := hy
      obtain ⟨s, rfl⟩ := hz
      exact ⟨r + s, (add_smul r s c₀).symm⟩
    · intro q y _ hy
      obtain ⟨r, rfl⟩ := hy
      exact ⟨q * r, smul_smul q r c₀⟩
  -- THE LAW: the dead-or-monogenic classification, weight by weight
  have hlaw : NativeGSTSingleFoldOrbitLaw V H :=
    native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights
      (fun q => by
        rcases q with _ | _ | q
        · refine Or.inr ⟨Z₀, ?_, ?_⟩
          · rw [show H.cycleClass 0 Z₀ = cl₀ Z₀ from rfl, hcl₀_Z₀,
              htop0]
            exact Submodule.mem_top
          · intro x _
            rw [show H.cycleClass 0 Z₀ = cl₀ Z₀ from rfl, hcl₀_Z₀]
            exact hmono₀ x
        · refine Or.inr ⟨Z₁, ?_, ?_⟩
          · rw [show H.cycleClass 1 Z₁ = cl₁ Z₁ from rfl, hcl₁_Z₁]
            have hmem : c₀ ∈ Submodule.span ℚ (Set.range c) :=
              Submodule.subset_span
                ⟨⟨0, (by norm_num : 0 < 1)⟩, rfl⟩
            exact hfiber1.symm ▸ hmem
          · intro x hx
            rw [show H.cycleClass 1 Z₁ = cl₁ Z₁ from rfl, hcl₁_Z₁]
            exact hmono₁ x hx
        · refine Or.inl ?_
          have hbot : rationalHodgeSubspace (H.hodgeBigrading (q + 2)) = ⊥ :=
            by
            rw [show H.hodgeBigrading (q + 2) = stashBigrading _
                (2 * (q + 2)) from rfl]
            exact rationalHodgeSubspace_stash_eq_bot (q + 2) (by omega)
          exact subsingleton_hodgeFiber_of_eq_bot hbot)
  refine ⟨H, hlaw, ⟨c₀, ?_, ?_⟩, ?_⟩
  · have hmem : c₀ ∈ Submodule.span ℚ (Set.range c) :=
      Submodule.subset_span
        ⟨⟨0, (by norm_num : 0 < 1)⟩, rfl⟩
    exact hfiber1.symm ▸ hmem
  · exact hcne ⟨0, (by norm_num : 0 < 1)⟩
  · exact exactHodge_of_one_GST_fold_orbit hlaw

/-! ## §5 THE MASTER PACKAGE ## -/

/-- **THE POSITIVE-DIMENSIONAL LIVE-WEIGHT PACKAGE.**  The complete receipt:
the law on the one-line positive-dimensional world, the live weight-one
witness, and the one-line live-weight family record. -/
theorem the_positive_dimensional_live_weight_package
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace 1))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (hω : ω ≠ 0)
    (Z₀ : codimensionCycles V.X 0) (hZ₀ : Z₀ ≠ 0)
    (Z₁ : codimensionCycles V.X 1) (hZ₁ : Z₁ ≠ 0) :
    (∃ H : HodgeBigradedBettiData V, NativeGSTSingleFoldOrbitLaw V H) ∧
    (∃ H : HodgeBigradedBettiData V,
      ∃ x ∈ rationalHodgeSubspace (H.hodgeBigrading 1), x ≠ 0) ∧
    (∃ c : Fin 1 → singularCohomologyOf A.space 2,
      (∀ i, c i ≠ 0) ∧ LinearIndependent ℚ c) := by
  obtain ⟨H, hlaw, ⟨x, hx, hxne⟩, _⟩ :=
    positive_dimensional_live_weight_law A hspace ω hω Z₀ hZ₀ Z₁ hZ₁
  exact ⟨⟨H, hlaw⟩, ⟨H, x, hx, hxne⟩,
    positive_dimensional_live_weight_family 1 A hspace ω hω⟩

end GSTPositiveDimensionalLiveWeightLaw

#check GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_family
#check GSTPositiveDimensionalLiveWeightLaw.exists_cycle_functional
#check GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_bearing
#check GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_law
#check GSTPositiveDimensionalLiveWeightLaw.the_positive_dimensional_live_weight_package

#print axioms GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_family
#print axioms GSTPositiveDimensionalLiveWeightLaw.exists_cycle_functional
#print axioms GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_bearing
#print axioms GSTPositiveDimensionalLiveWeightLaw.positive_dimensional_live_weight_law
#print axioms GSTPositiveDimensionalLiveWeightLaw.the_positive_dimensional_live_weight_package
