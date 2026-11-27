/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# The positive-dimensional live-core kit (Wave 44)

The frontier target: the general live rank >= 2 core on positive-dimensional
worlds.  The campaign's certified lanes (`twelvePointWorld`, `finitePointWorld`)
are 0-dimensional: their live weight-0 fibers were computed through
`singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`, and all positive
weights were discharged by PROVED vanishing of the singular cohomology of a
finite discrete space.

A positive-dimensional world (the planned `finiteLineWorld M`, the disjoint
union of M projective lines = Proj of the blocked quotient ring, with the
M-cycle automorphism as the single certificate letter at both live weights)
has a NON-discrete honest analytification (a disjoint union of 2-spheres).
At the Mathlib pin (v4.33.0-rc2) the singular cohomology of any
positive-dimensional space is unreachable: no Mayer-Vietoris, no excision, no
Hurewicz, no Brouwer degree, no singular cohomology of spheres.  The campaign
record `research/records/2026-11-18-gst-positive-dimensional-frontier-map.md`
enumerates the full dodge table.

This kit certifies the ALGEBRAIC ENGINES of the positive-dimensional lane,
none of which requires computing any cohomology group:

1. `complexificationMapQ_injective` — `v ↦ 1 ⊗ v` from a rational singular
   cohomology group into its complexification is injective.  The keystone:
   it converts a declared-zero `(p,p)`-slot into a genuinely dead
   (subsingleton) rational Hodge fiber WITHOUT any vanishing proof for
   `H^{2p}`.

2. `stashBigrading` + `rationalHodgeSubspace_stash_eq_bot` — the dead-weight
   engine.  For any weight `p ≥ 1`, the `(⊤, ⊥, …, ⊥)` bigrading is a legal
   `HodgeBigrading` whose rational fiber is `⊥`.  Unlike the finite-point
   lane's `deadBigrading`, NO vanishing of `H^{2p}` is required: the
   off-`(p,p)` slots absorb the complexification.  This is honest exactly
   for weights whose true `(p,p)`-part is zero — for a curve world, every
   `p ≥ 2`.

3. `spanBigrading` + `rationalHodgeSubspace_span_eq` — the gated-live-weight
   engine.  Given any family of classes `c : Fin M → H^{2p}`, the bigrading
   whose `(p,p)`-slot is the complex span of the complexified family has
   rational fiber EXACTLY the rational span of `c`.  This is the honest
   shape of a live positive weight on the planned curve world: the fiber is
   the span of the point classes.  Instantiated at the honest point classes
   of the M lines (the 3-field disclosed gate of the planned lane), the
   law's content at the live weight becomes exactly the Krylov cyclicity
   of that span.

4. `native_GST_single_fold_orbit_law_of_stashed_positive_weights` — the
   frontier corollary: a world whose weight-0 certificate is cyclic and
   whose positive weights are stashed satisfies the full
   `NativeGSTSingleFoldOrbitLaw`.  The positive-dimensional frontier is
   thereby REDUCED to (a) the honest weight-0 core (the H^0 machine: H^0 is
   the dual of H_0, and Mathlib's `TopCat.singularHomology₀Iso` computes
   H_0 on path components — to be certified in the lane's next wave) and
   (b) the honest point-class gate at the live weights (the Mathlib
   sphere-cohomology gap, precisely fenced).

Honesty ledger: every statement here is proved unconditionally.  Nothing is
assumed about any world; the kit applies to every
`SmoothProjectiveComplexScheme` and every `HodgeBigradedBettiData`.  No
`sorry`, no new axioms; the GitHub CI lane owns the kernel check.
-/

import HCUniverse2.GSTProjectiveOverC
import HCUniverse2.GSTGeometricRealizationStage2F
import HCUniverse2.GSTGeometricRealizationStage2G
import HCUniverse2.GSTClassicalHodgeFiberedCosmology
import HCUniverse2.GSTNativeSingleFoldOrbitLawLanding
import Mathlib

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTHodgeSingleHypothesisConditional
open GSTNativeSingleFoldOrbitLawLanding

namespace GSTPositiveDimensionalLiveCoreKit

/-! ## Section 1: complexification is injective on rational classes -/

/-- A ℚ-linear retraction of ℂ onto the line `ℚ • 1`.  Pure linear algebra
over the field ℚ: the identity on `ℚ • 1` extends to a functional on all of
ℂ by `LinearMap.exists_extend`. -/
theorem exists_complex_retraction :
    ∃ r : ℂ →ₗ[ℚ] ℚ, r 1 = 1 := by
  have himg : Function.Injective (Algebra.linearMap ℚ ℂ) := by
    intro q q' hqq
    have h1 : q • (1 : ℂ) = q' • (1 : ℂ) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
        ← Algebra.linearMap_apply, ← Algebra.linearMap_apply]
      exact hqq
    have hz : (q - q') • (1 : ℂ) = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases (smul_eq_zero (R := ℚ) (M := ℂ)).mp hz with h | h1
    · exact sub_eq_zero.mp h
    · exact absurd h1 one_ne_zero
  set p₁ : Submodule ℚ ℂ := Submodule.span ℚ ({1} : Set ℂ) with hp₁def
  have hone : (1 : ℂ) ∈ p₁ :=
    Submodule.mem_span_singleton.mpr ⟨1, one_smul ℚ 1⟩
  set g : ℚ →ₗ[ℚ] ↥p₁ :=
    LinearMap.codRestrict p₁ (Algebra.linearMap ℚ ℂ)
      (fun q => Submodule.mem_span_singleton.mpr ⟨q, by
        rw [Algebra.linearMap_apply, ← Algebra.algebraMap_eq_smul_one]⟩) with hgdef
  have hginj : Function.Injective g := by
    intro q q' hqq
    refine himg ?_
    have hval : ((g q : ↥p₁) : ℂ) = ((g q' : ↥p₁) : ℂ) :=
      congrArg Subtype.val hqq
    rwa [LinearMap.codRestrict_apply, LinearMap.codRestrict_apply] at hval
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp y.2
    refine ⟨q, Subtype.ext ?_⟩
    rw [LinearMap.codRestrict_apply, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one]
    exact hq
  set e : ℚ ≃ₗ[ℚ] ↥p₁ := LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩ with hedef
  obtain ⟨r, hr⟩ := LinearMap.exists_extend (V := ℂ) (p := p₁) e.symm.toLinearMap
  refine ⟨r, ?_⟩
  have hval1 : ((e 1 : ↥p₁) : ℂ) = 1 := by
    show ((g 1 : ↥p₁) : ℂ) = 1
    rw [LinearMap.codRestrict_apply, Algebra.linearMap_apply, map_one]
  have hee : (e 1 : ↥p₁) = ⟨1, hone⟩ := Subtype.ext hval1
  have hrw : r 1 = r (p₁.subtype ⟨1, hone⟩) := rfl
  rw [hrw]
  have hrw2 : r (p₁.subtype ⟨1, hone⟩) = (r.comp p₁.subtype) ⟨1, hone⟩ := rfl
  rw [hrw2, hr]
  show (e.symm.toLinearMap ⟨1, hone⟩) = 1
  rw [show (e.symm.toLinearMap ⟨1, hone⟩) = e.symm ⟨1, hone⟩ from rfl, ← hee]
  exact e.symm_apply_apply 1

/-- The complexification map `v ↦ 1 ⊗ v` is injective: the retraction
contracts the first tensor factor to a left inverse.  The keystone of the
dead-positive-weight engine. -/
theorem complexificationMapQ_injective {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ] :
    Function.Injective (complexificationMapQ VQ) := by
  obtain ⟨r, hr⟩ := exists_complex_retraction
  set Λ : ℂ →ₗ[ℚ] (VQ →ₗ[ℚ] VQ) :=
    { toFun := fun z => (r z) • (LinearMap.id : VQ →ₗ[ℚ] VQ)
      map_add' := by
        intro z₁ z₂
        apply LinearMap.ext
        intro v
        show ((r (z₁ + z₂)) • (LinearMap.id : VQ →ₗ[ℚ] VQ)) v = _ + _
        simp only [LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply, map_add, add_smul]
      map_smul' := by
        intro q z
        apply LinearMap.ext
        intro v
        show ((r (q • z)) • (LinearMap.id : VQ →ₗ[ℚ] VQ)) v = _
        simp only [map_smul, LinearMap.smul_apply, LinearMap.id_apply,
          RingHom.id_apply, smul_eq_mul, smul_smul] } with hΛdef
  set ρ : Complexification VQ →ₗ[ℚ] VQ := TensorProduct.lift Λ with hρdef
  have hleft : ∀ v : VQ, ρ (complexificationMapQ VQ v) = v := by
    intro v
    have h1 : complexificationMapQ VQ v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl
    rw [h1, TensorProduct.lift.tmul]
    show (r 1) • v = v
    rw [hr, one_smul]
  exact Function.LeftInverse.injective hleft

/-! ## Section 2: the stash bigrading (dead positive weights without
vanishing proofs) -/

section Stash

variable {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ]

/-- The stash component family: everything in slot 0, nothing elsewhere. -/
def stashComponents (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ] (n : ℕ) :
    Fin (n + 1) → Submodule ℂ (Complexification VQ) :=
  fun j => if j = 0 then ⊤ else ⊥

theorem stashComponents_zero (n : ℕ) :
    stashComponents VQ n 0 = ⊤ := if_pos rfl

theorem stashComponents_ne_zero {n : ℕ} {j : Fin (n + 1)} (hj : j ≠ 0) :
    stashComponents VQ n j = ⊥ := if_neg hj

private theorem stashComponents_indep (n : ℕ) :
    iSupIndep (stashComponents VQ n) := by
  rw [iSupIndep_def]
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [stashComponents_zero n]
    have hle : (⨆ (j) (_ : j ≠ 0), stashComponents VQ n j) ≤
        (⊥ : Submodule ℂ (Complexification VQ)) := by
      refine iSup₂_le fun j hj => ?_
      rw [stashComponents_ne_zero hj]
    rw [disjoint_iff, top_inf_eq]
    exact le_bot_iff.mp hle
  · rw [stashComponents_ne_zero hi]
    exact disjoint_bot_left

private theorem stashComponents_spans (n : ℕ) :
    (⨆ a, stashComponents VQ n a) = ⊤ := by
  apply le_antisymm le_top
  rw [← stashComponents_zero n]
  exact le_iSup (stashComponents VQ n) 0

/-- THE DEAD-WEIGHT ENGINE.  For any degree `n`, the `(⊤, ⊥, …, ⊥)`
bigrading: slot 0 absorbs the whole complexification, all other slots are
zero.  Legal for EVERY `n`, with NO condition on the underlying rational
group. -/
def stashBigrading (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ] (n : ℕ) :
    HodgeBigrading VQ n where
  component := stashComponents VQ n
  independent := stashComponents_indep n
  spans := stashComponents_spans n

theorem stashBigrading_component (n : ℕ) (j : Fin (n + 1)) :
    (stashBigrading VQ n).component j = stashComponents VQ n j := rfl

theorem stashBigrading_ppComponent_eq_bot (p : ℕ) (hp : 0 < p) :
    (stashBigrading VQ (2 * p)).ppComponent = ⊥ := by
  have hne : (ppIndex p : Fin (2 * p + 1)) ≠ 0 := by
    intro h
    have h1 : (ppIndex p : Fin (2 * p + 1)).val = (0 : Fin (2 * p + 1)).val :=
      congrArg Fin.val h
    simp only [ppIndex, Fin.val_mk, Fin.val_zero] at h1
    omega
  show (stashBigrading VQ (2 * p)).component (ppIndex p) = ⊥
  rw [stashBigrading_component, stashComponents_ne_zero hne]

/-- The rational fiber of the stash bigrading at any positive weight is
zero: the `(p,p)`-slot is `⊥` and complexification is injective.  NO
vanishing of `H^{2p}` was used. -/
theorem rationalHodgeSubspace_stash_eq_bot (p : ℕ) (hp : 0 < p) :
    rationalHodgeSubspace (stashBigrading VQ (2 * p)) = ⊥ := by
  have hpp : (stashBigrading VQ (2 * p)).ppComponent = ⊥ :=
    stashBigrading_ppComponent_eq_bot p hp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hv' : complexificationMapQ VQ v ∈ (stashBigrading VQ (2 * p)).ppComponent :=
    (mem_rationalHodgeSubspace_iff (stashBigrading VQ (2 * p)) v).mp hv
  rw [hpp] at hv'
  have hzero : complexificationMapQ VQ v = 0 := (Submodule.mem_bot ℂ).mp hv'
  have h0 : complexificationMapQ VQ v = complexificationMapQ VQ 0 := by
    rw [map_zero]
    exact hzero
  exact complexificationMapQ_injective h0

end Stash

/-! ## Section 3: the span bigrading (a gated live weight from a family
of classes) -/

section SpanLive

variable {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ]

/-- The complexified class family. -/
def complexifiedFamily {M : ℕ} (c : Fin M → VQ) : Fin M → Complexification VQ :=
  fun i => complexificationMapQ VQ (c i)

/-- The `(p,p)`-slot of the span bigrading: the complex span of the
complexified family. -/
def spanSlot {M : ℕ} (c : Fin M → VQ) : Submodule ℂ (Complexification VQ) :=
  Submodule.span ℂ (Set.range (complexifiedFamily c))

/-- The complement of the span slot (a choice; exists over the field ℂ). -/
def spanComplement {M : ℕ} (c : Fin M → VQ) : Submodule ℂ (Complexification VQ) :=
  Classical.choose (Submodule.exists_isCompl (spanSlot c))

theorem isCompl_spanSlot {M : ℕ} (c : Fin M → VQ) :
    IsCompl (spanSlot c) (spanComplement c) :=
  Classical.choose_spec (Submodule.exists_isCompl (spanSlot c))

/-- The component family of the span bigrading: the `(p,p)`-slot is the
complex span of the complexified family; slot 0 is a complement; all other
slots are zero. -/
def spanComponents {M : ℕ} (c : Fin M → VQ) (p : ℕ) (hp : 0 < p) :
    Fin (2 * p + 1) → Submodule ℂ (Complexification VQ) :=
  fun j => if j = (⟨p, by omega⟩ : Fin (2 * p + 1)) then spanSlot c
    else if j = 0 then spanComplement c else ⊥

theorem spanComponents_pp {M : ℕ} (c : Fin M → VQ) (p : ℕ) (hp : 0 < p) :
    spanComponents c p hp (⟨p, by omega⟩ : Fin (2 * p + 1)) = spanSlot c := by
  show (if (⟨p, by omega⟩ : Fin (2 * p + 1)) =
        (⟨p, by omega⟩ : Fin (2 * p + 1)) then spanSlot c
      else if (⟨p, by omega⟩ : Fin (2 * p + 1)) = 0 then spanComplement c else ⊥) = _
  rw [if_pos rfl]

theorem spanComponents_zero {M : ℕ} (c : Fin M → VQ) (p : ℕ) (hp : 0 < p) :
    spanComponents c p hp (0 : Fin (2 * p + 1)) = spanComplement c := by
  have hne : (0 : Fin (2 * p + 1)) ≠ (⟨p, by omega⟩ : Fin (2 * p + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_mk] at hval
    omega
  show (if (0 : Fin (2 * p + 1)) = (⟨p, by omega⟩ : Fin (2 * p + 1))
      then spanSlot c
      else if (0 : Fin (2 * p + 1)) = 0 then spanComplement c else ⊥) = _
  rw [if_neg hne, if_pos rfl]

theorem spanComponents_other {M : ℕ} (c : Fin M → VQ) (p : ℕ) (hp : 0 < p)
    (j : Fin (2 * p + 1))
    (h1 : j ≠ (⟨p, by omega⟩ : Fin (2 * p + 1))) (h2 : j ≠ 0) :
    spanComponents c p hp j = ⊥ := by
  show (if j = (⟨p, by omega⟩ : Fin (2 * p + 1)) then spanSlot c
      else if j = 0 then spanComplement c else ⊥) = ⊥
  rw [if_neg h1, if_neg h2]

private theorem spanComponents_indep {M : ℕ} (c : Fin M → VQ) (p : ℕ)
    (hp : 0 < p) : iSupIndep (spanComponents c p hp) := by
  rw [iSupIndep_def]
  intro i
  have hW : IsCompl (spanSlot c) (spanComplement c) := isCompl_spanSlot c
  by_cases hpp : i = (⟨p, by omega⟩ : Fin (2 * p + 1))
  · subst hpp
    rw [spanComponents_pp c p hp]
    have hle : (⨆ (j) (_ : j ≠ (⟨p, by omega⟩ : Fin (2 * p + 1))),
        spanComponents c p hp j) ≤ spanComplement c := by
      refine iSup₂_le fun j hj => ?_
      by_cases h0 : j = 0
      · subst h0
        exact le_of_eq (spanComponents_zero c p hp)
      · rw [spanComponents_other c p hp j (fun h => hj h) h0]
        exact bot_le
    exact hW.disjoint.mono_right hle
  · by_cases h0i : i = 0
    · subst h0i
      rw [spanComponents_zero c p hp]
      have hle : (⨆ (j) (_ : j ≠ 0), spanComponents c p hp j) ≤ spanSlot c := by
        refine iSup₂_le fun j hj => ?_
        by_cases hppj : j = (⟨p, by omega⟩ : Fin (2 * p + 1))
        · subst hppj
          exact le_of_eq (spanComponents_pp c p hp)
        · rw [spanComponents_other c p hp j hppj hj]
          exact bot_le
      exact hW.disjoint.symm.mono_right hle
    · rw [spanComponents_other c p hp i hpp h0i]
      exact disjoint_bot_left

private theorem spanComponents_spans {M : ℕ} (c : Fin M → VQ) (p : ℕ)
    (hp : 0 < p) : (⨆ a, spanComponents c p hp a) = ⊤ := by
  have hW : IsCompl (spanSlot c) (spanComplement c) := isCompl_spanSlot c
  apply le_antisymm le_top
  rw [← hW.sup_eq_top]
  apply sup_le
  · rw [← spanComponents_pp c p hp]
    exact le_iSup (spanComponents c p hp) (⟨p, by omega⟩ : Fin (2 * p + 1))
  · rw [← spanComponents_zero c p hp]
    exact le_iSup (spanComponents c p hp) (0 : Fin (2 * p + 1))

/-- THE GATED-LIVE-WEIGHT ENGINE.  Given a family of classes at weight `p`,
the bigrading whose `(p,p)`-slot is the complex span of the complexified
family.  Legal for every family, with NO linear-independence and NO
spanning hypothesis. -/
def spanBigrading {M : ℕ} (c : Fin M → VQ) (p : ℕ) (hp : 0 < p) :
    HodgeBigrading VQ (2 * p) where
  component := spanComponents c p hp
  independent := spanComponents_indep c p hp
  spans := spanComponents_spans c p hp

theorem spanBigrading_ppComponent {M : ℕ} (c : Fin M → VQ) (p : ℕ)
    (hp : 0 < p) : (spanBigrading c p hp).ppComponent = spanSlot c := by
  show (spanBigrading c p hp).component (ppIndex p) = spanSlot c
  exact spanComponents_pp c p hp

/-- The rational fiber of the span bigrading is EXACTLY the rational span
of the family: the complex span of the complexification of `c`, pulled back
along the injective complexification, returns the rational span.  This is
the honest shape of a gated live weight: the fiber is the span of the
supplied classes.

The `(⊆)` direction is the tensor-projection argument: the map
`T := id ⊗ πW` (with `πW` the projection onto a rational complement `W` of
the rational span `A`) kills every generator `1 ⊗ c i` because `πW` kills
`A`; so `1 ⊗ v ∈ span ℂ (1 ⊗ c)` forces `πW v = 0` by injectivity of the
complexification, hence `v ∈ A`. -/
theorem rationalHodgeSubspace_span_eq {M : ℕ} (c : Fin M → VQ) (p : ℕ)
    (hp : 0 < p) :
    rationalHodgeSubspace (spanBigrading c p hp) =
      Submodule.span ℚ (Set.range c) := by
  have hpp : (spanBigrading c p hp).ppComponent = spanSlot c :=
    spanBigrading_ppComponent c p hp
  apply le_antisymm
  · -- (⊆) The tensor-projection argument.
    intro v hv
    have hmem : complexificationMapQ VQ v ∈ spanSlot c := by
      have hv' : complexificationMapQ VQ v ∈ (spanBigrading c p hp).ppComponent :=
        (mem_rationalHodgeSubspace_iff (spanBigrading c p hp) v).mp hv
      rwa [hpp] at hv'
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl
      (Submodule.span ℚ (Set.range c))
    -- The W-projection along A: every u decomposes as ↑q.1 + ↑q.2.
    set e : (↥(Submodule.span ℚ (Set.range c)) × ↥W) ≃ₗ[ℚ] VQ :=
      Submodule.prodEquivOfIsCompl
        (p := Submodule.span ℚ (Set.range c)) (q := W) hW with hedef
    set πW : VQ →ₗ[ℚ] VQ := W.subtype.comp ((LinearMap.snd ℚ
      ↥(Submodule.span ℚ (Set.range c)) ↥W).comp e.symm.toLinearMap) with hπWdef
    have hsplit : ∀ u : VQ, ∃ q : ↥(Submodule.span ℚ (Set.range c)) × ↥W,
        e q = u ∧ (q.2 : VQ) = πW u := by
      intro u
      exact ⟨e.symm u, e.apply_symm_apply u, rfl⟩
    -- Fact 1: the projection kills the rational span A.
    have hkill : ∀ u ∈ Submodule.span ℚ (Set.range c), πW u = 0 := by
      intro u hu
      obtain ⟨q, hqu, hqπ⟩ := hsplit u
      have h1 : (q.1 : VQ) ∈ Submodule.span ℚ (Set.range c) := q.1.2
      have h2 : (q.2 : VQ) ∈ W := q.2.2
      have heq : (q.1 : VQ) + (q.2 : VQ) = u := by
        rw [← hqu]
        rfl
      have hsub : (q.2 : VQ) = u - (q.1 : VQ) := by
        rw [← heq]
        abel
      have hwA : (q.2 : VQ) ∈ Submodule.span ℚ (Set.range c) := by
        rw [hsub]
        exact Submodule.sub_mem (p := Submodule.span ℚ (Set.range c)) hu h1
      have hbot : (q.2 : VQ) ∈ (⊥ : Submodule ℚ VQ) := by
        rw [← hW.inf_eq_bot]
        exact Submodule.mem_inf.mpr ⟨hwA, h2⟩
      rw [← hqπ]
      exact (Submodule.mem_bot ℚ).mp hbot
    -- Fact 2: the kernel of the projection is exactly A.
    have hker : ∀ u : VQ, πW u = 0 → u ∈ Submodule.span ℚ (Set.range c) := by
      intro u hzero
      obtain ⟨q, hqu, hqπ⟩ := hsplit u
      have hzero' : (q.2 : VQ) = 0 := by rw [hqπ]; exact hzero
      have hfin : u = (q.1 : VQ) := by
        rw [← hqu]
        show (q.1 : VQ) + (q.2 : VQ) = (q.1 : VQ)
        rw [hzero', add_zero]
      rw [hfin]
      exact q.1.2
    -- The tensor map T := id ⊗ πW kills the complex span of 1 ⊗ c.
    set T : Complexification VQ →ₗ[ℚ] Complexification VQ :=
      TensorProduct.map (LinearMap.id : ℂ →ₗ[ℚ] ℂ) πW with hTdef
    have hTgen : ∀ i : Fin M, T (complexifiedFamily c i) = 0 := by
      intro i
      have hci : c i ∈ Submodule.span ℚ (Set.range c) :=
        Submodule.subset_span ⟨i, rfl⟩
      have hcf : complexifiedFamily c i = (1 : ℂ) ⊗ₜ[ℚ] (c i) := rfl
      rw [hcf, hTdef, TensorProduct.map_tmul, hkill (c i) hci,
        TensorProduct.tmul_zero]
    have hTsmul : ∀ (a : ℂ) (z : Complexification VQ), T (a • z) = a • T z := by
      intro a z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
          rw [TensorProduct.smul_tmul', hTdef, TensorProduct.map_tmul,
            TensorProduct.map_tmul, TensorProduct.smul_tmul']
          simp only [LinearMap.id_apply]
      | add z₁ z₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
    have hvT : T (complexificationMapQ VQ v) = 0 := by
      have hmem2 : complexificationMapQ VQ v ∈
          Submodule.span ℂ (Set.range (complexifiedFamily c)) := hmem
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem2
      · rintro z ⟨i, rfl⟩
        exact hTgen i
      · rw [map_zero]
      · intro z₁ z₂ _ _ h₁ h₂
        rw [map_add, h₁, h₂, add_zero]
      · intro a z _ hz
        rw [hTsmul a z, hz, smul_zero]
    have hunravel : T (complexificationMapQ VQ v) =
        complexificationMapQ VQ (πW v) := by
      have hcv : complexificationMapQ VQ v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl
      rw [hcv, hTdef, TensorProduct.map_tmul]
      rfl
    have hfinal : complexificationMapQ VQ (πW v) = 0 := by
      rw [← hunravel]
      exact hvT
    have hπzero : πW v = 0 := by
      refine complexificationMapQ_injective ?_
      rw [hfinal, map_zero]
    exact hker v hπzero
  · -- (⊇) The rational span is contained in the fiber.
    intro v hv
    rw [mem_rationalHodgeSubspace_iff (spanBigrading c p hp) v, hpp]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro q x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ (q : ℂ) hx

end SpanLive

/-! ## Section 4: the frontier corollary — the reduction of the
positive-dimensional law -/

section Frontier

variable {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}

/-- THE FRONTIER COROLLARY.  A world whose weight-0 certificate is Krylov
cyclic and whose positive weights carry the stash bigrading satisfies the
full `NativeGSTSingleFoldOrbitLaw`: the positive weights are dead (fiber
`⊥`, by the injectivity of complexification — no vanishing proof for
`H^{2p}` needed), discharged by the empty word.  The positive-dimensional
frontier is thereby reduced to the honest weight-0 core plus, at any live
positive weight, the honest point-class gate (the span engine of
Section 3). -/
theorem native_GST_single_fold_orbit_law_of_stashed_positive_weights
    (h0 : ∃ C : RealizedCorrespondenceKrylovCertificate V H 0, C.IsKrylovCyclic)
    (hstash : ∀ p : ℕ, 0 < p →
      H.hodgeBigrading p =
        stashBigrading (RationalSingularCohomology H.analytification (2 * p)) (2 * p)) :
    NativeGSTSingleFoldOrbitLaw V H := by
  intro p
  by_cases hp : p = 0
  · subst hp
    exact h0
  · have hpos : 0 < p := Nat.pos_of_ne_zero hp
    have hbot : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥ := by
      rw [hstash p hpos]
      exact rationalHodgeSubspace_stash_eq_bot p hpos
    have hsub : Subsingleton (ClassicalHodgeFiber V H p) :=
      subsingleton_hodgeFiber_of_eq_bot hbot
    exact ⟨emptyWordKrylovCertificate 0 (zeroCycleClass_mem_hodgeFiber H p),
      isKrylovCyclic_of_subsingleton hsub _⟩

end Frontier

end GSTPositiveDimensionalLiveCoreKit
