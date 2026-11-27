/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTFinitePointWorldCarrier
import HCUniverse2.GSTGeometricRealizationStage2F

/-!
# THE GENERAL FINITE-POINT ANALYTIFICATION

The analytification of the general finite-point world: the discrete
N-point space

  `finitePointSpace N := TopCat.discrete.obj (Fin N)`

with the genuine point classification

  `ComplexPoint (finitePointWorld N) ≃ Fin N`

— the N sections of the structure map of `Spec (Fin N → ℂ)` over `Spec ℂ`
are exactly the evaluation maps `Pi.evalRingHom _ i`, classified through
the idempotent analysis of the section ring homomorphism (each section's
ring homomorphism sends exactly one of the N basis idempotents to `1`).
This assembles a concrete `AnalytificationData` of the corpus's Stage-2F
stack for every nonzero N; the arity-12 source lane is the instance
`N = 12`.

Contract delivered downstream (`GSTFinitePointCohomology` and beyond):
`finitePointAnalytification N : AnalytificationData (finitePointWorld N)`
whose `space` field is definitionally the constant `finitePointSpace N`,
together with the `TotallyDisconnectedSpace ↥(finitePointSpace N)`
instance consumed by Mathlib's pinned singular-chain isomorphism.

Binder discipline of the general-N lane (this is file 2; the world carrier
is file 1, `GSTFinitePointWorldCarrier`, exporting `finitePointWorld N
[NeZero N]`): every declaration that mentions `N` takes `(N : ℕ)
[NeZero N]` as its leading binders.  The empty world `N = 0` is rejected
by the lane law (`Fin 0 → ℂ` is the zero ring, and the section
classification lives on the nonempty idempotent sum).

No `sorry`, no new axioms, no `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTFinitePointWorldCarrier

namespace GSTFinitePointAnalytification

variable (N : ℕ) [NeZero N]
-- Lane binder discipline: every declaration below that mentions `N`
-- re-binds `(N : ℕ) [NeZero N]` explicitly at its head (the section
-- variable above is kept per the lane law and shadowed by the explicit
-- binders, so the shipped signatures are fully deterministic).

/-! ## §1 THE DISCRETE N-POINT SPACE -/

/-- The analytification space of the finite-point world: the discrete
topology on the N points (`TopCat.discrete.obj`, the pinned Mathlib
discrete-topology functor). -/
def finitePointSpace (N : ℕ) [NeZero N] : TopCat :=
  TopCat.discrete.obj (Fin N)

/-- The underlying type of the discrete space is definitionally `Fin N`
(`TopCat.coe_of` is `rfl` at the pin). -/
theorem finitePointSpace_coe (N : ℕ) [NeZero N] :
    ↥(finitePointSpace N) = Fin N := rfl

/-- The discrete N-point space is totally disconnected.  The chain is
`TopCat.str` (the space's carrier topology is literally `⊥`) →
`DiscreteTopology` → `TotallySeparatedSpace.of_discrete`
(Topology/Connected/TotallyDisconnected.lean:223) →
`TotallySeparatedSpace.totallyDisconnectedSpace` (:218).  The
`DiscreteTopology` link does not fire from bare instance search: Mathlib's
global `DiscreteTopology (TopCat.discrete.obj X)` (TopCat/Basic.lean:187)
cannot see through the non-reducible `def finitePointSpace`, so it is
provisioned explicitly with the same `⟨rfl⟩` Mathlib uses there (CI
43793762987, error at 66:2); the two pinned instances then close the chain. -/
instance finitePointSpace_totallyDisconnected (N : ℕ) [NeZero N] :
    TotallyDisconnectedSpace ↥(finitePointSpace N) := by
  haveI : DiscreteTopology ↥(finitePointSpace N) := ⟨rfl⟩
  infer_instance

/-! ## §2 THE N SECTIONS -/

/-- The evaluation ring homomorphism at the `i`-th component of the
N-fold product algebra `Fin N → ℂ`. -/
def finitePointEvalRingHom (N : ℕ) [NeZero N] (i : Fin N) :
    (Fin N → ℂ) →+* ℂ :=
  Pi.evalRingHom (fun _ : Fin N => ℂ) i

/-- Evaluation at `i` after the structure algebra map is the identity on
`ℂ`: the scalar embedding lands in the constant functions, and evaluating
a constant function at any component returns the scalar. -/
theorem eval_comp_algebraMap (N : ℕ) [NeZero N] (i : Fin N) :
    RingHom.comp (finitePointEvalRingHom N i) (algebraMap ℂ (Fin N → ℂ)) =
      RingHom.id ℂ := by
  ext r
  show finitePointEvalRingHom N i ((algebraMap ℂ (Fin N → ℂ)) r) = r
  -- AUDIT-1: the evaluation homomorphism is `Function.eval` (reducible at
  -- the pin), the Pi algebra map at a component is the component algebra
  -- map (`Pi.algebraMap_apply`, proved by `rfl` at the pin), and the self
  -- algebra map of `ℂ` is the identity (`Algebra.algebraMap_self`, proved
  -- by `rfl` at the pin): the goal is definitional.
  rfl

-- PORT RISK(W42B-CARRIER-X): this declaration's TYPECHECK requires the lane
-- carrier's definitional structure: Agent A's `finitePointWorld N` must have
-- its `X` field reduce (default transparency) to `Spec (CommRingCat.of
-- (Fin N → ℂ))` — i.e. the carrier must be assembled as
-- `⟨finitePointScheme N, finitePointStructureMap N, …⟩` with
-- `finitePointScheme N` the reducible alias of `Spec (CommRingCat.of
-- (Fin N → ℂ))`.  The arity-12 source exercised the identical defeq on its
-- own carrier, so the faithful carrier port discharges it; any deviation in
-- the carrier file is the designated CI repair point (restate this codomain
-- through `finitePointScheme N` there).  The same carrier-`X` defeq is
-- consumed below by `pointSection`, `sectionRingHom` (the `Spec.homEquiv`
-- unification) and `complexPoint_eq` (the `Spec.map_preimage` step).
/-- The `i`-th section as a scheme morphism `Spec ℂ ⟶ Spec (Fin N → ℂ)`. -/
def pointSectionHom (N : ℕ) [NeZero N] (i : Fin N) :
    complexBase ⟶ (finitePointWorld N).X :=
  Spec.map (CommRingCat.ofHom (finitePointEvalRingHom N i))

-- PORT RISK(W42B-CARRIER-SM): the opening `rfl` step of the calc below
-- requires `(finitePointWorld N).structureMap` to reduce (default
-- transparency) to `Spec.map (CommRingCat.ofHom (algebraMap ℂ
-- (Fin N → ℂ)))` — i.e. the carrier's structure-map field must be the
-- plain `def` port `finitePointStructureMap N := Spec.map
-- (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ)))`, delta-unfoldable exactly
-- as in the arity-12 source.  The same requirement reappears as the `hs`
-- rfl in `section_h_algebraMap`.  Designated CI repair point: align with
-- the carrier file's structure-map definition.
/-- The section property: composing with the structure map of the
finite-point world returns the identity on the complex base.  The
calculation is the contravariance of `Spec.map` (`Spec.map_comp`) applied
to `eval_comp_algebraMap`, concluded by `Spec.map_id`. -/
theorem pointSection_section (N : ℕ) [NeZero N] (i : Fin N) :
    pointSectionHom N i ≫ (finitePointWorld N).structureMap =
      𝟙 complexBase := by
  have hring : (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) ≫
      (CommRingCat.ofHom (finitePointEvalRingHom N i)) =
      CommRingCat.ofHom (RingHom.id ℂ) := by
    -- AUDIT-2: bundled-hom composition; `ConcreteCategory.hom_comp`
    -- unfolds `(ofHom a ≫ ofHom b).hom = RingHom.comp b a`, and
    -- `CommRingCat.hom_ext` reduces to the underlying `RingHom`
    -- identity `eval_comp_algebraMap`.
    apply CommRingCat.hom_ext
    exact eval_comp_algebraMap N i
  calc pointSectionHom N i ≫ (finitePointWorld N).structureMap
      = Spec.map (CommRingCat.ofHom (finitePointEvalRingHom N i)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) := rfl
    _ = Spec.map
          ((CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) ≫
            (CommRingCat.ofHom (finitePointEvalRingHom N i))) :=
          (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) := by rw [hring]
    _ = 𝟙 complexBase := Spec.map_id _

/-- The `i`-th section is a genuine complex point of the world. -/
def pointSection (N : ℕ) [NeZero N] (i : Fin N) :
    ComplexPoint (finitePointWorld N) :=
  ⟨pointSectionHom N i, pointSection_section N i⟩

/-! ## §3 THE CLASSIFICATION OF ALL SECTIONS -/

/-- The basis idempotent decomposition of every vector in the N-fold
product algebra: each function is the sum of its scalar-weighted basis
idempotents, expressed through the algebra map (the constant-function
embedding) to avoid any smul-instance ambiguity. -/
theorem pi_decomp (N : ℕ) [NeZero N] (x : Fin N → ℂ) :
    (∑ k : Fin N,
        algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin N → ℂ) =
      x := by
  funext i
  have hsum : (∑ k : Fin N,
      (algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) :
        Fin N → ℂ)) i =
      ∑ k : Fin N,
        (algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin N → ℂ) i :=
    Finset.sum_apply _ _ _
  rw [hsum]
  have hval : ∀ k : Fin N,
      ((algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) :
        Fin N → ℂ)) i =
        (if i = k then x k else 0) := by
    intro k
    rw [Pi.mul_apply, Pi.single_apply]
    -- AUDIT-3: the Pi algebra map at a component is the component algebra
    -- map (`Pi.algebraMap_apply`, `rfl` at the pin), and the self algebra
    -- map of `ℂ` is the identity (`Algebra.algebraMap_self`, `rfl`).
    have hconst : (algebraMap ℂ (Fin N → ℂ) (x k)) i = x k := rfl
    by_cases hik : i = k
    · rw [hconst, if_pos hik, mul_one, if_pos hik]
    · rw [hconst, if_neg hik, mul_zero, if_neg hik]
  simp only [hval]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm)]
  · intro hli
    exact absurd (Finset.mem_univ i) hli

/-- The ring homomorphism underlying a section, recovered through the
`Spec` preimage — the `Spec.homEquiv` of the pinned Mathlib adjunction. -/
def sectionRingHom (N : ℕ) [NeZero N] (f : ComplexPoint (finitePointWorld N)) :
    (Fin N → ℂ) →+* ℂ :=
  (Spec.homEquiv (R := CommRingCat.of (Fin N → ℂ)) (S := CommRingCat.of ℂ)
    f.1).hom

-- PORT RISK(W42B-CARRIER-SM): the `hs` step below is the second
-- `rfl`-on-structure-map site of this file (see `pointSection_section` for
-- the full analysis of the carrier requirement).
/-- The hom-level identity behind every section: composing the structure
algebra map with the section's preimage ring homomorphism returns the
identity.  This is the transport of the section condition through
`Spec.preimage_comp`, `Spec.preimage_map` and `Spec.preimage_id`. -/
theorem section_h_algebraMap (N : ℕ) [NeZero N]
    (f : ComplexPoint (finitePointWorld N)) :
    (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) ≫
      (Spec.preimage (R := CommRingCat.of (Fin N → ℂ)) (S := CommRingCat.of ℂ)
        f.1) =
      𝟙 (CommRingCat.of ℂ) := by
  have h0 : f.1 ≫ (finitePointWorld N).structureMap = 𝟙 complexBase := f.2
  have hs : (finitePointWorld N).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) := rfl
  calc (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) ≫
      (Spec.preimage (R := CommRingCat.of (Fin N → ℂ)) (S := CommRingCat.of ℂ)
        f.1)
      = Spec.preimage ((finitePointWorld N).structureMap) ≫
          Spec.preimage (R := CommRingCat.of (Fin N → ℂ))
            (S := CommRingCat.of ℂ) f.1 := by
        simp only [hs, Spec.preimage_map]
        all_goals rfl
    _ = Spec.preimage (f.1 ≫ (finitePointWorld N).structureMap) :=
          (Spec.preimage_comp _ _).symm
    _ = Spec.preimage (𝟙 complexBase) := by rw [h0]
    _ = 𝟙 (CommRingCat.of ℂ) := Spec.preimage_id

/-- Every section ring homomorphism composes with the structure algebra map
to the identity. -/
theorem sectionRingHom_comp_algebraMap (N : ℕ) [NeZero N]
    (f : ComplexPoint (finitePointWorld N)) :
    RingHom.comp (sectionRingHom N f) (algebraMap ℂ (Fin N → ℂ)) =
      RingHom.id ℂ := by
  have h := section_h_algebraMap N f
  have h2 : RingHom.comp (sectionRingHom N f) (algebraMap ℂ (Fin N → ℂ)) =
      ((CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ))) ≫
        (Spec.preimage (R := CommRingCat.of (Fin N → ℂ)) (S := CommRingCat.of ℂ)
          f.1)).hom := by
    -- AUDIT-4: bundled-hom composite unfolds to the `RingHom` composite
    -- (`ConcreteCategory.hom_comp`, `ConcreteCategory.ofHom_hom`).
    rfl
  rw [h2, h]
  -- AUDIT-5: the identity morphism's underlying `RingHom`
  -- (`CommRingCat.hom_id`, proved by `rfl` at the pin).
  exact CommRingCat.hom_id

/-- The scalar bookkeeping: a section ring homomorphism maps the algebra-map
image of a scalar to the scalar itself. -/
theorem sectionRingHom_algebraMap_apply (N : ℕ) [NeZero N]
    (f : ComplexPoint (finitePointWorld N)) (r : ℂ) :
    sectionRingHom N f ((algebraMap ℂ (Fin N → ℂ)) r) = r :=
  congrArg (fun h => h r) (sectionRingHom_comp_algebraMap N f)

/-- The basis idempotents multiply trivially: equal indices persist,
distinct indices annihilate. -/
theorem single_mul_single_self (N : ℕ) [NeZero N] (k : Fin N) :
    (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ) : Fin N → ℂ) =
      Pi.single k (1 : ℂ) := by
  funext i
  rw [Pi.mul_apply, Pi.single_apply]
  by_cases hik : i = k
  · rw [if_pos hik, one_mul]
  · rw [if_neg hik, mul_zero]
  -- AUDIT: with the summand type pinned, the three `Pi.single`-applications
  -- become the SAME term, so ONE `Pi.single_apply` rewrites all three and a
  -- single `if_pos`/`if_neg` closes each branch (the two-rewrite form of the
  -- original over-fires — the run-11 masked defect M1).

theorem single_mul_single_ne (N : ℕ) [NeZero N] {k j : Fin N} (hkj : k ≠ j) :
    (Pi.single k (1 : ℂ) * Pi.single j (1 : ℂ) : Fin N → ℂ) = 0 := by
  funext i
  rw [Pi.mul_apply, Pi.single_apply, Pi.single_apply]
  by_cases hik : i = k
  · rw [if_pos hik, if_neg (fun h => hkj (hik.symm.trans h)), mul_zero,
      Pi.zero_apply]
  · rw [if_neg hik, zero_mul, Pi.zero_apply]

/-- The sum of the N basis idempotents is the multiplicative unit. -/
theorem sum_single_eq_one (N : ℕ) [NeZero N] :
    ∑ k : Fin N, Pi.single k (1 : ℂ) = 1 := by
  have h' : (∑ k : Fin N, Pi.single k (1 : ℂ) : Fin N → ℂ) =
      (fun _ : Fin N => (1 : ℂ)) := by
    simpa only [map_one, one_mul] using pi_decomp N (fun _ => (1 : ℂ))
  exact h'
  -- AUDIT: the instantiated decomposition has summands
  -- `algebraMap ℂ (Fin N → ℂ) ((fun _ => (1 : ℂ)) k) * Pi.single k (1 : ℂ)`;
  -- `map_one` and `one_mul` reduce them to `Pi.single k (1 : ℂ)`, and the
  -- function `fun _ => (1 : ℂ)` is definitionally the Pi-one (the `exact`
  -- closes across the `Pi.one` seam at default transparency — CI 43793762987
  -- error at 241:2 was the `simpa`-normalized `fun x => 1` vs `1` mismatch).

/-- A section ring homomorphism sends exactly one basis idempotent to `1`. -/
theorem sectionRingHom_single_one (N : ℕ) [NeZero N]
    (f : ComplexPoint (finitePointWorld N)) :
    ∃! k : Fin N, sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 := by
  have hvals : ∀ k : Fin N,
      sectionRingHom N f (Pi.single k (1 : ℂ)) = 0 ∨
      sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 := by
    intro k
    apply eq_zero_or_one_of_sq_eq_self
    have hmul : sectionRingHom N f (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ))
        = sectionRingHom N f (Pi.single k (1 : ℂ)) :=
      congrArg (sectionRingHom N f) (single_mul_single_self N k)
    rw [map_mul] at hmul
    rw [pow_two, hmul]
  -- the sum of the N values is one
  have hsum : ∑ k : Fin N, sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 := by
    have h : sectionRingHom N f (∑ k : Fin N, Pi.single k (1 : ℂ)) = 1 := by
      rw [sum_single_eq_one N, map_one]
    rw [map_sum] at h
    exact h
  -- at most one value is one: two distinct ones would multiply to 0 = 1
  have hatmost : ∀ k j : Fin N, k ≠ j →
      sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 →
      sectionRingHom N f (Pi.single j (1 : ℂ)) ≠ 1 := by
    intro k j hkj hk1 hcontra
    have hprod : sectionRingHom N f (Pi.single k (1 : ℂ) * Pi.single j (1 : ℂ)) = 0 := by
      rw [single_mul_single_ne N hkj, map_zero]
    rw [map_mul, hk1, hcontra, one_mul] at hprod
    exact absurd hprod.symm zero_ne_one
  -- at least one value is one (else the sum would be zero)
  obtain ⟨k₀, hk₀⟩ : ∃ k : Fin N, sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ k : Fin N, sectionRingHom N f (Pi.single k (1 : ℂ)) = 0 := by
      intro k
      rcases hvals k with h | h
      · exact h
      · exact absurd h (hnone k)
    rw [Finset.sum_eq_zero (fun k _ => hzero k)] at hsum
    exact zero_ne_one hsum
  refine ⟨k₀, hk₀, fun j hj => ?_⟩
  by_contra hkj
  exact hatmost k₀ j (Ne.symm hkj) hk₀ hj

/-- **THE CLASSIFICATION.**  Every complex point (section) of the
finite-point world is exactly one of the N evaluation sections. -/
theorem complexPoint_eq (N : ℕ) [NeZero N]
    (f : ComplexPoint (finitePointWorld N)) :
    ∃ i : Fin N, f.1 = pointSectionHom N i := by
  obtain ⟨k₀, hk₀, huniq⟩ := sectionRingHom_single_one N f
  -- the section ring homomorphism is the evaluation at k₀
  have heq : sectionRingHom N f = finitePointEvalRingHom N k₀ := by
    -- AUDIT-8: `ext` picks `RingHom.pi_ext` from the registry, which
    -- decomposes at `Pi.single x x✝` (two levels, CI 43800560334 errors at
    -- 313:35/317:37/330:42 — `x : Fin N` applied at `k`); the proof is
    -- written for the full-function variable, so the extensionality is
    -- pinned to the one-level generic `DFunLike.ext` (Mathlib's own idiom at
    -- the pin, Data/FunLike/Ring.lean:32).
    apply DFunLike.ext
    intro x
    have hdx : x = (∑ k : Fin N,
        algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin N → ℂ) :=
      (pi_decomp N x).symm
    have hsrw : sectionRingHom N f x =
        sectionRingHom N f (∑ k : Fin N,
          (algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ) :
            Fin N → ℂ)) :=
      congrArg (fun s => sectionRingHom N f s) hdx
    -- AUDIT-9: the 0-or-1 dichotomy of the basis idempotents' values, the
    -- same `eq_zero_or_one_of_sq_eq_self` spine that carries
    -- `sectionRingHom_single_one` (CI 43800560334 error at 326:27 — the
    -- by_contra had only `¬ = 0`, which does not produce the `= 1` that
    -- `huniq` consumes).
    have hval01 : ∀ k : Fin N,
        sectionRingHom N f (Pi.single k (1 : ℂ)) = 0 ∨
        sectionRingHom N f (Pi.single k (1 : ℂ)) = 1 := by
      intro k
      apply eq_zero_or_one_of_sq_eq_self
      have hmul : sectionRingHom N f (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ))
          = sectionRingHom N f (Pi.single k (1 : ℂ)) :=
        congrArg (sectionRingHom N f) (single_mul_single_self N k)
      rw [map_mul] at hmul
      rw [pow_two, hmul]
    have hvals : ∀ k : Fin N,
        sectionRingHom N f (Pi.single k (1 : ℂ)) = (if k = k₀ then 1 else 0) := by
      intro k
      by_cases hkk : k = k₀
      · rw [hkk, if_pos rfl, hk₀]
      · rw [if_neg hkk]
        rcases hval01 k with h0 | h1
        · exact h0
        · exact absurd (huniq k h1) hkk
    calc sectionRingHom N f x
        = ∑ k : Fin N,
            sectionRingHom N f
              (algebraMap ℂ (Fin N → ℂ) (x k) * Pi.single k (1 : ℂ)) := by
          rw [hsrw, map_sum]
      _ = ∑ k : Fin N,
            x k * sectionRingHom N f (Pi.single k (1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_mul, sectionRingHom_algebraMap_apply]
      _ = x k₀ := by
          have hterm : ∀ k : Fin N,
              x k * sectionRingHom N f (Pi.single k (1 : ℂ)) =
              (if k = k₀ then x k else 0) := by
            intro k
            rw [hvals k]
            by_cases hkk : k = k₀
            · rw [if_pos hkk, mul_one, if_pos hkk]
            · rw [if_neg hkk, mul_zero, if_neg hkk]
          simp only [hterm]
          rw [Finset.sum_eq_single k₀]
          · rw [if_pos rfl]
          · intro b _ hb
            rw [if_neg hb]
          · intro hli
            exact absurd (Finset.mem_univ k₀) hli
  -- transport back to the scheme level
  have hhom : (Spec.preimage (R := CommRingCat.of (Fin N → ℂ))
      (S := CommRingCat.of ℂ) f.1) =
      CommRingCat.ofHom (finitePointEvalRingHom N k₀) := by
    -- AUDIT-6: bundled-hom equality through the underlying `RingHom`.
    apply CommRingCat.hom_ext
    exact heq
  have hmap : f.1 = Spec.map (Spec.preimage
      (R := CommRingCat.of (Fin N → ℂ)) (S := CommRingCat.of ℂ) f.1) :=
    (Spec.map_preimage _).symm
  rw [hmap, hhom]
  exact ⟨k₀, rfl⟩

/-- The N sections are pairwise distinct. -/
theorem pointSection_injective (N : ℕ) [NeZero N] :
    Function.Injective (fun i => pointSection N i) := by
  intro i j hij
  have h : pointSectionHom N i = pointSectionHom N j := congrArg (·.1) hij
  -- AUDIT-7: the `ofHom` wrapper's underlying `RingHom`, recovered through
  -- `Spec.map_inj` (the pinned iff-form; `Spec.map_injective` is a plain
  -- `Function.Injective` fact, not a rewrite rule).
  have h2 : finitePointEvalRingHom N i = finitePointEvalRingHom N j :=
    congrArg (fun g => g.hom) (Spec.map_inj.mp h)
  have hv : finitePointEvalRingHom N i (Pi.single i (1 : ℂ)) =
      finitePointEvalRingHom N j (Pi.single i (1 : ℂ)) := by rw [h2]
  have hli : finitePointEvalRingHom N i (Pi.single i (1 : ℂ)) = 1 := by
    -- AUDIT-10 (wave 14): the defeq `finitePointEvalRingHom N i g ≡ g i`
    -- exposed by a `show` whose `Pi.single` dependent family is pinned by an
    -- explicit type ascription — the corpus's own battle-tested idiom (the
    -- ascription sites of the arity-12 source all elaborated clean in run
    -- 43832523181).  The bare `show (Pi.single i (1 : ℂ)) i = 1` leaves the
    -- family a bare metavariable `?m.76` with no expected type, and `1 : ℂ`
    -- collides with `?m.76 i` (CI 43832523181, error at 410:22); the pinned
    -- `Pi.single_eq_same` (Algebra/Notation/Pi/Basic.lean:32 at the pin,
    -- args `(i : ι) (x : M i)` both explicit) then unifies against the clean
    -- application.
    show ((Pi.single i (1 : ℂ) : Fin N → ℂ)) i = 1
    -- WAVE 16 (run-15 error at 416:30): the lemma call's own family binder is
    -- a bare metavariable `?m.88 i` against `1 : ℂ` — pinned by the named
    -- implicit `M`, Mathlib's own idiom at the pin (Finsupp/Single.lean,
    -- `single_eq_same`'s proof: `exact Pi.single_eq_same (M := fun _ ↦ M) a b`).
    exact Pi.single_eq_same (M := fun _ : Fin N => ℂ) i (1 : ℂ)
  have hrj : finitePointEvalRingHom N j (Pi.single i (1 : ℂ)) =
      (if j = i then (1 : ℂ) else 0) :=
    Pi.single_apply i (1 : ℂ) j
  -- AUDIT: the `show`-normalizations of the original put `Pi.single` in
  -- application-head position with no expected type (the implicit-β seam,
  -- CI 43793762987 errors at 361/365); the defeq
  -- `finitePointEvalRingHom N i g ≡ g i` is kernel-proven by the clean
  -- receipt `eval_comp_algebraMap`, so the pinned lemmas close directly.
  rw [hli, hrj] at hv
  by_cases hij' : i = j
  · exact hij'
  · have hne : ¬(j = i) := fun hcon => hij' hcon.symm
    rw [if_neg hne] at hv
    exact absurd hv.symm zero_ne_one

/-- **THE POINT EQUIVALENCE.**  The complex points of the finite-point
world are exactly the N evaluation sections. -/
noncomputable def finitePointSectionEquiv (N : ℕ) [NeZero N] :
    Fin N ≃ ComplexPoint (finitePointWorld N) :=
  Equiv.ofBijective (fun i => pointSection N i)
    ⟨pointSection_injective N,
     fun f => by
       obtain ⟨i, hi⟩ := complexPoint_eq N f
       exact ⟨i, Subtype.ext hi.symm⟩⟩

/-- **THE FINITE-POINT ANALYTIFICATION.**  The discrete N-point space
with the genuine point classification. -/
noncomputable def finitePointAnalytification (N : ℕ) [NeZero N] :
    AnalytificationData (finitePointWorld N) where
  space := finitePointSpace N
  pointsEquiv :=
    (finitePointSectionEquiv N).symm.trans
      (Equiv.cast (finitePointSpace_coe N).symm)

/-! ## Receipts -/

#check finitePointSpace
#check finitePointSpace_coe
#check finitePointSpace_totallyDisconnected
#check finitePointEvalRingHom
#check eval_comp_algebraMap
#check pointSectionHom
#check pointSection_section
#check pointSection
#check pi_decomp
#check sectionRingHom
#check section_h_algebraMap
#check sectionRingHom_comp_algebraMap
#check sectionRingHom_algebraMap_apply
#check single_mul_single_self
#check single_mul_single_ne
#check sum_single_eq_one
#check sectionRingHom_single_one
#check complexPoint_eq
#check pointSection_injective
#check finitePointSectionEquiv
#check finitePointAnalytification

#print axioms eval_comp_algebraMap
#print axioms pointSection_section
#print axioms pi_decomp
#print axioms section_h_algebraMap
#print axioms sectionRingHom_comp_algebraMap
#print axioms sectionRingHom_algebraMap_apply
#print axioms single_mul_single_self
#print axioms single_mul_single_ne
#print axioms sum_single_eq_one
#print axioms sectionRingHom_single_one
#print axioms complexPoint_eq
#print axioms pointSection_injective
#print axioms finitePointSectionEquiv
#print axioms finitePointAnalytification

end GSTFinitePointAnalytification

/-! DRAFT STATUS (W42-B, file 2 of the general-N finite-point lane):
* Source: the arity-12 analytification module of the native-point world
  lane (496 lines), ported under the wave-42 lane law.
* Declarations ported: 21 / 21 (7 defs, 1 instance, 13 theorems), in
  source order.  Rename map `twelvePoint ↦ finitePoint` applied to 6 names
  (`finitePointSpace`, `finitePointSpace_coe`,
  `finitePointSpace_totallyDisconnected`, `finitePointEvalRingHom`,
  `finitePointSectionEquiv`, `finitePointAnalytification`); the other 15
  names keep their source names inside the renamed namespace.
* Binder discipline: every N-mentioning declaration (all 21) takes
  `(N : ℕ) [NeZero N]` as leading binders; the `variable (N : ℕ)
  [NeZero N]` line at namespace top is kept per the lane law and shadowed
  by the explicit binders, so the exported signatures are deterministic.
* PORT NOTE(n12): 0 — the wave-41 recon claim is VERIFIED: every proof
  body of the source is arity-agnostic (no `by decide`, no `norm_num` on
  12, no 12-literals in any proof term; the source's only 12-content was
  the fixed index type and prose).  All bodies are verbatim modulo the
  type map `Fin 12 ↦ Fin N` and explicit N-threading at application
  sites (plus the mandatory parentheses at `(finitePointWorld N).X`,
  `(finitePointDualCochains-style projections, and `↥(finitePointSpace N)`).
* PORT NOTE(rename-map): 0 exemptions needed in this file.
* PORT RISK(W42B-CARRIER-X) at `pointSectionHom`: the declared codomain's
  typecheck requires the carrier's `X` field to reduce to
  `Spec (CommRingCat.of (Fin N → ℂ))` (Agent A's
  `⟨finitePointScheme N, …⟩` assembly with the reducible alias); the same
  defeq is consumed by `pointSection`, `sectionRingHom` (`Spec.homEquiv`
  unification) and `complexPoint_eq` (`Spec.map_preimage`).
* PORT RISK(W42B-CARRIER-SM) at `pointSection_section` (pointer at
  `section_h_algebraMap`): the `rfl` steps require the carrier's
  `structureMap` field to reduce to `Spec.map (CommRingCat.ofHom
  (algebraMap ℂ (Fin N → ℂ)))` — the faithful plain-`def` port of the
  carrier's structure map.
* Static verification: no `twelvePoint`/`TwelvePoint`/`GSTTwelvePoint`/
  `Fin 12` survives anywhere (grep-checked, comments included); external
  identifiers are exactly the source's CI-green set plus the lane-carrier
  contract names (`finitePointWorld`); parenthesis balance depth 0
  (docstring-excluded).  NOT COMPILED (no local Lean by repo law) — the
  two PORT RISK sites above are the designated CI repair points.
-/
end -- noncomputable section
