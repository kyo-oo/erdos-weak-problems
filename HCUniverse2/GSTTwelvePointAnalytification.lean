/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTTwelvePointWorldCarrier
import HCUniverse2.GSTGeometricRealizationStage2F

/-!
# GST TWELVE-POINT ANALYTIFICATION

The analytification of the first genuine geometric world: the discrete
twelve-point space

  `twelvePointSpace := TopCat.discrete.obj (Fin 12)`

with the genuine point classification

  `ComplexPoint twelvePointWorld ≃ Fin 12`

— the twelve sections of the structure map of `Spec (ℂ¹²)` over `Spec ℂ` are
exactly the evaluation maps `Pi.evalRingHom _ i`, classified through the
idempotent analysis of the section ring homomorphism (each section's ring
homomorphism sends exactly one of the twelve basis idempotents to `1`).
This assembles the first concrete `AnalytificationData` of the corpus's
Stage-2F stack.

Contract delivered downstream (`GSTTwelvePointCohomology` and beyond):
`twelvePointAnalytification : AnalytificationData twelvePointWorld` whose
`space` field is definitionally the constant `twelvePointSpace`, together
with the `TotallyDisconnectedSpace ↥twelvePointSpace` instance consumed by
Mathlib's pinned singular-chain isomorphism.

No `sorry`, no new axioms, no `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTTwelvePointWorldCarrier

namespace GSTTwelvePointAnalytification

/-! ## §1 THE DISCRETE TWELVE-POINT SPACE -/

/-- The analytification space of the twelve-point world: the discrete
topology on the twelve points (`TopCat.discrete.obj`, the pinned Mathlib
discrete-topology functor). -/
def twelvePointSpace : TopCat := TopCat.discrete.obj (Fin 12)

/-- The underlying type of the discrete space is definitionally `Fin 12`
(`TopCat.coe_of` is `rfl` at the pin). -/
theorem twelvePointSpace_coe : ↥twelvePointSpace = Fin 12 := rfl

/-- The discrete twelve-point space is totally disconnected.  The chain is
`TopCat.str` (the space's carrier topology is literally `⊥`) →
`DiscreteTopology` → `TotallySeparatedSpace.of_discrete`
(Topology/Connected/TotallyDisconnected.lean:223) →
`TotallySeparatedSpace.totallyDisconnectedSpace` (:218).  The
`DiscreteTopology` link does not fire from bare instance search: Mathlib's
global `DiscreteTopology (TopCat.discrete.obj X)` (TopCat/Basic.lean:187)
cannot see through the non-reducible `def twelvePointSpace`, so it is
provisioned explicitly with the same `⟨rfl⟩` Mathlib uses there (CI
43793762987, error at 66:2); the two pinned instances then close the chain. -/
instance twelvePointSpace_totallyDisconnected :
    TotallyDisconnectedSpace ↥twelvePointSpace := by
  haveI : DiscreteTopology ↥twelvePointSpace := ⟨rfl⟩
  infer_instance

/-! ## §2 THE TWELVE SECTIONS -/

/-- The evaluation ring homomorphism at the `i`-th component of `ℂ¹²`. -/
def twelvePointEvalRingHom (i : Fin 12) :
    (Fin 12 → ℂ) →+* ℂ :=
  Pi.evalRingHom (fun _ : Fin 12 => ℂ) i

/-- Evaluation at `i` after the structure algebra map is the identity on
`ℂ`: the scalar embedding lands in the constant functions, and evaluating
a constant function at any component returns the scalar. -/
theorem eval_comp_algebraMap (i : Fin 12) :
    RingHom.comp (twelvePointEvalRingHom i) (algebraMap ℂ (Fin 12 → ℂ)) =
      RingHom.id ℂ := by
  ext r
  show twelvePointEvalRingHom i ((algebraMap ℂ (Fin 12 → ℂ)) r) = r
  -- AUDIT-1: the evaluation homomorphism is `Function.eval` (reducible at
  -- the pin), the Pi algebra map at a component is the component algebra
  -- map (`Pi.algebraMap_apply`, proved by `rfl` at the pin), and the self
  -- algebra map of `ℂ` is the identity (`Algebra.algebraMap_self`, proved
  -- by `rfl` at the pin): the goal is definitional.
  rfl

/-- The `i`-th section as a scheme morphism `Spec ℂ ⟶ Spec (ℂ¹²)`. -/
def pointSectionHom (i : Fin 12) : complexBase ⟶ twelvePointWorld.X :=
  Spec.map (CommRingCat.ofHom (twelvePointEvalRingHom i))

/-- The section property: composing with the structure map of the twelve
point world returns the identity on the complex base.  The calculation is
the contravariance of `Spec.map` (`Spec.map_comp`) applied to
`eval_comp_algebraMap`, concluded by `Spec.map_eq_id`. -/
theorem pointSection_section (i : Fin 12) :
    pointSectionHom i ≫ twelvePointWorld.structureMap = 𝟙 complexBase := by
  have hring : (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) ≫
      (CommRingCat.ofHom (twelvePointEvalRingHom i)) =
      CommRingCat.ofHom (RingHom.id ℂ) := by
    -- AUDIT-2: bundled-hom composition; `ConcreteCategory.hom_comp`
    -- unfolds `(ofHom a ≫ ofHom b).hom = RingHom.comp b a`, and
    -- `CommRingCat.hom_ext` reduces to the underlying `RingHom`
    -- identity `eval_comp_algebraMap`.
    apply CommRingCat.hom_ext
    exact eval_comp_algebraMap i
  calc pointSectionHom i ≫ twelvePointWorld.structureMap
      = Spec.map (CommRingCat.ofHom (twelvePointEvalRingHom i)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) := rfl
    _ = Spec.map
          ((CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) ≫
            (CommRingCat.ofHom (twelvePointEvalRingHom i))) :=
          (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) := by rw [hring]
    _ = 𝟙 complexBase := Spec.map_id _

/-- The `i`-th section is a genuine complex point of the world. -/
def pointSection (i : Fin 12) : ComplexPoint twelvePointWorld :=
  ⟨pointSectionHom i, pointSection_section i⟩

/-! ## §3 THE CLASSIFICATION OF ALL SECTIONS -/

/-- The basis idempotent decomposition of every vector in `ℂ¹²`: each
function is the sum of its scalar-weighted basis idempotents, expressed
through the algebra map (the constant-function embedding) to avoid any
smul-instance ambiguity. -/
theorem pi_decomp (x : Fin 12 → ℂ) :
    (∑ k : Fin 12,
        algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin 12 → ℂ) =
      x := by
  funext i
  have hsum : (∑ k : Fin 12,
      (algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) :
        Fin 12 → ℂ)) i =
      ∑ k : Fin 12,
        (algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin 12 → ℂ) i :=
    Finset.sum_apply _ _ _
  rw [hsum]
  have hval : ∀ k : Fin 12,
      ((algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) :
        Fin 12 → ℂ)) i =
        (if i = k then x k else 0) := by
    intro k
    rw [Pi.mul_apply, Pi.single_apply]
    -- AUDIT-3: the Pi algebra map at a component is the component algebra
    -- map (`Pi.algebraMap_apply`, `rfl` at the pin), and the self algebra
    -- map of `ℂ` is the identity (`Algebra.algebraMap_self`, `rfl`).
    have hconst : (algebraMap ℂ (Fin 12 → ℂ) (x k)) i = x k := rfl
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
def sectionRingHom (f : ComplexPoint twelvePointWorld) :
    (Fin 12 → ℂ) →+* ℂ :=
  (Spec.homEquiv (R := CommRingCat.of (Fin 12 → ℂ)) (S := CommRingCat.of ℂ)
    f.1).hom

/-- The hom-level identity behind every section: composing the structure
algebra map with the section's preimage ring homomorphism returns the
identity.  This is the transport of the section condition through
`Spec.preimage_comp`, `Spec.preimage_map` and `Spec.preimage_id`. -/
theorem section_h_algebraMap (f : ComplexPoint twelvePointWorld) :
    (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) ≫
      (Spec.preimage (R := CommRingCat.of (Fin 12 → ℂ)) (S := CommRingCat.of ℂ)
        f.1) =
      𝟙 (CommRingCat.of ℂ) := by
  have h0 : f.1 ≫ twelvePointWorld.structureMap = 𝟙 complexBase := f.2
  have hs : twelvePointWorld.structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) := rfl
  calc (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) ≫
      (Spec.preimage (R := CommRingCat.of (Fin 12 → ℂ)) (S := CommRingCat.of ℂ)
        f.1)
      = Spec.preimage (twelvePointWorld.structureMap) ≫
          Spec.preimage (R := CommRingCat.of (Fin 12 → ℂ))
            (S := CommRingCat.of ℂ) f.1 := by
        simp only [hs, Spec.preimage_map]
        all_goals rfl
    _ = Spec.preimage (f.1 ≫ twelvePointWorld.structureMap) :=
          (Spec.preimage_comp _ _).symm
    _ = Spec.preimage (𝟙 complexBase) := by rw [h0]
    _ = 𝟙 (CommRingCat.of ℂ) := Spec.preimage_id

/-- Every section ring homomorphism composes with the structure algebra map
to the identity. -/
theorem sectionRingHom_comp_algebraMap (f : ComplexPoint twelvePointWorld) :
    RingHom.comp (sectionRingHom f) (algebraMap ℂ (Fin 12 → ℂ)) =
      RingHom.id ℂ := by
  have h := section_h_algebraMap f
  have h2 : RingHom.comp (sectionRingHom f) (algebraMap ℂ (Fin 12 → ℂ)) =
      ((CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ))) ≫
        (Spec.preimage (R := CommRingCat.of (Fin 12 → ℂ)) (S := CommRingCat.of ℂ)
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
theorem sectionRingHom_algebraMap_apply
    (f : ComplexPoint twelvePointWorld) (r : ℂ) :
    sectionRingHom f ((algebraMap ℂ (Fin 12 → ℂ)) r) = r :=
  congrArg (fun h => h r) (sectionRingHom_comp_algebraMap f)

/-- The basis idempotents multiply trivially: equal indices persist,
distinct indices annihilate. -/
theorem single_mul_single_self (k : Fin 12) :
    (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ) : Fin 12 → ℂ) =
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

theorem single_mul_single_ne {k j : Fin 12} (hkj : k ≠ j) :
    (Pi.single k (1 : ℂ) * Pi.single j (1 : ℂ) : Fin 12 → ℂ) = 0 := by
  funext i
  rw [Pi.mul_apply, Pi.single_apply, Pi.single_apply]
  by_cases hik : i = k
  · rw [if_pos hik, if_neg (fun h => hkj (hik.symm.trans h)), mul_zero,
      Pi.zero_apply]
  · rw [if_neg hik, zero_mul, Pi.zero_apply]

/-- The sum of the twelve basis idempotents is the multiplicative unit. -/
theorem sum_single_eq_one :
    ∑ k : Fin 12, Pi.single k (1 : ℂ) = 1 := by
  have h' : (∑ k : Fin 12, Pi.single k (1 : ℂ) : Fin 12 → ℂ) =
      (fun _ : Fin 12 => (1 : ℂ)) := by
    simpa only [map_one, one_mul] using pi_decomp (fun _ => (1 : ℂ))
  exact h'
  -- AUDIT: the instantiated decomposition has summands
  -- `algebraMap ℂ (Fin 12 → ℂ) ((fun _ => (1 : ℂ)) k) * Pi.single k (1 : ℂ)`;
  -- `map_one` and `one_mul` reduce them to `Pi.single k (1 : ℂ)`, and the
  -- function `fun _ => (1 : ℂ)` is definitionally the Pi-one (the `exact`
  -- closes across the `Pi.one` seam at default transparency — CI 43793762987
  -- error at 241:2 was the `simpa`-normalized `fun x => 1` vs `1` mismatch).

/-- A section ring homomorphism sends exactly one basis idempotent to `1`. -/
theorem sectionRingHom_single_one (f : ComplexPoint twelvePointWorld) :
    ∃! k : Fin 12, sectionRingHom f (Pi.single k (1 : ℂ)) = 1 := by
  have hvals : ∀ k : Fin 12,
      sectionRingHom f (Pi.single k (1 : ℂ)) = 0 ∨
      sectionRingHom f (Pi.single k (1 : ℂ)) = 1 := by
    intro k
    apply eq_zero_or_one_of_sq_eq_self
    have hmul : sectionRingHom f (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ))
        = sectionRingHom f (Pi.single k (1 : ℂ)) :=
      congrArg (sectionRingHom f) (single_mul_single_self k)
    rw [map_mul] at hmul
    rw [pow_two, hmul]
  -- the sum of the twelve values is one
  have hsum : ∑ k : Fin 12, sectionRingHom f (Pi.single k (1 : ℂ)) = 1 := by
    have h : sectionRingHom f (∑ k : Fin 12, Pi.single k (1 : ℂ)) = 1 := by
      rw [sum_single_eq_one, map_one]
    rw [map_sum] at h
    exact h
  -- at most one value is one: two distinct ones would multiply to 0 = 1
  have hatmost : ∀ k j : Fin 12, k ≠ j →
      sectionRingHom f (Pi.single k (1 : ℂ)) = 1 →
      sectionRingHom f (Pi.single j (1 : ℂ)) ≠ 1 := by
    intro k j hkj hk1 hcontra
    have hprod : sectionRingHom f (Pi.single k (1 : ℂ) * Pi.single j (1 : ℂ)) = 0 := by
      rw [single_mul_single_ne hkj, map_zero]
    rw [map_mul, hk1, hcontra, one_mul] at hprod
    exact absurd hprod.symm zero_ne_one
  -- at least one value is one (else the sum would be zero)
  obtain ⟨k₀, hk₀⟩ : ∃ k : Fin 12, sectionRingHom f (Pi.single k (1 : ℂ)) = 1 := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ k : Fin 12, sectionRingHom f (Pi.single k (1 : ℂ)) = 0 := by
      intro k
      rcases hvals k with h | h
      · exact h
      · exact absurd h (hnone k)
    rw [Finset.sum_eq_zero (fun k _ => hzero k)] at hsum
    exact zero_ne_one hsum
  refine ⟨k₀, hk₀, fun j hj => ?_⟩
  by_contra hkj
  exact hatmost k₀ j (Ne.symm hkj) hk₀ hj

/-- **THE CLASSIFICATION.**  Every complex point (section) of the twelve
point world is exactly one of the twelve evaluation sections. -/
theorem complexPoint_eq (f : ComplexPoint twelvePointWorld) :
    ∃ i : Fin 12, f.1 = pointSectionHom i := by
  obtain ⟨k₀, hk₀, huniq⟩ := sectionRingHom_single_one f
  -- the section ring homomorphism is the evaluation at k₀
  have heq : sectionRingHom f = twelvePointEvalRingHom k₀ := by
    -- AUDIT-8: `ext` picks `RingHom.pi_ext` from the registry, which
    -- decomposes at `Pi.single x x✝` (two levels, CI 43800560334 errors at
    -- 313:35/317:37/330:42 — `x : Fin 12` applied at `k`); the proof is
    -- written for the full-function variable, so the extensionality is
    -- pinned to the one-level generic `DFunLike.ext` (Mathlib's own idiom at
    -- the pin, Data/FunLike/Ring.lean:32).
    apply DFunLike.ext
    intro x
    have hdx : x = (∑ k : Fin 12,
        algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) : Fin 12 → ℂ) :=
      (pi_decomp x).symm
    have hsrw : sectionRingHom f x =
        sectionRingHom f (∑ k : Fin 12,
          (algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ) :
            Fin 12 → ℂ)) :=
      congrArg (fun s => sectionRingHom f s) hdx
    -- AUDIT-9: the 0-or-1 dichotomy of the basis idempotents' values, the
    -- same `eq_zero_or_one_of_sq_eq_self` spine that carries
    -- `sectionRingHom_single_one` (CI 43800560334 error at 326:27 — the
    -- by_contra had only `¬ = 0`, which does not produce the `= 1` that
    -- `huniq` consumes).
    have hval01 : ∀ k : Fin 12,
        sectionRingHom f (Pi.single k (1 : ℂ)) = 0 ∨
        sectionRingHom f (Pi.single k (1 : ℂ)) = 1 := by
      intro k
      apply eq_zero_or_one_of_sq_eq_self
      have hmul : sectionRingHom f (Pi.single k (1 : ℂ) * Pi.single k (1 : ℂ))
          = sectionRingHom f (Pi.single k (1 : ℂ)) :=
        congrArg (sectionRingHom f) (single_mul_single_self k)
      rw [map_mul] at hmul
      rw [pow_two, hmul]
    have hvals : ∀ k : Fin 12,
        sectionRingHom f (Pi.single k (1 : ℂ)) = (if k = k₀ then 1 else 0) := by
      intro k
      by_cases hkk : k = k₀
      · rw [hkk, if_pos rfl, hk₀]
      · rw [if_neg hkk]
        rcases hval01 k with h0 | h1
        · exact h0
        · exact absurd (huniq k h1) hkk
    calc sectionRingHom f x
        = ∑ k : Fin 12,
            sectionRingHom f
              (algebraMap ℂ (Fin 12 → ℂ) (x k) * Pi.single k (1 : ℂ)) := by
          rw [hsrw, map_sum]
      _ = ∑ k : Fin 12,
            x k * sectionRingHom f (Pi.single k (1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_mul, sectionRingHom_algebraMap_apply]
      _ = x k₀ := by
          have hterm : ∀ k : Fin 12,
              x k * sectionRingHom f (Pi.single k (1 : ℂ)) =
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
  have hhom : (Spec.preimage (R := CommRingCat.of (Fin 12 → ℂ))
      (S := CommRingCat.of ℂ) f.1) =
      CommRingCat.ofHom (twelvePointEvalRingHom k₀) := by
    -- AUDIT-6: bundled-hom equality through the underlying `RingHom`.
    apply CommRingCat.hom_ext
    exact heq
  have hmap : f.1 = Spec.map (Spec.preimage
      (R := CommRingCat.of (Fin 12 → ℂ)) (S := CommRingCat.of ℂ) f.1) :=
    (Spec.map_preimage _).symm
  rw [hmap, hhom]
  exact ⟨k₀, rfl⟩

/-- The twelve sections are pairwise distinct. -/
theorem pointSection_injective :
    Function.Injective (fun i => pointSection i) := by
  intro i j hij
  have h : pointSectionHom i = pointSectionHom j := congrArg (·.1) hij
  -- AUDIT-7: the `ofHom` wrapper's underlying `RingHom`, recovered through
  -- `Spec.map_inj` (the pinned iff-form; `Spec.map_injective` is a plain
  -- `Function.Injective` fact, not a rewrite rule).
  have h2 : twelvePointEvalRingHom i = twelvePointEvalRingHom j :=
    congrArg (fun g => g.hom) (Spec.map_inj.mp h)
  have hv : twelvePointEvalRingHom i (Pi.single i (1 : ℂ)) =
      twelvePointEvalRingHom j (Pi.single i (1 : ℂ)) := by rw [h2]
  have hli : twelvePointEvalRingHom i (Pi.single i (1 : ℂ)) = 1 := by
    -- AUDIT-10 (wave 14): the defeq `twelvePointEvalRingHom i g ≡ g i` exposed
    -- by a `show` whose `Pi.single` dependent family is pinned by an explicit
    -- type ascription — the corpus's own battle-tested idiom (the ascription
    -- sites at :137/:141/:144/:148/:228/:241/:252 all elaborated clean in run
    -- 43832523181).  The bare `show (Pi.single i (1 : ℂ)) i = 1` leaves the
    -- family a bare metavariable `?m.76` with no expected type, and `1 : ℂ`
    -- collides with `?m.76 i` (CI 43832523181, error at 410:22); the pinned
    -- `Pi.single_eq_same` (Algebra/Notation/Pi/Basic.lean:32 at the pin, args
    -- `(i : ι) (x : M i)` both explicit) then unifies against the clean
    -- application.
    show ((Pi.single i (1 : ℂ) : Fin 12 → ℂ)) i = 1
    -- WAVE 16 (run-15 error at 416:30): the lemma call's own family binder is
    -- a bare metavariable `?m.88 i` against `1 : ℂ` — pinned by the named
    -- implicit `M`, Mathlib's own idiom at the pin (Finsupp/Single.lean,
    -- `single_eq_same`'s proof: `exact Pi.single_eq_same (M := fun _ ↦ M) a b`).
    exact Pi.single_eq_same (M := fun _ : Fin 12 => ℂ) i (1 : ℂ)
  have hrj : twelvePointEvalRingHom j (Pi.single i (1 : ℂ)) =
      (if j = i then (1 : ℂ) else 0) :=
    Pi.single_apply i (1 : ℂ) j
  -- AUDIT: the `show`-normalizations of the original put `Pi.single` in
  -- application-head position with no expected type (the implicit-β seam,
  -- CI 43793762987 errors at 361/365); the defeq
  -- `twelvePointEvalRingHom i g ≡ g i` is kernel-proven by the clean receipt
  -- `eval_comp_algebraMap`, so the pinned lemmas close directly.
  rw [hli, hrj] at hv
  by_cases hij' : i = j
  · exact hij'
  · have hne : ¬(j = i) := fun hcon => hij' hcon.symm
    rw [if_neg hne] at hv
    exact absurd hv.symm zero_ne_one

/-- **THE POINT EQUIVALENCE.**  The complex points of the twelve-point world
are exactly the twelve evaluation sections. -/
noncomputable def twelvePointSectionEquiv :
    Fin 12 ≃ ComplexPoint twelvePointWorld :=
  Equiv.ofBijective (fun i => pointSection i)
    ⟨pointSection_injective,
     fun f => by
       obtain ⟨i, hi⟩ := complexPoint_eq f
       exact ⟨i, Subtype.ext hi.symm⟩⟩

/-- **THE FIRST GENUINE ANALYTIFICATION.**  The discrete twelve-point space
with the genuine point classification. -/
noncomputable def twelvePointAnalytification :
    AnalytificationData twelvePointWorld where
  space := twelvePointSpace
  pointsEquiv :=
    twelvePointSectionEquiv.symm.trans
      (Equiv.cast twelvePointSpace_coe.symm)

/-! ## Receipts -/

#check twelvePointSpace
#check twelvePointSpace_coe
#check twelvePointSpace_totallyDisconnected
#check twelvePointEvalRingHom
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
#check twelvePointSectionEquiv
#check twelvePointAnalytification

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
#print axioms twelvePointSectionEquiv
#print axioms twelvePointAnalytification

end GSTTwelvePointAnalytification

end -- noncomputable section
