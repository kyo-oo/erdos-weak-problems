/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import HCUniverse2.GSTProjectiveOverC

/-!
# THE TWELVE-POINT WORLD CARRIER

This file manufactures the first genuine *twelve-point world*: an actual
complex scheme carrying exactly twelve closed points, an actual closed
projective embedding into the true projective line, and an actual smooth
structure morphism over `Spec(C)`.

The carrier is the affine scheme `Spec(C^12)`.  Its twelve points are the
kernels of the twelve coordinate projections.  The embedding into `P^1` is
`Proj.fromOfGlobalSections` of the evaluation homomorphism

`C[X0, X1] --> C^12,  X0 |-> nodeValues,  X1 |-> 1,`

where `nodeValues i = i`.  Surjectivity of the affine chart maps is classical
Lagrange interpolation through twelve distinct complex nodes, lifted to
homogeneous forms by homogenization.

Downstream contract (exports of this module):

* `twelvePointScheme`, `twelvePointStructureMap`, `twelvePointWorld`;
* `twelvePointEquiv : Fin 12 ≃ {x : twelvePointScheme // Order.coheight x = 0}`;
* `twelvePointCompactSpace`, `nodeValues_injective`.

This file contains no Hodge classes, no cycle-class surjectivity, and no form
of the Hodge conjecture.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open GSTProjectiveOverC

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTTwelvePointWorldCarrier

/-! ### The affine carrier and its smooth structure -/

/-- The twelve-point world: the spectrum of twelve copies of the complex
numbers.  An `abbrev` (reducible alias), like `complexBase` and
`ProjectiveGrading` before it: `rw` pattern matching and instance synthesis
run at `.instances` transparency, where a plain `def` is opaque — the
`Γ(twelvePointScheme, ⊤)` / `Γ(Spec (CommRingCat.of (Fin 12 → ℂ)), ⊤)`
boundary bled five CI errors (run 43767848609) before this. -/
abbrev twelvePointScheme : Scheme := Spec (CommRingCat.of (Fin 12 → ℂ))

/-- The structure morphism to the complex base, induced by the diagonal
`C -> C^12` (constant families). -/
def twelvePointStructureMap : twelvePointScheme ⟶ complexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ)))

/-- The structure morphism is smooth: `C^12` is a smooth `C`-algebra. -/
theorem twelvePoint_smooth : Smooth twelvePointStructureMap :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-! ### The twelve nodes -/

/-- The twelve node values: `i |-> i` in `C`, pairwise distinct complex
numbers (the Lagrange interpolation nodes). -/
def nodeValues : Fin 12 → ℂ := fun i => (i.val : ℂ)

theorem nodeValues_injective : Function.Injective nodeValues := by
  intro a b h
  -- `C` is of characteristic zero, so the natural-number cast is injective,
  -- and `Fin.val` is injective.
  have h' : (a.val : ℂ) = (b.val : ℂ) := h
  exact Fin.val_injective (Nat.cast_injective h')
  -- AUDIT: cast bookkeeping; alternates `Fin.val_inj` / `Fin.ext`,
  -- `Nat.cast_inj.mp`.

/-- Distinctness of the nodes on the whole type — the Lagrange side
condition. -/
theorem nodeValues_injOn : Set.InjOn nodeValues Set.univ :=
  nodeValues_injective.injOn
  -- AUDIT: `Function.Injective.injOn`; avoids the `Set.InjOn` binder-shape
  -- (membership vs subtype form) of the pinned revision.

/-! ### The graded ring, the evaluation, and the global-sections map -/

/-- The standard total-degree grading on `C[X0, X1]`; definitionally equal to
`ProjectiveGrading 1` from the geometry front, so no transport is needed. -/
abbrev grading : ℕ → Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℂ

/-- Ring homomorphism evaluating `C[X0, X1]` at the twelve nodes:
`X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def evalRingHom12 : MvPolynomial (Fin 2) ℂ →+* (Fin 12 → ℂ) :=
  (MvPolynomial.aeval ![nodeValues, fun _ => 1]).toRingHom

/-- The same evaluation, transported to global sections of the twelve-point
scheme via the canonical `Γ(Spec C^12, ⊤) ≅ C^12` isomorphism.

AUDIT: the `Scheme.ΓSpecIso` invocation follows Mathlib Scheme.lean:602
(`(ΓSpecIso R).inv.hom : R →+* Γ(Spec R, ⊤)`); if the pinned revision prefers
the `ΓSpecIso_hom_toSpecZero`-style simp normalization, this def is the place
to adjust. -/
noncomputable def sectionRingHom : MvPolynomial (Fin 2) ℂ →+* Γ(twelvePointScheme, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom.comp evalRingHom12

/-- The first coordinate evaluates to the unit: `X1 |-> 1`. -/
private theorem eval_X_one : evalRingHom12 (MvPolynomial.X 1) = 1 := by
  show MvPolynomial.aeval ![nodeValues, fun _ => 1] (MvPolynomial.X 1) = 1
  rw [MvPolynomial.aeval_X]
  -- `![u, v] 1 = v` and `v = (fun _ => 1)` is the pointwise unit.
  -- AUDIT: matrix-notation evaluation; alternate `Matrix.cons_val_one`.
  rfl

/-- Under `sectionRingHom`, the first coordinate is the unit of the global
sections ring. -/
private theorem section_X_one : sectionRingHom (MvPolynomial.X 1) = 1 := by
  -- `sectionRingHom` is `evalRingHom12` followed by the inverse of the
  -- `Γ(Spec C^12, ⊤) ≅ C^12` isomorphism, so it maps `X1 |-> 1 |-> 1`.
  show (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
      (evalRingHom12 (MvPolynomial.X 1)) = 1
  rw [eval_X_one]
  exact map_one _

/-- The image of the irrelevant ideal under `sectionRingHom` is everything:
`X1` lies in the irrelevant ideal and evaluates to the unit. -/
theorem section_hf :
    (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionRingHom = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  have hmem : sectionRingHom (MvPolynomial.X 1) ∈
      (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionRingHom :=
    Ideal.mem_map_of_mem sectionRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem grading zero_lt_one
        (by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_X ℂ 1))
  rw [section_X_one] at hmem
  exact hmem
  -- AUDIT: the degree side condition is `0 < 1` (`zero_lt_one`); the
  -- membership shape `mem_irrelevant_of_mem` + `mem_homogeneousSubmodule`
  -- follows the pinned ProjectiveSpectrum API.

/-! ### The embedding into the projective line -/

/-- The closed embedding of the twelve-point world into the projective line,
from the global sections `X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def twelvePointEmbedding : twelvePointScheme ⟶ projectiveSpace 1 :=
  Proj.fromOfGlobalSections grading sectionRingHom section_hf

/-- The variables generate the homogeneous coordinate ring as an algebra over
its degree-zero piece — the `D₊(X₀) ∪ D₊(X₁) = P¹` cover side condition, via
`Proj.iSup_basicOpen_eq_top'` (the adjoin route; the same green idiom as
`GSTCompactNativeCyclePresentation.projectiveSpace_isCompact_univ`). -/
theorem span_cover :
    Algebra.adjoin (↑(grading 0))
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) = ⊤ := by
  set S := Algebra.adjoin (↑(grading 0))
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ))
  refine top_unique fun p hp => ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact S.algebraMap_mem
        ⟨MvPolynomial.C a,
          MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := ℂ) a⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p j hp => exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self j))

/-- Every variable is homogeneous of degree one — the finiteness side
condition of `Proj.iSup_basicOpen_eq_top'`. -/
theorem variables_homogeneous (j : Fin 2) :
    ∃ n : ℕ, MvPolynomial.X j ∈ grading n := by
  refine ⟨1, ?_⟩
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X ℂ j

/-! ### The Lagrange cores -/

/-- Lagrange interpolation through the twelve distinct nodes: any value
vector on the nodes is realized by a polynomial of degree at most eleven. -/
private theorem exists_interpolating (y : Fin 12 → ℂ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ 11 ∧ ∀ i : Fin 12, q.eval (nodeValues i) = y i := by
  refine ⟨Lagrange.interpolate (Finset.univ : Finset (Fin 12)) nodeValues y, ?_, ?_⟩
  · -- degree < card univ = 12, hence ≤ 11
    -- AUDIT: Lagrange API (`Mathlib/LinearAlgebra/Lagrange.lean`):
    -- `degree_interpolate_lt` binds `(r) (hvs : Set.InjOn v ↑s)` with `r`
    -- explicit first; the degree-to-natDegree conversion is
    -- `Polynomial.natDegree_lt_iff_degree_lt` (Degree/Defs.lean), with the
    -- zero-polynomial case discharged separately.
    refine Nat.le_of_lt_succ ?_
    by_cases h0 : Lagrange.interpolate (Finset.univ : Finset (Fin 12)) nodeValues y = 0
    · rw [h0]; simp
    · have h := Lagrange.degree_interpolate_lt y
        (by rw [Finset.coe_univ]; exact nodeValues_injOn)
      rw [Finset.card_univ, Fintype.card_fin,
        ← Polynomial.natDegree_lt_iff_degree_lt h0] at h
      exact h
  · exact fun i => Lagrange.eval_interpolate_at_node y (by
      rw [Finset.coe_univ]; exact nodeValues_injOn) (Finset.mem_univ i)

/-- Homogeneous lift along the chart `X1 = 1`: a univariate `q` of degree at
most `N` homogenizes to a degree-`N` form whose node-evaluation is `q` at the
nodes. -/
private theorem homogenize_chart_eval (N : ℕ) (q : Polynomial ℂ)
    (hq : q.natDegree ≤ N) :
    ∃ p : MvPolynomial (Fin 2) ℂ,
      p ∈ grading N ∧ evalRingHom12 p = fun i => q.eval (nodeValues i) := by
  refine ⟨q.homogenize N, ?_, ?_⟩
  · -- AUDIT: `Polynomial.isHomogeneous_homogenize q` (Homogenize.lean:160)
    -- proves `(q.homogenize N).IsHomogeneous N` unconditionally; membership in
    -- `homogeneousSubmodule` is `IsHomogeneous` by `Iff.rfl`.
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact Polynomial.isHomogeneous_homogenize q
  · -- AUDIT: `Polynomial.aeval_homogenize_of_eq_one (hn) (g) (hg : g 1 = 1)`
    -- (Homogenize.lean:148) transports the Pi-algebra evaluation of the
    -- homogenized form to the univariate `aeval` at `nodeValues`; the
    -- Pi-algebra evaluation is componentwise node evaluation.
    show MvPolynomial.aeval ![nodeValues, fun _ => 1] (q.homogenize N) =
      fun i => q.eval (nodeValues i)
    rw [Polynomial.aeval_homogenize_of_eq_one hq
      (![nodeValues, fun _ => 1] : Fin 2 → (Fin 12 → ℂ)) rfl]
    funext i
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum]

/-- Lagrange surjectivity core, chart `j = 1` (the section of `X1` is the
unit): every value vector on the twelve nodes is realized by a homogeneous
form of degree `N`. -/
private theorem chart_core_one (y : Fin 12 → ℂ) :
    ∃ (N : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading N ∧ ∀ i : Fin 12, evalRingHom12 p i = y i := by
  obtain ⟨q, hqdeg, hqeval⟩ := exists_interpolating y
  obtain ⟨p, hp, hpeval⟩ := homogenize_chart_eval 11 q hqdeg
  exact ⟨11, p, hp, fun i => by rw [hpeval]; exact hqeval i⟩

/-- Lagrange surjectivity core, chart `j = 0` (the section of `X0` is
`nodeValues`): for every value vector `y` and every denominator exponent
`N` there is a homogeneous form `p` of degree `M` with
`p(v i) * (v i)^N = y i * (v i)^M` — the `mk'`-cancellation identity of the
away-localization. -/
private theorem chart_core_zero (y : Fin 12 → ℂ) (N : ℕ) :
    ∃ (M : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading M ∧ ∀ i : Fin 12,
        evalRingHom12 p i * (nodeValues i)^N = y i * (nodeValues i)^M := by
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_interpolating (fun i => y i * (nodeValues i)^11)
  obtain ⟨p, hp, hpeval⟩ := homogenize_chart_eval (N + 11) q (le_trans hqdeg (by omega))
  refine ⟨N + 11, p, hp, fun i => ?_⟩
  have hval : evalRingHom12 p i = q.eval (nodeValues i) := by rw [hpeval]
  rw [hval, hqeval i]
  -- `y i * a ^ 11 * a ^ N = y i * a ^ (N + 11)`
  ring

/-- The first coordinate evaluates to the node values: `X0 |-> nodeValues`. -/
private theorem eval_X_zero : evalRingHom12 (MvPolynomial.X 0) = nodeValues := by
  show MvPolynomial.aeval ![nodeValues, fun _ => 1] (MvPolynomial.X 0) = nodeValues
  rw [MvPolynomial.aeval_X]
  rfl
  -- AUDIT: matrix-notation evaluation at index 0; alternate
  -- `Matrix.cons_val_zero` (mirror of `eval_X_one` below).

/-! ### The closed immersion -/

/-- The submonoid side condition of the localization transport: the powers
of `X j` map into the powers of its section.  Stated standalone so the
definition and the computation below ride the same proof (proof
irrelevance makes the two uses definitionally equal). -/
private theorem chartRingMap_le (j : Fin 2) :
    Submonoid.powers (MvPolynomial.X j) ≤
      (Submonoid.powers (sectionRingHom (MvPolynomial.X j))).comap sectionRingHom := by
  rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]

/-- The ring-level chart map at the variable `X j`: the `IsLocalization.map`
composite inside `Proj.toBasicOpenOfGlobalSections` (pinned
ProjectiveSpectrum/Basic.lean:369-377), from the degree-`0` homogeneous
localization `HomogeneousLocalization.Away grading (MvPolynomial.X j)` (the
`D₊(X j)` chart ring — the domain forced by `basicOpenIsoSpec`'s target) to
the away-localization of its section.  Surjectivity of this ring map is the
Lagrange interpolation core of the embedding. -/
private noncomputable def chartRingMap (j : Fin 2) :
    HomogeneousLocalization.Away grading (MvPolynomial.X j) →+*
      Localization.Away (sectionRingHom (MvPolynomial.X j)) :=
  RingHom.comp
    (IsLocalization.map
      (R := MvPolynomial (Fin 2) ℂ)
      (S := Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
      (M := Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
      (P := Γ(twelvePointScheme, ⊤))
      (T := Submonoid.powers (sectionRingHom (MvPolynomial.X j)))
      (Q := Localization.Away (sectionRingHom (MvPolynomial.X j)))
      sectionRingHom (chartRingMap_le j))
    (algebraMap (HomogeneousLocalization.Away grading (MvPolynomial.X j))
      (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)))
  -- AUDIT: term-mode transcription of the pinned `toBasicOpenOfGlobalSections`
  -- composite (ProjectiveSpectrum/Basic.lean:369-377), where the FIRST-applied
  -- factor is the `homogeneousLocalizationAlgebra` algebraMap
  -- (definitionally `HomogeneousLocalization.val`,
  -- GradedAlgebra/HomogeneousLocalization.lean:477-490) and the second is
  -- `IsLocalization.map` (Localization/Defs.lean:604).  The domain is the
  -- degree-0 homogeneous localization — CI run 43778820813 error 2 exposed
  -- the true composite (every earlier wave transcribed the wrong source
  -- ring).  All of `R S M P T Q` are given so every instance resolves
  -- against a concrete type, and each `MvPolynomial.X j` feeding an
  -- `Away`/`powers` head carries a type ascription pinning the coefficient
  -- ring to `ℂ`.

/-- The chart ring map on a homogeneous fraction `p / (X j)^k` is the
transported `mk'` fraction.  The proof is Mathlib's own computation spine of
this exact composite (ProjectiveSpectrum/Basic.lean:481-484): the away
`algebraMap` forgets the same-degree structure (`val`), `val_mk` exposes the
plain `Localization.mk` fraction, `mk_eq_mk'` rewrites it to `mk'` form, and
`map_mk'` transports numerator and denominator. -/
private theorem chartRingMap_apply (j : Fin 2) {d : ℕ}
    (hXj : MvPolynomial.X j ∈ grading d) (k : ℕ)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p ∈ grading (k • d)) :
    chartRingMap j (HomogeneousLocalization.Away.mk grading hXj k p hp) =
      IsLocalization.mk'
        (M := Submonoid.powers (sectionRingHom (MvPolynomial.X j)))
        (S := Localization.Away (sectionRingHom (MvPolynomial.X j)))
        (sectionRingHom p)
        ⟨sectionRingHom (MvPolynomial.X j) ^ k,
          (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩⟩ := by
  have h1 : chartRingMap j (HomogeneousLocalization.Away.mk grading hXj k p hp) =
      (IsLocalization.map
        (R := MvPolynomial (Fin 2) ℂ)
        (S := Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
        (M := Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
        (P := Γ(twelvePointScheme, ⊤))
        (T := Submonoid.powers (sectionRingHom (MvPolynomial.X j)))
        (Q := Localization.Away (sectionRingHom (MvPolynomial.X j)))
        sectionRingHom (chartRingMap_le j))
        ((algebraMap (HomogeneousLocalization.Away grading (MvPolynomial.X j))
          (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ)))
          (HomogeneousLocalization.Away.mk grading hXj k p hp)) := by
    -- the definition IS this composite: `RingHom.comp` is built with
    -- `toFun x := g (f x)` (`RingHom.comp_apply` is `rfl`), so the
    -- unfolding is definitional.
    first
    | rfl
    | (unfold chartRingMap; rfl)
    | (simp only [chartRingMap]; rfl)
  rw [h1, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk'_apply, IsLocalization.map_mk']
  simp only [Subtype.coe_mk, map_pow]
  all_goals rfl
  -- AUDIT: the first five rewrites are the pinned spine of Mathlib's own
  -- computation of this composite (ProjectiveSpectrum/Basic.lean:481-485).
  -- The last two normalizations are PROOF-DEPENDENT — the transported
  -- denominator's membership proof mentions the coerced constructor — so
  -- `rw` cannot cross them (motive not type correct: CI 43790217021,
  -- error at 347:4); `simp only`'s congruence machinery rebuilds the
  -- Subtype and discharges the proof difference by proof irrelevance —
  -- the same idiom that carried the four `Subtype.coe_mk`
  -- simp-normalizations in the chart branches below (CI-proven in the
  -- same run).  The closer `all_goals rfl` is zero-goal-safe (vacuous if
  -- the simp already closed the goal by proof irrelevance).

/-- Surjectivity of the `ΓSpecIso` inverse transport: every global section
of the twelve-point scheme is the transport of a vector. -/
private theorem gammaInv_surjective :
    Function.Surjective
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom := by
  intro g
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).hom.hom g, ?_⟩
  exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))) g
  -- AUDIT: the X-side round trip of the adjunction iso — the pinned
  -- `Iso.hom_inv_id_apply`, the same transport `Scheme.lean:851` itself
  -- applies to `ΓSpecIso`; the equation direction is direct (no `symm`).

/-- Injectivity of the `ΓSpecIso` inverse transport: a section is determined
by its vector. -/
private theorem gammaInv_injective :
    Function.Injective
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom := by
  have hli : Function.LeftInverse
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom :=
    fun r => Iso.inv_hom_id_apply
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))) r
  exact hli.injective
  -- AUDIT: the Y-side round trip; `Function.LeftInverse.injective`; the
  -- equation direction is direct (no `symm`).

/-- **The chart ring map is surjective — the Lagrange core.**  Every element
of the away-localization is a fraction `mk' y (f (X j))^N`
(`IsLocalization.exists_mk'_eq`, Localization/Defs.lean:305; the power
extraction is `Submonoid.mem_powers_iff`).  On chart `j = 0` the cleared
Lagrange identity of `chart_core_zero` (`p(v) · v^N = y · v^M` pointwise,
with `p` homogeneous of degree `M`) supplies the numerator, the homogeneous
fraction `p / X₀^M` the preimage, and one more factor of `v` the
`mk'`-clearing multiplier.  On chart `j = 1` the section of `X₁` is the
unit, so the interpolating form of `chart_core_one` is the preimage. -/
private theorem chartRingMap_surjective (j : Fin 2) :
    Function.Surjective (chartRingMap j) := by
  -- The fraction decomposition is obtained at GENERIC `j` (no embedded
  -- literal forms), then the two charts are dispatched by `Fin 2`'s
  -- two-element structure.
  intro z
  obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (M := .powers (sectionRingHom (MvPolynomial.X j))) z
  -- `s` is destructured first so that the power equation's side is a bare
  -- local (`subst` cannot eliminate the coercion `↑s`).
  obtain ⟨t, ht⟩ := s
  obtain ⟨N, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ht
  obtain ⟨y', hy'⟩ := gammaInv_surjective y
  by_cases hj : j = 0
  · subst hj
    -- chart `j = 0`: the cleared Lagrange identity at all twelve nodes.
    obtain ⟨M, p, hp, hpt⟩ := chart_core_zero y' N
    have hXj : MvPolynomial.X 0 ∈ grading 1 := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X ℂ 0
    have hpnsm : p ∈ grading (M • 1) := by rwa [nsmul_one]
    -- the vector identity, one node-value higher than `hpt`
    have hvec : evalRingHom12 p * nodeValues ^ (N + 1) =
        y' * nodeValues ^ (M + 1) := by
      funext i
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [pow_succ, ← mul_assoc, pow_succ, ← mul_assoc, hpt i]
    -- the section-level identity (the `ΓSpecIso` transport)
    have hΓ : sectionRingHom p * sectionRingHom (MvPolynomial.X 0) ^ (N + 1) =
        y * sectionRingHom (MvPolynomial.X 0) ^ (M + 1) := by
      have e1 : sectionRingHom p =
          (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
            (evalRingHom12 p) := rfl
      have e2 : sectionRingHom (MvPolynomial.X 0) =
          (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
            (evalRingHom12 (MvPolynomial.X 0)) := rfl
      rw [e1, e2, eval_X_zero, ← map_pow, ← map_mul, ← hy', ← map_pow, ← map_mul]
      exact congrArg _ hvec
    refine ⟨HomogeneousLocalization.Away.mk grading hXj M p hpnsm, ?_⟩
    rw [chartRingMap_apply]
    refine (IsLocalization.mk'_eq_iff_eq'
      (S := Localization.Away (sectionRingHom (MvPolynomial.X 0)))
      (M := Submonoid.powers (sectionRingHom (MvPolynomial.X 0)))).mpr ?_
    simp only [Subtype.coe_mk]
    refine (IsLocalization.eq_iff_exists
      (M := Submonoid.powers (sectionRingHom (MvPolynomial.X 0)))
      (S := Localization.Away (sectionRingHom (MvPolynomial.X 0)))
      (x := sectionRingHom p * sectionRingHom (MvPolynomial.X 0) ^ N)
      (y := y * sectionRingHom (MvPolynomial.X 0) ^ M)).mpr
      ⟨⟨sectionRingHom (MvPolynomial.X 0),
        Submonoid.mem_powers _⟩, ?_⟩
    simp only [Subtype.coe_mk]
    rw [show sectionRingHom (MvPolynomial.X 0) * (sectionRingHom p *
        sectionRingHom (MvPolynomial.X 0) ^ N) =
      sectionRingHom p * sectionRingHom (MvPolynomial.X 0) ^ (N + 1) from by ring,
      show sectionRingHom (MvPolynomial.X 0) * (y *
        sectionRingHom (MvPolynomial.X 0) ^ M) =
      y * sectionRingHom (MvPolynomial.X 0) ^ (M + 1) from by ring]
    exact hΓ
  · have hj1 : j = 1 := Fin.ext (by
      have h := j.isLt
      have hne : j.val ≠ 0 := fun h0 => hj (Fin.ext h0)
      omega)
    subst hj1
    -- chart `j = 1`: the section of `X₁` is the unit.
    obtain ⟨M, p, hp, hpeval⟩ := chart_core_one y'
    have hXj : MvPolynomial.X 1 ∈ grading 1 := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X ℂ 1
    have hpnsm : p ∈ grading (M • 1) := by rwa [nsmul_one]
    have hΓ : sectionRingHom p = y := by
      show (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
          (evalRingHom12 p) = y
      rw [← hy']
      exact congrArg _ (funext hpeval)
    refine ⟨HomogeneousLocalization.Away.mk grading hXj M p hpnsm, ?_⟩
    rw [chartRingMap_apply]
    refine (IsLocalization.mk'_eq_iff_eq'
      (S := Localization.Away (sectionRingHom (MvPolynomial.X 1)))
      (M := Submonoid.powers (sectionRingHom (MvPolynomial.X 1)))).mpr ?_
    simp only [Subtype.coe_mk]
    refine (IsLocalization.eq_iff_exists
      (M := Submonoid.powers (sectionRingHom (MvPolynomial.X 1)))
      (S := Localization.Away (sectionRingHom (MvPolynomial.X 1)))
      (x := sectionRingHom p * sectionRingHom (MvPolynomial.X 1) ^ N)
      (y := y * sectionRingHom (MvPolynomial.X 1) ^ M)).mpr
      ⟨⟨sectionRingHom (MvPolynomial.X 1),
        Submonoid.mem_powers _⟩, ?_⟩
    -- the section of `X₁` is the unit: the clearing multiplier collapses
    simp only [Subtype.coe_mk, section_X_one, one_pow, one_mul, mul_one]
    exact hΓ
  -- AUDIT: the `mk'`-bookkeeping rides the pinned
  -- `IsLocalization.mk'_eq_iff_eq'` (Localization/Defs.lean:326) with the
  -- localization-equality criterion `IsLocalization.eq_iff_exists`
  -- (Localization/Defs.lean:165); the clearing multiplier is a single power
  -- of the chart section (`Submonoid.mem_powers`).  The j=0 branch needs
  -- the multiplier `f₀` (node 0 makes `f₀` a zero divisor — the identity is
  -- the CLEARED Lagrange form `chart_core_zero`, never a division); the j=1
  -- branch's multiplier is the unit.

/-- Per-chart closed immersion: restricted to each basic open `D+(X_j)`, the
twelve-point embedding is a closed immersion, because the chart ring map is
Lagrange-surjective. -/
private theorem chart_closed (j : Fin 2) :
    IsClosedImmersion (twelvePointEmbedding ∣_ Proj.basicOpen grading (MvPolynomial.X j)) := by
  have hXj : MvPolynomial.X j ∈ grading 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STAGE 0-1: retype the restricted embedding at `Proj grading` (the
  -- `projectiveSpace 1` wrapper is defeq but not reducible), then unfold
  -- the embedding to the `fromOfGlobalSections` head.
  rw [show (twelvePointEmbedding ∣_ Proj.basicOpen grading (MvPolynomial.X j)) =
    (Proj.fromOfGlobalSections grading sectionRingHom section_hf ∣_
      (Proj.basicOpen grading (MvPolynomial.X j))) from rfl]
  -- STAGE 1: the restriction rewrite
  -- (`Proj.fromOfGlobalSections_morphismRestrict`, Basic.lean:496)
  -- factorizes the restricted embedding through the affine chart map.
  rw [Proj.fromOfGlobalSections_morphismRestrict grading sectionRingHom section_hf
      zero_lt_one hXj]
  -- STAGE 2: unfold the chart composite (the pinned definition of
  -- `toBasicOpenOfGlobalSections`, Basic.lean:369): the goal becomes the
  -- isomorphism chunk on the left, the `Spec` of the chart ring map in the
  -- middle, and the target `basicOpenIsoSpec` isomorphism (inverted) on the
  -- right.  The chart ring map inside is *definitionally* `chartRingMap j`
  -- (transcribed verbatim in its definition above).
  simp only [Proj.toBasicOpenOfGlobalSections]
  -- STAGE 3-4: left-associate the composite, cancel the right target
  -- isomorphism (`basicOpenIsoSpec` inverted — the affine chart of the
  -- projective target), re-associate, and cancel the left isomorphism
  -- factors one at a time — the
  -- `Scheme.isoOfEq` hom of the morphismRestrict factorization, the
  -- `Scheme.isoOfEq` inv of the chart-source transport, the restriction of
  -- the affine `toSpecΓ` (`IsIso (f ∣_ U)` for `IsIso f`, Restrict.lean:639
  -- the twelve-point scheme is affine), and `basicOpenIsoSpecAway`
  -- (Restrict.lean:520) — then close by the affine closed-immersion
  -- criterion with the Lagrange surjectivity of the chart ring map.
  -- The peeling rides the `.mpr` direction of the cancel lemmas so that
  -- every factor match is definitional (proof-irrelevant iso arguments),
  -- not syntactic.
  simp only [← CategoryTheory.Category.assoc]
  refine (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
    _ (Proj.basicOpenIsoSpec grading (MvPolynomial.X j) hXj zero_lt_one).inv).mpr ?_
  simp only [CategoryTheory.Category.assoc]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    ((Scheme.isoOfEq twelvePointScheme
      (Proj.fromOfGlobalSections_preimage_basicOpen grading sectionRingHom
        section_hf zero_lt_one hXj)).hom) _).mpr ?_
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    ((Scheme.isoOfEq twelvePointScheme
      (Scheme.toSpecΓ_preimage_basicOpen twelvePointScheme
        (sectionRingHom (MvPolynomial.X j)))).inv) _).mpr ?_
  -- STAGE 5: the next left factor is `toSpecΓ ∣_ D(section)`, the
  -- restriction of the affine `toSpecΓ`; its `IsIso` side condition is the
  -- restriction instance (`instance (f) [IsIso f] (U) : IsIso (f ∣_ U)`,
  -- Restrict.lean:639) fed by `IsAffine.affine`
  -- (AffineScheme.lean:59).  Instance synthesis cannot find it through the
  -- def-alias alone: the chain is supplied explicitly; this is independent
  -- of the alias's reducibility.
  haveI haff : IsAffine twelvePointScheme :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Fin 12 → ℂ))))
  haveI hΓ : IsIso (twelvePointScheme.toSpecΓ) :=
    @IsAffine.affine twelvePointScheme haff
  haveI hΓU : IsIso (twelvePointScheme.toSpecΓ ∣_
      PrimeSpectrum.basicOpen (sectionRingHom (MvPolynomial.X j))) := by
    -- Mathlib's own instance body (Restrict.lean:639-640): unfold the
    -- restriction to its pullback composite and let instance synthesis find
    -- the iso structure there — the direct `inferInstance` on the
    -- restriction form gets stuck at the `Opens`-type seam (CI
    -- 43778820813 error 1), while the post-`delta` search works on the
    -- already-elaborated composite.
    delta AlgebraicGeometry.morphismRestrict
    infer_instance
  refine ((MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) _ _)).mpr ?_
  refine ((MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) _ _)).mpr ?_
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (chartRingMap j)) (chartRingMap_surjective j)

/-- **The twelve-point embedding is a closed immersion.** -/
theorem twelvePoint_closedImmersion : IsClosedImmersion twelvePointEmbedding :=
  IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion)
    (fun j => Proj.basicOpen grading (MvPolynomial.X j))
    (Proj.iSup_basicOpen_eq_top' grading MvPolynomial.X
      variables_homogeneous span_cover)
    (fun j => chart_closed j)
  -- AUDIT: `IsZariskiLocalAtTarget` is a root-namespace abbreviation
  -- (Morphisms/Basic.lean); the cover family is normalized to `MvPolynomial.X`,
  -- matching `Proj.iSup_basicOpen_eq_top'` (ProjectiveSpectrum/Basic.lean),
  -- whose adjoin side condition is `span_cover` above.

/-- The embedding commutes with the structure maps over `Spec(C)`. -/
theorem twelvePoint_over_base :
    twelvePointEmbedding ≫ projectiveSpaceToBase 1 = twelvePointStructureMap := by
  -- STAGE 1 (definitional): retype the whole composite at `Proj grading` —
  -- the `projectiveSpace 1` wrapper is defeq but not reducible, so the
  -- regrouping below must operate on the `Proj`-typed form; unfold the
  -- embedding and the base map in one definitional step.
  rw [show (twelvePointEmbedding ≫ projectiveSpaceToBase 1 :
      twelvePointScheme ⟶ complexBase) =
      (Proj.fromOfGlobalSections grading sectionRingHom section_hf ≫
        Proj.toSpecZero (ProjectiveGrading 1)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (ProjectiveGrading 1 0))) from rfl]
  -- STAGE 2 (the triangle identity, Basic.lean:515):
  -- `fromOfGlobalSections ≫ toSpecZero` is the `toSpecΓ` composite of the
  -- degree-zero part of `sectionRingHom`.  AUDIT: exact rewrite shape.
  rw [Proj.fromOfGlobalSections_toSpecZero]
  -- STAGE 3: constants stay constant through the degree-zero transport.
  -- The pinned lemma `fromOfGlobalSections_toSpecZero` produces the
  -- composite with the DEGREE-ZERO algebra map `A₀ → A` (not the constants
  -- `C → A`), so the ring identity is stated for the doubly-embedded
  -- constant and bridged by `IsScalarTower` (the definitional route is
  -- tried first).
  have hconst : ∀ c : ℂ,
      evalRingHom12 (algebraMap ℂ (MvPolynomial (Fin 2) ℂ) c) =
        (algebraMap ℂ (Fin 12 → ℂ) c) :=
    fun c => (MvPolynomial.aeval ![nodeValues, fun _ => 1]).commutes c
  have hzero : ∀ c : ℂ,
      evalRingHom12 ((algebraMap ↥(ProjectiveGrading 1 0)
          (MvPolynomial (Fin 2) ℂ))
          ((algebraMap ℂ ↥(ProjectiveGrading 1 0)) c)) =
        (algebraMap ℂ (Fin 12 → ℂ) c) := by
    intro c
    first
    | exact hconst c
    | (rw [IsScalarTower.algebraMap_apply]; exact hconst c)
    | (simp only [IsScalarTower.algebraMap_apply]; exact hconst c)
    | simp
  have hcomp : (sectionRingHom.comp (algebraMap ↥(ProjectiveGrading 1 0)
        (MvPolynomial (Fin 2) ℂ))).comp
      (algebraMap ℂ ↥(ProjectiveGrading 1 0)) =
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom.comp
        (algebraMap ℂ (Fin 12 → ℂ)) := by
    ext c
    show (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
        (evalRingHom12 ((algebraMap ↥(ProjectiveGrading 1 0)
          (MvPolynomial (Fin 2) ℂ))
          ((algebraMap ℂ ↥(ProjectiveGrading 1 0)) c))) =
      (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
        (algebraMap ℂ (Fin 12 → ℂ) c)
    rw [hzero c]
  -- STAGE 4: merge the two spectral factors into the single transported
  -- map, then cancel the adjunction inverse by the unit triangle
  -- `toSpecΓ ≫ Spec.map (ΓSpecIso _).inv = 𝟙`
  -- (GammaSpecAdjunction.lean:487-490).  AUDIT: every rewrite operates at
  -- the raw ring / `Spec (of C^12)` level (`ofHom`-composites split by
  -- `CommRingCat.ofHom_comp`, `Spec.map_comp`); the `twelvePointScheme`
  -- alias is bridged exactly once by the `show` below (pure defeq), never
  -- by cross-level syntactic matching inside a rewrite.
  rw [CategoryTheory.Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [hcomp]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  show (Spec (CommRingCat.of (Fin 12 → ℂ))).toSpecΓ ≫
      (Spec.map (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ)))
  rw [← CategoryTheory.Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of (Fin 12 → ℂ)),
    CategoryTheory.Category.id_comp]

/-! ### The world -/

/-- **THE TWELVE-POINT WORLD.**  The affine twelve-point scheme with its
smooth structure morphism and its closed projective embedding into `P^1`,
packaged as a `SmoothProjectiveComplexScheme`. -/
noncomputable def twelvePointWorld : SmoothProjectiveComplexScheme :=
  ⟨twelvePointScheme, twelvePointStructureMap, twelvePoint_smooth,
    ⟨1, twelvePointEmbedding, twelvePoint_closedImmersion, twelvePoint_over_base⟩⟩

/-! ### The twelve points -/

/-- Every point of the twelve-point scheme is closed (maximal in the
specialization order): all primes of the artinian ring `C^12` are maximal. -/
theorem twelvePoint_coheight (x : twelvePointScheme) :
    Order.coheight x = 0 := by
  -- `C^12` is artinian: each factor is artinian and the finite `Pi` type is
  -- artinian by instance synthesis (the `haveI` below did not error in CI).
  haveI hart : IsArtinianRing (Fin 12 → ℂ) := inferInstance
  refine Order.coheight_eq_zero.mpr (fun y hle => ?_)
  -- `hle : x ≤ y` in the scheme specialization order is `y ⤳ x` topologically
  -- (`Scheme.le_iff_specializes : a ≤ b ↔ b ⤳ a`); on the affine spectrum
  -- this is reverse ideal inclusion, bridged through `PrimeSpectrum`.
  have hsp : y ⤳ x := Scheme.le_iff_specializes.mp hle
  have hle' : (show PrimeSpectrum (Fin 12 → ℂ) from y).asIdeal ≤
      (show PrimeSpectrum (Fin 12 → ℂ) from x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hsp
  -- both point ideals are prime, hence maximal in the artinian ring; a
  -- maximal ideal below another maximal ideal is equal to it.
  have hyi : (show PrimeSpectrum (Fin 12 → ℂ) from y).asIdeal.IsPrime :=
    (show PrimeSpectrum (Fin 12 → ℂ) from y).isPrime
  have hxi : (show PrimeSpectrum (Fin 12 → ℂ) from x).asIdeal.IsPrime :=
    (show PrimeSpectrum (Fin 12 → ℂ) from x).isPrime
  have hymax : (show PrimeSpectrum (Fin 12 → ℂ) from y).asIdeal.IsMaximal :=
    (IsArtinianRing.isPrime_iff_isMaximal _).mp hyi
  have heq : (show PrimeSpectrum (Fin 12 → ℂ) from y).asIdeal =
      (show PrimeSpectrum (Fin 12 → ℂ) from x).asIdeal :=
    hymax.eq_of_le (Ideal.IsPrime.ne_top hxi) hle'
  -- the points are equal, so `y ≤ x` holds by reflexivity (the `rw` closes
  -- the goal through `le_refl`).
  rw [show y = x from PrimeSpectrum.ext heq]
  -- AUDIT: the order bridge is `Scheme.le_iff_specializes` (Scheme.lean,
  -- `a ≤ b ↔ b ⤳ a`) and `PrimeSpectrum.le_iff_specializes` (`x ≤ y ↔ x ⤳ y`,
  -- the inclusion order); the artinian step is
  -- `IsArtinianRing.isPrime_iff_isMaximal` (Artinian/Module.lean); the
  -- scheme-point and prime-spectrum carriers are definitionally identified.

/-- The twelve points of the world, indexed by `Fin 12`.  The prime spectrum
of a finite product is the sigma of the factor spectra; each
`PrimeSpectrum ℂ` is uniquely inhabited; and all points of the twelve-point
scheme have coheight zero, so the coheight-zero subtype is the whole
space. -/
noncomputable def twelvePointEquiv :
    Fin 12 ≃ {x : twelvePointScheme // Order.coheight x = 0} :=
  ((Equiv.sigmaUnique (Fin 12) (fun _ => PrimeSpectrum ℂ)).symm.trans
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : Fin 12 => ℂ)).toEquiv).trans
      (Equiv.subtypeUnivEquiv (fun p => twelvePoint_coheight p)).symm
  -- AUDIT: the `Equiv.cast`-level transport of the definitional
  -- identification `↥(Spec (of (Fin 12 → ℂ))) = PrimeSpectrum (Fin 12 → ℂ)`
  -- (`Spec_carrier`); the subtype predicates coincide because the
  -- scheme-point order and the prime-spectrum order are definitionally the
  -- same instance.

/-- Compactness: the twelve-point scheme is an affine spectrum, hence
compact.  (Stated as a *named* instance so that both the instance path and
the contracted name `twelvePointCompactSpace` are available downstream.) -/
noncomputable instance twelvePointCompactSpace : CompactSpace ↥twelvePointScheme :=
  PrimeSpectrum.compactSpace
  -- AUDIT: definitional transport `↥twelvePointScheme = ↥(PrimeSpectrum
  -- (Fin 12 → ℂ))`; the pinned `PrimeSpectrum.compactSpace` is an instance
  -- with the ring implicit — no explicit argument.

/-! ### Receipts -/

#check twelvePointScheme
#check twelvePointStructureMap
#check twelvePoint_smooth
#check nodeValues
#check nodeValues_injective
#check nodeValues_injOn
#check grading
#check evalRingHom12
#check sectionRingHom
#check section_hf
#check twelvePointEmbedding
#check span_cover
#check twelvePoint_closedImmersion
#check twelvePoint_over_base
#check twelvePointWorld
#check twelvePoint_coheight
#check twelvePointEquiv
#check twelvePointCompactSpace

#print axioms twelvePoint_smooth
#print axioms section_hf
#print axioms span_cover
#print axioms twelvePoint_closedImmersion
#print axioms twelvePoint_over_base
#print axioms twelvePoint_coheight
#print axioms twelvePointWorld

end GSTTwelvePointWorldCarrier
