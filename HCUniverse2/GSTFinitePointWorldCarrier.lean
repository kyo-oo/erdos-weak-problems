/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
Adapted (Wave 42, Agent A2) from the corpus's arity-12 world carrier to the
general finite-point lane; proof bodies ported verbatim under the campaign
rename map, with the 12-specific numerals re-derived at variable `N`.
-/
import HCUniverse2.GSTProjectiveOverC

/-!
# THE GENERAL FINITE-POINT WORLD CARRIER

This file manufactures the general finite-point world: for every nonzero
natural number `N`, an actual complex scheme carrying exactly `N` closed
points, an actual closed projective embedding of the `N` distinct points
into the true projective line, and an actual smooth structure morphism over
`Spec(ℂ)`.

The carrier is the affine scheme `Spec(ℂ^N)` = `Spec (Fin N → ℂ)`.  Its `N`
points are the kernels of the `N` coordinate projections.  The embedding
into `P^1` places the `N` distinct nodes `nodeValues i = (i : ℂ)` on the
projective line and is `Proj.fromOfGlobalSections` of the evaluation
homomorphism

`ℂ[X0, X1] --> ℂ^N,  X0 |-> nodeValues,  X1 |-> 1.`

Surjectivity of the affine chart maps is classical Lagrange interpolation
through `N` distinct complex nodes, lifted to homogeneous forms by
homogenization.  The motivating instance is `N = 12` — the twelve-point
world of the ancestor carrier module this file ports (the first genuine
geometric world of the corpus); everything below is its uniform-`N`
generalization.

Downstream contract (exports of this module, the Wave-42 general-N lane):

* `finitePointScheme`, `finitePointStructureMap`, `finitePointWorld`;
* `finitePointEquiv : Fin N ≃ {x : finitePointScheme N //
  Order.coheight x = 0}` — definitionally `CodimensionPoint
  (finitePointWorld N).X 0`; the sibling Hodge-data lane destructures
  `(finitePointEquiv N i).1` / `(finitePointEquiv N i).2` directly;
* `finitePoint_smooth`, `finitePointCompactSpace`, `nodeValues_injective`.

Binder discipline (lane law, matching the sibling analytification file):
every declaration that mentions `N` takes `(N : ℕ) [NeZero N]` as its
leading explicit binders.  The empty world `N = 0` is rejected by the lane
(`Fin 0 → ℂ` is the zero ring).

This file contains no Hodge classes, no cycle-class surjectivity, and no
form of the Hodge conjecture.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open GSTProjectiveOverC

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFinitePointWorldCarrier

variable (N : ℕ) [NeZero N]
-- Lane binder discipline: every declaration below that mentions `N`
-- re-binds `(N : ℕ) [NeZero N]` explicitly at its head (the section
-- variable above is kept per the lane law and shadowed by the explicit
-- binders, so the shipped signatures are fully deterministic).

/-! ### The affine carrier and its smooth structure -/

/-- The finite-point world: the spectrum of `N` copies of the complex
numbers.  An `abbrev` (reducible alias), like `complexBase` and
`ProjectiveGrading` before it: `rw` pattern matching and instance synthesis
run at `.instances` transparency, where a plain `def` is opaque — the
`Γ(finitePointScheme N, ⊤)` / `Γ(Spec (CommRingCat.of (Fin N → ℂ)), ⊤)`
boundary bled five CI errors (run 43767848609, in the arity-12 ancestor)
before this. -/
abbrev finitePointScheme (N : ℕ) [NeZero N] : Scheme :=
  Spec (CommRingCat.of (Fin N → ℂ))

/-- The structure morphism to the complex base, induced by the diagonal
`ℂ -> ℂ^N` (constant families). -/
def finitePointStructureMap (N : ℕ) [NeZero N] :
    finitePointScheme N ⟶ complexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ)))

-- PORT RISK(W42A-SMOOTH-PI): the smooth side condition is pure instance
-- synthesis, exactly as in the ancestor: `Algebra.Etale ℂ ℂ` →
-- `Algebra.Etale ℂ (Fin N → ℂ)` (Etale/Pi.lean, `Finite (Fin N)`) →
-- `Algebra.Smooth ℂ (Fin N → ℂ)` (Etale/Basic.lean:223) →
-- `RingHom.smooth_algebraMap` (RingHom/Smooth.lean:82).  Every link of
-- the chain is arity-uniform in `N` (`Finite (Fin N)` is an instance for
-- every `N`), so `inferInstance` should close it at variable `N` the same
-- way it closed at the ancestor's literal arity.  Designated CI repair
-- point if synthesis ordering differs at the pin: provision the etale
-- step explicitly with `haveI : Algebra.Etale ℂ (Fin N → ℂ) :=
-- inferInstance` and feed the smooth-of-etale instance by hand.
/-- The structure morphism is smooth: `ℂ^N` is a smooth `ℂ`-algebra. -/
theorem finitePoint_smooth (N : ℕ) [NeZero N] :
    Smooth (finitePointStructureMap N) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-! ### The N nodes -/

/-- The N node values: `i |-> i` in `ℂ`, pairwise distinct complex
numbers (the Lagrange interpolation nodes). -/
def nodeValues (N : ℕ) [NeZero N] : Fin N → ℂ := fun i => (i.val : ℂ)

theorem nodeValues_injective (N : ℕ) [NeZero N] :
    Function.Injective (nodeValues N) := by
  intro a b h
  -- `ℂ` is of characteristic zero, so the natural-number cast is injective,
  -- and `Fin.val` is injective.
  have h' : (a.val : ℂ) = (b.val : ℂ) := h
  exact Fin.val_injective (Nat.cast_injective h')
  -- AUDIT: cast bookkeeping; alternates `Fin.val_inj` / `Fin.ext`,
  -- `Nat.cast_inj.mp`.

/-- Distinctness of the nodes on the whole type — the Lagrange side
condition. -/
theorem nodeValues_injOn (N : ℕ) [NeZero N] :
    Set.InjOn (nodeValues N) Set.univ :=
  (nodeValues_injective N).injOn
  -- AUDIT: `Function.Injective.injOn`; avoids the `Set.InjOn` binder-shape
  -- (membership vs subtype form) of the pinned revision.

/-! ### The graded ring, the evaluation, and the global-sections map -/

/-- The standard total-degree grading on `ℂ[X0, X1]`; definitionally equal to
`ProjectiveGrading 1` from the geometry front, so no transport is needed. -/
abbrev grading : ℕ → Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℂ

/-- Ring homomorphism evaluating `ℂ[X0, X1]` at the N nodes:
`X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def evalRingHomN (N : ℕ) [NeZero N] :
    MvPolynomial (Fin 2) ℂ →+* (Fin N → ℂ) :=
  (MvPolynomial.aeval ![nodeValues N, fun _ => 1]).toRingHom

/-- The same evaluation, transported to global sections of the finite-point
scheme via the canonical `Γ(Spec ℂ^N, ⊤) ≅ ℂ^N` isomorphism.

AUDIT: the `Scheme.ΓSpecIso` invocation follows Mathlib Scheme.lean:602
(`(ΓSpecIso R).inv.hom : R →+* Γ(Spec R, ⊤)`); if the pinned revision prefers
the `ΓSpecIso_hom_toSpecZero`-style simp normalization, this def is the place
to adjust. -/
noncomputable def sectionRingHom (N : ℕ) [NeZero N] :
    MvPolynomial (Fin 2) ℂ →+* Γ(finitePointScheme N, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom.comp (evalRingHomN N)

/-- The first coordinate evaluates to the unit: `X1 |-> 1`. -/
private theorem eval_X_one (N : ℕ) [NeZero N] :
    evalRingHomN N (MvPolynomial.X 1) = 1 := by
  show MvPolynomial.aeval ![nodeValues N, fun _ => 1] (MvPolynomial.X 1) = 1
  rw [MvPolynomial.aeval_X]
  -- `![u, v] 1 = v` and `v = (fun _ => 1)` is the pointwise unit.
  -- AUDIT: matrix-notation evaluation; alternate `Matrix.cons_val_one`.
  rfl

/-- Under `sectionRingHom`, the first coordinate is the unit of the global
sections ring. -/
private theorem section_X_one (N : ℕ) [NeZero N] :
    sectionRingHom N (MvPolynomial.X 1) = 1 := by
  -- `sectionRingHom` is `evalRingHomN` followed by the inverse of the
  -- `Γ(Spec ℂ^N, ⊤) ≅ ℂ^N` isomorphism, so it maps `X1 |-> 1 |-> 1`.
  show (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
      (evalRingHomN N (MvPolynomial.X 1)) = 1
  rw [eval_X_one N]
  exact map_one _

/-- The image of the irrelevant ideal under `sectionRingHom` is everything:
`X1` lies in the irrelevant ideal and evaluates to the unit. -/
theorem section_hf (N : ℕ) [NeZero N] :
    (HomogeneousIdeal.irrelevant grading).toIdeal.map (sectionRingHom N) = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  have hmem : sectionRingHom N (MvPolynomial.X 1) ∈
      (HomogeneousIdeal.irrelevant grading).toIdeal.map (sectionRingHom N) :=
    Ideal.mem_map_of_mem (sectionRingHom N)
      (HomogeneousIdeal.mem_irrelevant_of_mem grading zero_lt_one
        (by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_X ℂ 1))
  rw [section_X_one N] at hmem
  exact hmem
  -- AUDIT: the degree side condition is `0 < 1` (`zero_lt_one`); the
  -- membership shape `mem_irrelevant_of_mem` + `mem_homogeneousSubmodule`
  -- follows the pinned ProjectiveSpectrum API.

/-! ### The embedding into the projective line -/

/-- The closed embedding of the finite-point world into the projective line,
from the global sections `X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def finitePointEmbedding (N : ℕ) [NeZero N] :
    finitePointScheme N ⟶ projectiveSpace 1 :=
  Proj.fromOfGlobalSections grading (sectionRingHom N) (section_hf N)

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

/-- Lagrange interpolation through the N distinct nodes: any value
vector on the nodes is realized by a polynomial of degree below `N`. -/
private theorem exists_interpolating (N : ℕ) [NeZero N] (y : Fin N → ℂ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ N - 1 ∧ ∀ i : Fin N,
      q.eval (nodeValues N i) = y i := by
  refine ⟨Lagrange.interpolate (Finset.univ : Finset (Fin N)) (nodeValues N) y, ?_, ?_⟩
  · -- degree < card univ = N, hence ≤ N - 1
    -- PORT NOTE(n12): the ancestor bridged `natDegree ≤ 11` with
    -- `Nat.le_of_lt_succ` on the literal pair `11`/`12`; at variable `N`
    -- both branches are re-derived from the bound `natDegree < N` — the
    -- zero branch stays `rw [h0]; simp` (`0 ≤ _` by `Nat.zero_le`), the
    -- main branch closes by `omega` (truncated subtraction is linear).
    by_cases h0 : Lagrange.interpolate (Finset.univ : Finset (Fin N))
        (nodeValues N) y = 0
    · rw [h0]; simp
    · have h := Lagrange.degree_interpolate_lt y
        (by rw [Finset.coe_univ]; exact nodeValues_injOn N)
      rw [Finset.card_univ, Fintype.card_fin,
        ← Polynomial.natDegree_lt_iff_degree_lt h0] at h
      omega
  · exact fun i => Lagrange.eval_interpolate_at_node y (by
      rw [Finset.coe_univ]; exact nodeValues_injOn N) (Finset.mem_univ i)
  -- AUDIT: Lagrange API (`Mathlib/LinearAlgebra/Lagrange.lean`):
  -- `degree_interpolate_lt` binds `(r) (hvs : Set.InjOn v ↑s)` with `r`
  -- explicit first; the degree-to-natDegree conversion is
  -- `Polynomial.natDegree_lt_iff_degree_lt` (Degree/Defs.lean), with the
  -- zero-polynomial case discharged separately.

/-- Homogeneous lift along the chart `X1 = 1`: a univariate `q` of degree at
most `d` homogenizes to a degree-`d` form whose node-evaluation is `q` at the
nodes. -/
private theorem homogenize_chart_eval (N : ℕ) [NeZero N] (d : ℕ) (q : Polynomial ℂ)
    (hq : q.natDegree ≤ d) :
    ∃ p : MvPolynomial (Fin 2) ℂ,
      p ∈ grading d ∧ evalRingHomN N p = fun i => q.eval (nodeValues N i) := by
  -- PORT NOTE(n12): the ancestor's degree binder `N` is renamed `d` (the
  -- world parameter `N` now leads the binders and would be shadowed); the
  -- body is the ancestor body verbatim under the rename map.
  refine ⟨q.homogenize d, ?_, ?_⟩
  · -- AUDIT: `Polynomial.isHomogeneous_homogenize q` (Homogenize.lean:160)
    -- proves `(q.homogenize N).IsHomogeneous N` unconditionally; membership in
    -- `homogeneousSubmodule` is `IsHomogeneous` by `Iff.rfl`.
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact Polynomial.isHomogeneous_homogenize q
  · -- AUDIT: `Polynomial.aeval_homogenize_of_eq_one (hn) (g) (hg : g 1 = 1)`
    -- (Homogenize.lean:148) transports the Pi-algebra evaluation of the
    -- homogenized form to the univariate `aeval` at `nodeValues`; the
    -- Pi-algebra evaluation is componentwise node evaluation.
    show MvPolynomial.aeval ![nodeValues N, fun _ => 1] (q.homogenize d) =
      fun i => q.eval (nodeValues N i)
    rw [Polynomial.aeval_homogenize_of_eq_one hq
      (![nodeValues N, fun _ => 1] : Fin 2 → (Fin N → ℂ)) rfl]
    funext i
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum]

/-- Lagrange surjectivity core, chart `j = 1` (the section of `X1` is the
unit): every value vector on the N nodes is realized by a homogeneous
form of degree `N - 1`. -/
private theorem chart_core_one (N : ℕ) [NeZero N] (y : Fin N → ℂ) :
    ∃ (d : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading d ∧ ∀ i : Fin N, evalRingHomN N p i = y i := by
  -- PORT NOTE(n12): the degree literal `11` becomes `N - 1`, and the
  -- statement's degree binder `N` is renamed `d` (shadowing the world
  -- parameter); the body is otherwise the ancestor body verbatim.
  obtain ⟨q, hqdeg, hqeval⟩ := exists_interpolating N y
  obtain ⟨p, hp, hpeval⟩ := homogenize_chart_eval N (N - 1) q hqdeg
  exact ⟨N - 1, p, hp, fun i => by rw [hpeval]; exact hqeval i⟩

/-- Lagrange surjectivity core, chart `j = 0` (the section of `X0` is
`nodeValues`): for every value vector `y` and every denominator exponent
`K` there is a homogeneous form `p` of degree `M` with
`p(v i) * (v i)^K = y i * (v i)^M` — the `mk'`-cancellation identity of the
away-localization. -/
private theorem chart_core_zero (N : ℕ) [NeZero N] (y : Fin N → ℂ) (K : ℕ) :
    ∃ (M : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading M ∧ ∀ i : Fin N,
        evalRingHomN N p i * (nodeValues N i)^K = y i * (nodeValues N i)^M := by
  -- PORT NOTE(n12): the ancestor's denominator-exponent binder `N` is
  -- renamed `K` (shadowing the world parameter); the literals `11` /
  -- `N + 11` become `N - 1` / `K + (N - 1)`; the closer gains one explicit
  -- `pow_add` split so `ring` runs on bare power atoms.
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_interpolating N (fun i => y i * (nodeValues N i)^(N - 1))
  obtain ⟨p, hp, hpeval⟩ :=
    homogenize_chart_eval N (K + (N - 1)) q (le_trans hqdeg (by omega))
  refine ⟨K + (N - 1), p, hp, fun i => ?_⟩
  have hval : evalRingHomN N p i = q.eval (nodeValues N i) := by rw [hpeval]
  rw [hval, hqeval i, pow_add]
  -- `y i * a ^ (N - 1) * a ^ K = y i * a ^ (K + (N - 1))`
  ring

/-- The first coordinate evaluates to the node values: `X0 |-> nodeValues`. -/
private theorem eval_X_zero (N : ℕ) [NeZero N] :
    evalRingHomN N (MvPolynomial.X 0) = nodeValues N := by
  show MvPolynomial.aeval ![nodeValues N, fun _ => 1] (MvPolynomial.X 0) = nodeValues N
  rw [MvPolynomial.aeval_X]
  rfl
  -- AUDIT: matrix-notation evaluation at index 0; alternate
  -- `Matrix.cons_val_zero` (mirror of `eval_X_one` above).

/-! ### The closed immersion -/

/-- The submonoid side condition of the localization transport: the powers
of `X j` map into the powers of its section.  Stated standalone so the
definition and the computation below ride the same proof (proof
irrelevance makes the two uses definitionally equal). -/
private theorem chartRingMap_le (N : ℕ) [NeZero N] (j : Fin 2) :
    Submonoid.powers (MvPolynomial.X j) ≤
      (Submonoid.powers (sectionRingHom N (MvPolynomial.X j))).comap
        (sectionRingHom N) := by
  rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]

/-- The ring-level chart map at the variable `X j`: the `IsLocalization.map`
composite inside `Proj.toBasicOpenOfGlobalSections` (pinned
ProjectiveSpectrum/Basic.lean:369-377), from the degree-`0` homogeneous
localization `HomogeneousLocalization.Away grading (MvPolynomial.X j)` (the
`D₊(X j)` chart ring — the domain forced by `basicOpenIsoSpec`'s target) to
the away-localization of its section.  Surjectivity of this ring map is the
Lagrange interpolation core of the embedding. -/
private noncomputable def chartRingMap (N : ℕ) [NeZero N] (j : Fin 2) :
    HomogeneousLocalization.Away grading (MvPolynomial.X j) →+*
      Localization.Away (sectionRingHom N (MvPolynomial.X j)) :=
  RingHom.comp
    (IsLocalization.map
      (R := MvPolynomial (Fin 2) ℂ)
      (S := Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
      (M := Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
      (P := Γ(finitePointScheme N, ⊤))
      (T := Submonoid.powers (sectionRingHom N (MvPolynomial.X j)))
      (Q := Localization.Away (sectionRingHom N (MvPolynomial.X j)))
      (sectionRingHom N) (chartRingMap_le N j))
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
private theorem chartRingMap_apply (N : ℕ) [NeZero N] (j : Fin 2) {d : ℕ}
    (hXj : MvPolynomial.X j ∈ grading d) (k : ℕ)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p ∈ grading (k • d)) :
    chartRingMap N j (HomogeneousLocalization.Away.mk grading hXj k p hp) =
      IsLocalization.mk'
        (M := Submonoid.powers (sectionRingHom N (MvPolynomial.X j)))
        (S := Localization.Away (sectionRingHom N (MvPolynomial.X j)))
        (sectionRingHom N p)
        ⟨sectionRingHom N (MvPolynomial.X j) ^ k,
          (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩⟩ := by
  have h1 : chartRingMap N j (HomogeneousLocalization.Away.mk grading hXj k p hp) =
      (IsLocalization.map
        (R := MvPolynomial (Fin 2) ℂ)
        (S := Localization.Away (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
        (M := Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin 2) ℂ))
        (P := Γ(finitePointScheme N, ⊤))
        (T := Submonoid.powers (sectionRingHom N (MvPolynomial.X j)))
        (Q := Localization.Away (sectionRingHom N (MvPolynomial.X j)))
        (sectionRingHom N) (chartRingMap_le N j))
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
of the finite-point scheme is the transport of a vector. -/
private theorem gammaInv_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom := by
  intro g
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).hom.hom g, ?_⟩
  exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))) g
  -- AUDIT: the X-side round trip of the adjunction iso — the pinned
  -- `Iso.hom_inv_id_apply`, the same transport `Scheme.lean:851` itself
  -- applies to `ΓSpecIso`; the equation direction is direct (no `symm`).

/-- Injectivity of the `ΓSpecIso` inverse transport: a section is determined
by its vector. -/
private theorem gammaInv_injective (N : ℕ) [NeZero N] :
    Function.Injective
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom := by
  have hli : Function.LeftInverse
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom :=
    fun r => Iso.inv_hom_id_apply
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))) r
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
private theorem chartRingMap_surjective (N : ℕ) [NeZero N] (j : Fin 2) :
    Function.Surjective (chartRingMap N j) := by
  -- PORT NOTE(n12): the power exponent obtained from
  -- `Submonoid.mem_powers_iff` below is renamed `k` (the ancestor bound
  -- it as `N`, which now names the world parameter and would be
  -- shadowed); the two chart branches are otherwise the ancestor bodies
  -- verbatim under the rename map.
  -- The fraction decomposition is obtained at GENERIC `j` (no embedded
  -- literal forms), then the two charts are dispatched by `Fin 2`'s
  -- two-element structure.
  intro z
  obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (M := .powers (sectionRingHom N (MvPolynomial.X j))) z
  -- `s` is destructured first so that the power equation's side is a bare
  -- local (`subst` cannot eliminate the coercion `↑s`).
  obtain ⟨t, ht⟩ := s
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ht
  obtain ⟨y', hy'⟩ := gammaInv_surjective N y
  by_cases hj : j = 0
  · subst hj
    -- chart `j = 0`: the cleared Lagrange identity at all N nodes.
    obtain ⟨M, p, hp, hpt⟩ := chart_core_zero N y' k
    have hXj : MvPolynomial.X 0 ∈ grading 1 := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X ℂ 0
    have hpnsm : p ∈ grading (M • 1) := by rwa [nsmul_one]
    -- the vector identity, one node-value higher than `hpt`
    have hvec : evalRingHomN N p * nodeValues N ^ (k + 1) =
        y' * nodeValues N ^ (M + 1) := by
      funext i
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [pow_succ, ← mul_assoc, pow_succ, ← mul_assoc, hpt i]
    -- the section-level identity (the `ΓSpecIso` transport)
    have hΓ : sectionRingHom N p * sectionRingHom N (MvPolynomial.X 0) ^ (k + 1) =
        y * sectionRingHom N (MvPolynomial.X 0) ^ (M + 1) := by
      have e1 : sectionRingHom N p =
          (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
            (evalRingHomN N p) := rfl
      have e2 : sectionRingHom N (MvPolynomial.X 0) =
          (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
            (evalRingHomN N (MvPolynomial.X 0)) := rfl
      rw [e1, e2, eval_X_zero N, ← map_pow, ← map_mul, ← hy', ← map_pow, ← map_mul]
      exact congrArg _ hvec
    refine ⟨HomogeneousLocalization.Away.mk grading hXj M p hpnsm, ?_⟩
    rw [chartRingMap_apply]
    refine (IsLocalization.mk'_eq_iff_eq'
      (S := Localization.Away (sectionRingHom N (MvPolynomial.X 0)))
      (M := Submonoid.powers (sectionRingHom N (MvPolynomial.X 0)))).mpr ?_
    simp only [Subtype.coe_mk]
    refine (IsLocalization.eq_iff_exists
      (M := Submonoid.powers (sectionRingHom N (MvPolynomial.X 0)))
      (S := Localization.Away (sectionRingHom N (MvPolynomial.X 0)))
      (x := sectionRingHom N p * sectionRingHom N (MvPolynomial.X 0) ^ k)
      (y := y * sectionRingHom N (MvPolynomial.X 0) ^ M)).mpr
      ⟨⟨sectionRingHom N (MvPolynomial.X 0),
        Submonoid.mem_powers _⟩, ?_⟩
    simp only [Subtype.coe_mk]
    rw [show sectionRingHom N (MvPolynomial.X 0) * (sectionRingHom N p *
        sectionRingHom N (MvPolynomial.X 0) ^ k) =
      sectionRingHom N p * sectionRingHom N (MvPolynomial.X 0) ^ (k + 1) from by ring,
      show sectionRingHom N (MvPolynomial.X 0) * (y *
        sectionRingHom N (MvPolynomial.X 0) ^ M) =
      y * sectionRingHom N (MvPolynomial.X 0) ^ (M + 1) from by ring]
    exact hΓ
  · have hj1 : j = 1 := Fin.ext (by
      have h := j.isLt
      have hne : j.val ≠ 0 := fun h0 => hj (Fin.ext h0)
      omega)
    subst hj1
    -- chart `j = 1`: the section of `X₁` is the unit.
    obtain ⟨M, p, hp, hpeval⟩ := chart_core_one N y'
    have hXj : MvPolynomial.X 1 ∈ grading 1 := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X ℂ 1
    have hpnsm : p ∈ grading (M • 1) := by rwa [nsmul_one]
    have hΓ : sectionRingHom N p = y := by
      show (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
          (evalRingHomN N p) = y
      rw [← hy']
      exact congrArg _ (funext hpeval)
    refine ⟨HomogeneousLocalization.Away.mk grading hXj M p hpnsm, ?_⟩
    rw [chartRingMap_apply]
    refine (IsLocalization.mk'_eq_iff_eq'
      (S := Localization.Away (sectionRingHom N (MvPolynomial.X 1)))
      (M := Submonoid.powers (sectionRingHom N (MvPolynomial.X 1)))).mpr ?_
    simp only [Subtype.coe_mk]
    refine (IsLocalization.eq_iff_exists
      (M := Submonoid.powers (sectionRingHom N (MvPolynomial.X 1)))
      (S := Localization.Away (sectionRingHom N (MvPolynomial.X 1)))
      (x := sectionRingHom N p * sectionRingHom N (MvPolynomial.X 1) ^ k)
      (y := y * sectionRingHom N (MvPolynomial.X 1) ^ M)).mpr
      ⟨⟨sectionRingHom N (MvPolynomial.X 1),
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
finite-point embedding is a closed immersion, because the chart ring map is
Lagrange-surjective. -/
private theorem chart_closed (N : ℕ) [NeZero N] (j : Fin 2) :
    IsClosedImmersion
      (finitePointEmbedding N ∣_ Proj.basicOpen grading (MvPolynomial.X j)) := by
  have hXj : MvPolynomial.X j ∈ grading 1 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℂ j
  -- STAGE 0-1: retype the restricted embedding at `Proj grading` (the
  -- `projectiveSpace 1` wrapper is defeq but not reducible), then unfold
  -- the embedding to the `fromOfGlobalSections` head.
  rw [show (finitePointEmbedding N ∣_ Proj.basicOpen grading (MvPolynomial.X j)) =
    (Proj.fromOfGlobalSections grading (sectionRingHom N) (section_hf N) ∣_
      (Proj.basicOpen grading (MvPolynomial.X j))) from rfl]
  -- STAGE 1: the restriction rewrite
  -- (`Proj.fromOfGlobalSections_morphismRestrict`, Basic.lean:496)
  -- factorizes the restricted embedding through the affine chart map.
  rw [Proj.fromOfGlobalSections_morphismRestrict grading (sectionRingHom N)
      (section_hf N) zero_lt_one hXj]
  -- STAGE 2: unfold the chart composite (the pinned definition of
  -- `toBasicOpenOfGlobalSections`, Basic.lean:369): the goal becomes the
  -- isomorphism chunk on the left, the `Spec` of the chart ring map in the
  -- middle, and the target `basicOpenIsoSpec` isomorphism (inverted) on the
  -- right.  The chart ring map inside is *definitionally* `chartRingMap N j`
  -- (transcribed verbatim in its definition above).
  simp only [Proj.toBasicOpenOfGlobalSections]
  -- STAGE 3-4: left-associate the composite, cancel the right target
  -- isomorphism (`basicOpenIsoSpec` inverted — the affine chart of the
  -- projective target), re-associate, and cancel the left isomorphism
  -- factors one at a time — the
  -- `Scheme.isoOfEq` hom of the morphismRestrict factorization, the
  -- `Scheme.isoOfEq` inv of the chart-source transport, the restriction of
  -- the affine `toSpecΓ` (`IsIso (f ∣_ U)` for `IsIso f`, Restrict.lean:639
  -- the finite-point scheme is affine), and `basicOpenIsoSpecAway`
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
    ((Scheme.isoOfEq (finitePointScheme N)
      (Proj.fromOfGlobalSections_preimage_basicOpen grading (sectionRingHom N)
        (section_hf N) zero_lt_one hXj)).hom) _).mpr ?_
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    ((Scheme.isoOfEq (finitePointScheme N)
      (Scheme.toSpecΓ_preimage_basicOpen (finitePointScheme N)
        (sectionRingHom N (MvPolynomial.X j)))).inv) _).mpr ?_
  -- STAGE 5: the next left factor is `toSpecΓ ∣_ D(section)`, the
  -- restriction of the affine `toSpecΓ`; its `IsIso` side condition is the
  -- restriction instance (`instance (f) [IsIso f] (U) : IsIso (f ∣_ U)`,
  -- Restrict.lean:639) fed by `IsAffine.affine`
  -- (AffineScheme.lean:59).  Instance synthesis cannot find it through the
  -- def-alias alone: the chain is supplied explicitly; this is independent
  -- of the alias's reducibility.
  haveI haff : IsAffine (finitePointScheme N) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Fin N → ℂ))))
  haveI hΓ : IsIso (finitePointScheme N).toSpecΓ :=
    @IsAffine.affine (finitePointScheme N) haff
  haveI hΓU : IsIso ((finitePointScheme N).toSpecΓ ∣_
      PrimeSpectrum.basicOpen (sectionRingHom N (MvPolynomial.X j))) := by
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
    (CommRingCat.ofHom (chartRingMap N j)) (chartRingMap_surjective N j)

/-- **The finite-point embedding is a closed immersion.** -/
theorem finitePoint_closedImmersion (N : ℕ) [NeZero N] :
    IsClosedImmersion (finitePointEmbedding N) :=
  IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion)
    (fun j => Proj.basicOpen grading (MvPolynomial.X j))
    (Proj.iSup_basicOpen_eq_top' grading MvPolynomial.X
      variables_homogeneous span_cover)
    (fun j => chart_closed N j)
  -- AUDIT: `IsZariskiLocalAtTarget` is a root-namespace abbreviation
  -- (Morphisms/Basic.lean); the cover family is normalized to `MvPolynomial.X`,
  -- matching `Proj.iSup_basicOpen_eq_top'` (ProjectiveSpectrum/Basic.lean),
  -- whose adjoin side condition is `span_cover` above.

/-- The embedding commutes with the structure maps over `Spec(ℂ)`. -/
theorem finitePoint_over_base (N : ℕ) [NeZero N] :
    finitePointEmbedding N ≫ projectiveSpaceToBase 1 =
      finitePointStructureMap N := by
  -- STAGE 1 (definitional): retype the whole composite at `Proj grading` —
  -- the `projectiveSpace 1` wrapper is defeq but not reducible, so the
  -- regrouping below must operate on the `Proj`-typed form; unfold the
  -- embedding and the base map in one definitional step.
  rw [show (finitePointEmbedding N ≫ projectiveSpaceToBase 1 :
      finitePointScheme N ⟶ complexBase) =
      (Proj.fromOfGlobalSections grading (sectionRingHom N) (section_hf N) ≫
        Proj.toSpecZero (ProjectiveGrading 1)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (ProjectiveGrading 1 0))) from rfl]
  -- STAGE 2 (the triangle identity, Basic.lean:515):
  -- `fromOfGlobalSections ≫ toSpecZero` is the `toSpecΓ` composite of the
  -- degree-zero part of `sectionRingHom`.  AUDIT: exact rewrite shape.
  rw [Proj.fromOfGlobalSections_toSpecZero]
  -- STAGE 3: constants stay constant through the degree-zero transport.
  -- The pinned lemma `fromOfGlobalSections_toSpecZero` produces the
  -- composite with the DEGREE-ZERO algebra map `A₀ → A` (not the constants
  -- `ℂ → A`), so the ring identity is stated for the doubly-embedded
  -- constant and bridged by `IsScalarTower` (the definitional route is
  -- tried first).
  have hconst : ∀ c : ℂ,
      evalRingHomN N (algebraMap ℂ (MvPolynomial (Fin 2) ℂ) c) =
        (algebraMap ℂ (Fin N → ℂ) c) :=
    fun c => (MvPolynomial.aeval ![nodeValues N, fun _ => 1]).commutes c
  have hzero : ∀ c : ℂ,
      evalRingHomN N ((algebraMap ↥(ProjectiveGrading 1 0)
          (MvPolynomial (Fin 2) ℂ))
          ((algebraMap ℂ ↥(ProjectiveGrading 1 0)) c)) =
        (algebraMap ℂ (Fin N → ℂ) c) := by
    intro c
    first
    | exact hconst c
    | (rw [IsScalarTower.algebraMap_apply]; exact hconst c)
    | (simp only [IsScalarTower.algebraMap_apply]; exact hconst c)
    | simp
  have hcomp : ((sectionRingHom N).comp (algebraMap ↥(ProjectiveGrading 1 0)
        (MvPolynomial (Fin 2) ℂ))).comp
      (algebraMap ℂ ↥(ProjectiveGrading 1 0)) =
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom.comp
        (algebraMap ℂ (Fin N → ℂ)) := by
    ext c
    show (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
        (evalRingHomN N ((algebraMap ↥(ProjectiveGrading 1 0)
          (MvPolynomial (Fin 2) ℂ))
          ((algebraMap ℂ ↥(ProjectiveGrading 1 0)) c))) =
      (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv.hom
        (algebraMap ℂ (Fin N → ℂ) c)
    rw [hzero c]
  -- STAGE 4: merge the two spectral factors into the single transported
  -- map, then cancel the adjunction inverse by the unit triangle
  -- `toSpecΓ ≫ Spec.map (ΓSpecIso _).inv = 𝟙`
  -- (GammaSpecAdjunction.lean:487-490).  AUDIT: every rewrite operates at
  -- the raw ring / `Spec (of ℂ^N)` level (`ofHom`-composites split by
  -- `CommRingCat.ofHom_comp`, `Spec.map_comp`); the `finitePointScheme N`
  -- alias is bridged exactly once by the `show` below (pure defeq), never
  -- by cross-level syntactic matching inside a rewrite.
  rw [CategoryTheory.Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [hcomp]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  show (Spec (CommRingCat.of (Fin N → ℂ))).toSpecΓ ≫
      (Spec.map (Scheme.ΓSpecIso (CommRingCat.of (Fin N → ℂ))).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin N → ℂ)))
  rw [← CategoryTheory.Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of (Fin N → ℂ)),
    CategoryTheory.Category.id_comp]

/-! ### The world -/

/-- **THE FINITE-POINT WORLD.**  The affine finite-point scheme with its
smooth structure morphism and its closed projective embedding into `P^1`,
packaged as a `SmoothProjectiveComplexScheme`. -/
noncomputable def finitePointWorld (N : ℕ) [NeZero N] :
    SmoothProjectiveComplexScheme :=
  ⟨finitePointScheme N, finitePointStructureMap N, finitePoint_smooth N,
    ⟨1, finitePointEmbedding N, finitePoint_closedImmersion N,
      finitePoint_over_base N⟩⟩

/-! ### The N points -/

-- PORT RISK(W42A-ARTINIAN-PI): the coheight-zero argument takes
-- `IsArtinianRing (Fin N → ℂ)` by instance synthesis, exactly as the
-- ancestor took the artinian structure of the 12-fold product.  The
-- artinian Pi chain of the pin (field factors over a finite index type) is
-- arity-uniform in `N`, so it should fire at variable `N`; the designated
-- CI repair point, should the pin's synthesis route differ, is to provision
-- the artinian structure explicitly (`haveI` with the finite-dimensional
-- product decomposition) before `IsArtinianRing.isPrime_iff_isMaximal`.
/-- Every point of the finite-point scheme is closed (maximal in the
specialization order): all primes of the artinian ring `ℂ^N` are maximal. -/
theorem finitePoint_coheight (N : ℕ) [NeZero N] (x : finitePointScheme N) :
    Order.coheight x = 0 := by
  -- `ℂ^N` is artinian: each factor is artinian and the finite `Pi` type is
  -- artinian by instance synthesis (the `haveI` below did not error in CI,
  -- in the ancestor).
  haveI hart : IsArtinianRing (Fin N → ℂ) := inferInstance
  refine Order.coheight_eq_zero.mpr (fun y hle => ?_)
  -- `hle : x ≤ y` in the scheme specialization order is `y ⤳ x` topologically
  -- (`Scheme.le_iff_specializes : a ≤ b ↔ b ⤳ a`); on the affine spectrum
  -- this is reverse ideal inclusion, bridged through `PrimeSpectrum`.
  have hsp : y ⤳ x := Scheme.le_iff_specializes.mp hle
  have hle' : (show PrimeSpectrum (Fin N → ℂ) from y).asIdeal ≤
      (show PrimeSpectrum (Fin N → ℂ) from x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr hsp
  -- both point ideals are prime, hence maximal in the artinian ring; a
  -- maximal ideal below another maximal ideal is equal to it.
  have hyi : (show PrimeSpectrum (Fin N → ℂ) from y).asIdeal.IsPrime :=
    (show PrimeSpectrum (Fin N → ℂ) from y).isPrime
  have hxi : (show PrimeSpectrum (Fin N → ℂ) from x).asIdeal.IsPrime :=
    (show PrimeSpectrum (Fin N → ℂ) from x).isPrime
  have hymax : (show PrimeSpectrum (Fin N → ℂ) from y).asIdeal.IsMaximal :=
    (IsArtinianRing.isPrime_iff_isMaximal _).mp hyi
  have heq : (show PrimeSpectrum (Fin N → ℂ) from y).asIdeal =
      (show PrimeSpectrum (Fin N → ℂ) from x).asIdeal :=
    hymax.eq_of_le (Ideal.IsPrime.ne_top hxi) hle'
  -- the points are equal, so `y ≤ x` holds by reflexivity (the `rw` closes
  -- the goal through `le_refl`).
  rw [show y = x from PrimeSpectrum.ext heq]
  -- AUDIT: the order bridge is `Scheme.le_iff_specializes` (Scheme.lean,
  -- `a ≤ b ↔ b ⤳ a`) and `PrimeSpectrum.le_iff_specializes` (`x ≤ y ↔ x ⤳ y`,
  -- the inclusion order); the artinian step is
  -- `IsArtinianRing.isPrime_iff_isMaximal` (Artinian/Module.lean); the
  -- scheme-point and prime-spectrum carriers are definitionally identified.

/-- The N points of the world, indexed by `Fin N`.  The prime spectrum
of a finite product is the sigma of the factor spectra; each
`PrimeSpectrum ℂ` is uniquely inhabited; and all points of the finite-point
scheme have coheight zero, so the coheight-zero subtype is the whole
space. -/
noncomputable def finitePointEquiv (N : ℕ) [NeZero N] :
    Fin N ≃ {x : finitePointScheme N // Order.coheight x = 0} :=
  ((Equiv.sigmaUnique (Fin N) (fun _ => PrimeSpectrum ℂ)).symm.trans
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : Fin N => ℂ)).toEquiv).trans
      (Equiv.subtypeUnivEquiv (fun p => finitePoint_coheight N p)).symm
  -- AUDIT: the `Equiv.cast`-level transport of the definitional
  -- identification `↥(Spec (of (Fin N → ℂ))) = PrimeSpectrum (Fin N → ℂ)`
  -- (`Spec_carrier`); the subtype predicates coincide because the
  -- scheme-point order and the prime-spectrum order are definitionally the
  -- same instance.

/-- Compactness: the finite-point scheme is an affine spectrum, hence
compact.  (Stated as a *named* instance so that both the instance path and
the contracted name `finitePointCompactSpace` are available downstream.) -/
noncomputable instance finitePointCompactSpace (N : ℕ) [NeZero N] :
    CompactSpace ↥(finitePointScheme N) :=
  PrimeSpectrum.compactSpace
  -- AUDIT: definitional transport `↥(finitePointScheme N) = ↥(PrimeSpectrum
  -- (Fin N → ℂ))`; the pinned `PrimeSpectrum.compactSpace` is an instance
  -- with the ring implicit — no explicit argument.

/-! ### Receipts -/

#check finitePointScheme
#check finitePointStructureMap
#check finitePoint_smooth
#check nodeValues
#check nodeValues_injective
#check nodeValues_injOn
#check grading
#check evalRingHomN
#check sectionRingHom
#check section_hf
#check finitePointEmbedding
#check span_cover
#check finitePoint_closedImmersion
#check finitePoint_over_base
#check finitePointWorld
#check finitePoint_coheight
#check finitePointEquiv
#check finitePointCompactSpace

#print axioms finitePoint_smooth
#print axioms section_hf
#print axioms span_cover
#print axioms finitePoint_closedImmersion
#print axioms finitePoint_over_base
#print axioms finitePoint_coheight
#print axioms finitePointWorld

end GSTFinitePointWorldCarrier

/-! DRAFT STATUS: ported 33/33 declarations; 5 PORT NOTEs; 2 PORT RISKs -/
