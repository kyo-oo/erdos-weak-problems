import Mathlib
import HCUniverse2.GSTGeometricRealizationStage2F
import HCUniverse2.GSTSphereUnionComponents

/-!
# GST SINGULAR COHOMOLOGY MAPS (Wave 57) — the generalized pullback calculus

THE CORPUS-MATHS MODULE of the sphere-machine campaign.  The corpus's own
functoriality recipe (`GSTClassicalHodgeSingularCohomologyFunctoriality.lean`,
CI-green) constructs the induced pullback on `RationalSingularCohomology`
for analytic ENDOMORPHISMS of one analytification.  This module generalizes
the same three-step recipe (chain map ⟶ linear-Yoneda dual ⟶ homology map)
to ARBITRARY continuous maps between ARBITRARY topological spaces, adds the
degree-two face interface shared by the winding machine and the sphere
cycle, and specializes everything to the sphere-union legs of the planned
finite-line world (inclusion / collapse / M-cycle permutation, with the
restriction-section calculus on cohomology).

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTSphereUnionComponents

namespace GSTSingularCohomologyMaps

/-! ## §1 The raw-space singular (co)chain complexes -/

/-- The genuine rational singular chain complex of a raw topological space
(the corpus's `rationalSingularChains`, lifted off the analytification
carrier). -/
noncomputable def singularChainsOf (X : TopCat) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj X

/-- The rational singular chains of an analytification's space ARE the
corpus's `rationalSingularChains` (the same construction, `rfl`). -/
theorem singularChainsOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    singularChainsOf A.space = rationalSingularChains A := rfl

/-- The genuine rational singular cochain complex (the linear-Yoneda dual of
the chain complex — the corpus's `rationalSingularCochains` construction). -/
noncomputable def singularCochainsOf (X : TopCat) : CochainComplex (ModuleCat ℚ) ℕ :=
  (singularChainsOf X).linearYonedaObj ℚ rationalCoefficient

/-- The cochain complexes agree with the corpus's (`rfl`). -/
theorem singularCochainsOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    singularCochainsOf A.space = rationalSingularCochains A := rfl

/-- The n-th rational singular cohomology object of a raw space. -/
noncomputable def singularCohomologyObjOf (X : TopCat) (n : ℕ) : ModuleCat ℚ :=
  (singularCochainsOf X).homology n

/-- The underlying type of the n-th rational singular cohomology. -/
abbrev singularCohomologyOf (X : TopCat) (n : ℕ) : Type :=
  singularCohomologyObjOf X n

instance (X : TopCat) (n : ℕ) :
    AddCommGroup (singularCohomologyOf X n) :=
  inferInstance

instance (X : TopCat) (n : ℕ) :
    Module ℚ (singularCohomologyOf X n) :=
  inferInstance

/-- The cohomology of an analytification's space IS the corpus's
`RationalSingularCohomology` (`rfl` — the same homology object). -/
theorem singularCohomologyOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : ℕ) :
    (singularCohomologyOf A.space n) = RationalSingularCohomology A n := rfl

/-! ## §2 The induced maps of an arbitrary continuous map -/

/-- The covariant singular-chain map of a continuous map (the functor's
action — the corpus's `singularChainMap`, generalized off the
endomorphism shape). -/
noncomputable def chainMapOf {X Y : TopCat} (f : X ⟶ Y) :
    singularChainsOf X ⟶ singularChainsOf Y :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map f

theorem chainMapOf_id (X : TopCat) :
    chainMapOf (𝟙 X) = 𝟙 (singularChainsOf X) := by
  simp [chainMapOf, singularChainsOf]

theorem chainMapOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMapOf (f ≫ g) = chainMapOf f ≫ chainMapOf g := by
  unfold chainMapOf singularChainsOf
  -- WAVE 57.5: the pin's `Functor.map_comp` takes the FUNCTOR as an
  -- explicit leading argument (run 44595996727: f was consumed into the
  -- `C ⥤ D` slot); the underscore lets the goal's own functor unify.
  exact Functor.map_comp _ f g

/-- The contravariant singular-cochain map: the linear-Yoneda dual of the
chain map (the corpus's `singularCochainPullback` expression, verbatim,
generalized to distinct spaces). -/
noncomputable def cochainPullbackOf {X Y : TopCat} (f : X ⟶ Y) :
    singularCochainsOf Y ⟶ singularCochainsOf X := by
  unfold singularCochainsOf singularChainsOf
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (chainMapOf f)))

theorem cochainPullbackOf_id (X : TopCat) :
    cochainPullbackOf (𝟙 X) = 𝟙 (singularCochainsOf X) := by
  simp [cochainPullbackOf, chainMapOf_id]
  rfl

theorem cochainPullbackOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cochainPullbackOf (f ≫ g) = cochainPullbackOf g ≫ cochainPullbackOf f := by
  simp [cochainPullbackOf, chainMapOf_comp]
  rfl

/-- The induced map on the genuine rational singular cohomology objects. -/
noncomputable def cohomologyPullbackObjOf {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyObjOf Y n ⟶ singularCohomologyObjOf X n :=
  HomologicalComplex.homologyMap (cochainPullbackOf f) n

/-- The induced pullback on rational singular cohomology, as a rational
linear map. -/
noncomputable def cohomologyPullbackOf {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyOf Y n →ₗ[ℚ] singularCohomologyOf X n :=
  (cohomologyPullbackObjOf f n).hom

/-- Contravariant functoriality on cohomology (the corpus's green proof,
ported; NOTE the order: category composition `f ≫ g` acts on functions as
`g ∘ f`, so the induced linear maps compose `f* ∘ g*`). -/
theorem cohomologyPullbackOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    cohomologyPullbackOf (f ≫ g) n =
      (cohomologyPullbackOf f n).comp (cohomologyPullbackOf g n) := by
  ext x
  unfold cohomologyPullbackOf cohomologyPullbackObjOf
  have hcochain :
    cochainPullbackOf (f ≫ g) =
      (cochainPullbackOf g) ≫ (cochainPullbackOf f) :=
    cochainPullbackOf_comp f g
  have hcomp :
    HomologicalComplex.homologyMap (cochainPullbackOf (f ≫ g)) n =
      (HomologicalComplex.homologyMap (cochainPullbackOf g) n) ≫
        (HomologicalComplex.homologyMap (cochainPullbackOf f) n) := by
    rw [hcochain, HomologicalComplex.homologyMap_comp]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (cochainPullbackOf (f ≫ g)) n)) x =
    ((ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cochainPullbackOf f) n)).comp
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cochainPullbackOf g) n))) x
  rw [hcomp]
  simp

/-- The identity acts identically (the corpus's green proof, verbatim
port). -/
theorem cohomologyPullbackOf_id (X : TopCat) (n : ℕ) :
    cohomologyPullbackOf (𝟙 X) n = LinearMap.id := by
  ext x
  unfold cohomologyPullbackOf cohomologyPullbackObjOf
  have hcochain :
    cochainPullbackOf (𝟙 X) = 𝟙 (singularCochainsOf X) :=
    cochainPullbackOf_id X
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (cochainPullbackOf (𝟙 X)) n)) x =
    LinearMap.id x
  rw [hcochain, HomologicalComplex.homologyMap_id]
  simp
  rfl

/-! ## §3 The degree-two face interface -/

/-- The standard topological 2-simplex model (the pinned `stdSimplex`). -/
abbrev StdTwoSimplex : Type :=
  stdSimplex ℝ (Fin 3)

/-- The standard topological 1-simplex model. -/
abbrev StdOneSimplex : Type :=
  stdSimplex ℝ (Fin 2)

/-- The k-th coface between the concrete simplex models: the pinned
fiber-sum map `stdSimplex.map` of the skip-injection `k.succAbove`
(`Fin 2 → Fin 3`), with its pinned continuity proof
`stdSimplex.continuous_map` (a LEMMA supplying `Continuous (map f)`, not a
map itself — the wave-57.3 type mismatch, root-caused).  This is exactly
the coface of the pinned `TopCat.toSSetObjEquiv_δ_apply` face formula. -/
def stdFace (k : Fin 3) : C(StdOneSimplex, StdTwoSimplex) :=
  ⟨stdSimplex.map (Fin.succAbove k),
    stdSimplex.continuous_map (Fin.succAbove k)⟩

/-- The injection of a concrete 2-simplex map into the singular set (the
pinned `toSSetObjEquiv`, reversed). -/
def twoSimplexInject {X : TopCat} (σ : C(StdTwoSimplex, X)) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 2)) :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 2))).symm σ

/-- AUDIT(FACE-NAT): **THE DEGREE-TWO FACE FORMULA.**  The k-th face of an
injected 2-simplex, read through the pinned `toSSetObjEquiv`, is the
precomposition of the simplex map with the affine coface `stdFace k`.

The proof is the pinned `TopCat.toSSetObjEquiv_δ_apply` (itself `rfl` at
the pin) composed with the equiv roundtrip, bridged by `calc` so every
step elaborates at definitional equality (the `dsimp%`-marked pinned
statement never passes through `rw`). -/
theorem toSSetObj₂_face {X : TopCat} (σ : C(StdTwoSimplex, X)) (k : Fin 3)
    (z : StdOneSimplex) :
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))
        ((TopCat.toSSet.obj X).δ k (twoSimplexInject σ)) z =
      σ (stdFace k z) := by
  have h1 := TopCat.toSSetObjEquiv_δ_apply (X := X) (n := 1)
    (twoSimplexInject σ) k z
  have h2 : X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
      (twoSimplexInject σ)
      (stdSimplex.map (Fin.succAbove k) z) = σ (stdFace k z) := by
    show X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 2))).symm σ)
        (stdSimplex.map (Fin.succAbove k) z) = σ (stdFace k z)
    rw [(TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply]
    rfl
  calc X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))
        ((TopCat.toSSet.obj X).δ k (twoSimplexInject σ)) z
        = X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2)) (twoSimplexInject σ)
          (stdSimplex.map (Fin.succAbove k) z) := h1
    _ = σ (stdFace k z) := h2

/-! ## §4 The sphere-union leg maps -/

section Legs

variable (M : ℕ)

/-- The cyclic successor on `Fin M` (the M-cycle's index map). -/
def cyclicSucc (k : Fin M) : Fin M :=
  ⟨(k.val + 1) % M,
    Nat.mod_lt (k.val + 1)
      (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩

/-- The base point of the 2-sphere (the corpus's own nonempty-sphere point
of the green sphere-union file — any point serves the constant filler of
the collapse). -/
def sphereBase : unitSphereType :=
  unitSphere_nonempty.some

theorem sphereCollapse_continuous (M : ℕ) (i : Fin M) :
    Continuous (fun z : sphereUnionSpace M =>
      if z.1 = i then z.2 else sphereBase) := by
  refine ⟨fun U hU => ?_⟩
  rw [isOpen_sigma_iff]
  intro j
  -- WAVE 57.5 (run 44595996727): the pinned `isOpen_sigma_iff`'s RHS is
  -- PREIMAGE-spelled (`IsOpen (Sigma.mk j ⁻¹' s)`), the wave-57.4 setOf
  -- spelling could never rw-match it; `Set.mem_setOfEq` does not exist at
  -- the pin; and the ite-over-`sphereBase ∈ U` demanded a Classical
  -- decidability the bare statement cannot supply — the branch is split
  -- into two classically-free hset shapes, each closed by plain `simp`
  -- (which reduces the Fin-decidable `j = j` propositionally, the
  -- transparency the 57.4 `show` could not bridge).
  by_cases hj : j = i
  · subst hj
    have hset : Sigma.mk (β := fun _ : Fin M => unitSphereType) j ⁻¹'
        ((fun z : sphereUnionSpace M =>
            if z.1 = j then z.2 else sphereBase) ⁻¹' U) = U := by
      ext a
      simp
    rw [hset]
    exact hU
  · by_cases hb : sphereBase ∈ U
    · have hset : Sigma.mk (β := fun _ : Fin M => unitSphereType) j ⁻¹'
          ((fun z : sphereUnionSpace M =>
            if z.1 = i then z.2 else sphereBase) ⁻¹' U) = Set.univ := by
        ext a
        simp [hj, hb]
      rw [hset]
      exact isOpen_univ
    · have hset : Sigma.mk (β := fun _ : Fin M => unitSphereType) j ⁻¹'
          ((fun z : sphereUnionSpace M =>
            if z.1 = i then z.2 else sphereBase) ⁻¹' U) = ∅ := by
        ext a
        simp [hj, hb]
      rw [hset]
      exact isOpen_empty

/-- The inclusion of the i-th sphere slice (the green sphere file's
Continuous-STRUCTURE constructor route with the pinned
`isOpen_sigma_iff`). -/
def sphereIncl (i : Fin M) :
    TopCat.of unitSphereType ⟶ TopCat.of (sphereUnionSpace M) :=
  TopCat.ofHom
    ⟨fun x => Sigma.mk (β := fun _ : Fin M => unitSphereType) i x, by
      refine ⟨fun U hU => ?_⟩
      exact isOpen_sigma_iff.mp hU i⟩

/-- AUDIT(COLLAPSE-CONT): the collapse of the union onto the i-th slice
(identity there, constant filler elsewhere; the constant family makes the
second component's type index-independent — no transport needed). -/
def sphereCollapse (i : Fin M) :
    TopCat.of (sphereUnionSpace M) ⟶ TopCat.of unitSphereType :=
  TopCat.ofHom
    ⟨fun z => if z.1 = i then z.2 else sphereBase,
      sphereCollapse_continuous M i⟩

/-- The M-cycle permutation of the slices.  Continuity by the pinned
`isOpen_sigma_iff`: the preimage's j-component is the (cyclicSucc j)-slice
of the target, open by the pinned `isOpen_sigma_iff.mp`. -/
def sphereCycle :
    TopCat.of (sphereUnionSpace M) ⟶ TopCat.of (sphereUnionSpace M) :=
  TopCat.ofHom
    ⟨fun z => Sigma.mk (β := fun _ : Fin M => unitSphereType)
      (cyclicSucc M z.1) z.2, by
      refine ⟨fun U hU => ?_⟩
      rw [isOpen_sigma_iff]
      intro j
      exact isOpen_sigma_iff.mp hU (cyclicSucc M j)⟩

/-! ## §5 The leg identities -/

/-- The collapse is a left inverse of the inclusion on the slice.
WAVE 57.4: the pinned `TopCat.ext` (the POINTWISE extensionality lemma,
`Mathlib/Topology/Category/TopCat/Basic.lean:129`); `TopCat.hom_ext`
takes a `.hom`-equality (Basic.lean:125) and is the WRONG lemma here —
after `apply TopCat.ext` the goal is `∀ x, … x = … x`, so the binder
intro is `intro`, not `funext` (the wave-57.3 misdiagnosis, root-caused
against the pin). -/
theorem incl_comp_collapse (i : Fin M) :
    sphereIncl M i ≫ sphereCollapse M i = 𝟙 (TopCat.of unitSphereType) := by
  apply TopCat.ext
  intro x
  show (if (Sigma.mk (β := fun _ : Fin M => unitSphereType) i x).1 = i
      then (Sigma.mk (β := fun _ : Fin M => unitSphereType) i x).2
      else sphereBase) = x
  have hone : (Sigma.mk (β := fun _ : Fin M => unitSphereType) i x).1 = i :=
    rfl
  rw [if_pos hone]

/-- The M-cycle permutes the slices. -/
theorem cycle_comp_incl (j : Fin M) :
    sphereIncl M j ≫ sphereCycle M =
      sphereIncl M (cyclicSucc M j) := by
  apply TopCat.ext
  intro x
  rfl

/-! ## §6 The cohomology-level leg calculus -/

/-- **THE RESTRICTION-SECTION CALCULUS.**  On rational singular cohomology,
the restriction to the i-th slice followed by the collapse-pullback is the
identity: the collapse-pullback is a SECTION of the slice restriction.  Once
the honest sphere class exists, this is the mechanism that extends it to
the union. -/
theorem incl_collapse_section (i : Fin M) (n : ℕ) :
    (cohomologyPullbackOf (sphereIncl M i) n).comp
      (cohomologyPullbackOf (sphereCollapse M i) n) = LinearMap.id := by
  rw [← cohomologyPullbackOf_comp (sphereIncl M i) (sphereCollapse M i) n,
    incl_comp_collapse M i, cohomologyPullbackOf_id]

/-- **THE CYCLIC PERMUTATION ACTION ON SLICE RESTRICTIONS.**  Pulling back
along the M-cycle and then restricting to slice j equals restricting to
slice (cyclicSucc j). -/
theorem cycle_incl_calculus (j : Fin M) (n : ℕ) :
    (cohomologyPullbackOf (sphereIncl M j) n).comp
      (cohomologyPullbackOf (sphereCycle M) n) =
        cohomologyPullbackOf (sphereIncl M (cyclicSucc M j)) n := by
  rw [← cohomologyPullbackOf_comp (sphereIncl M j) (sphereCycle M) n,
    cycle_comp_incl M j]

end Legs

end GSTSingularCohomologyMaps
