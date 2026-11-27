/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# The component H⁰ machine (Wave 46, repair waves 47.x) — the positive-dimensional beachhead

THE CUSTOM TOOL.  The wave-44/45 frontier map established the wall: at the
pinned Mathlib (v4.33.0-rc2) there is no tool that computes ANY cohomology of
a positive-dimensional space — no Mayer-Vietoris, no excision, no Hurewicz,
no `Hⁿ(Sⁿ)`.  BOSS's directive (2026-11-18): write the custom tools.

This file is the beachhead — a genuine cohomology computation for arbitrary
(in particular positive-dimensional) spaces:

  `componentCohomologyZeroEquiv A :
      RationalSingularCohomology A 0 ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ)`

for EVERY analytification `A` of EVERY smooth projective complex scheme,
computed from the genuine singular chain complex.  Combined with a
component identification `ZerothHomotopy ↥A.space ≃ Fin M` (the sphere-union
companion file of this wave), this is the live rank-M weight-0 fiber the
wave-45 frozen design demanded — the first honest cohomology computation of
the campaign on a positive-dimensional world.

## The construction (four engines, all new to the corpus)

1. THE GENERATOR INTERFACE (§1).  The pinned simplicial-set chain complex
   `SSet.chainComplexFunctor` presents the degree-n chains as a coproduct
   (`Sigma`) of the coefficient object over the singular n-simplices, with
   the summand inclusions `SSet.ιChainComplex`, the boundary formula
   `SSet.ιChainComplex_d` (both `simp` lemmas of
   `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean` at the
   pin), and the colimit cone `SSet.chainComplexXCofan` with
   `SSet.isColimitChainComplexXCofan` and the PLAIN-INDEXED extensionality
   `SSet.chainComplex_hom_ext` (the same file).  Specializing through the
   pinned face identifications `TopCat.δ_zero_toSSetObj₁Equiv.symm`
   (`δ 0 s ↦ the 0-simplex of f 1`) and `TopCat.δ_one_toSSetObj₁Equiv.symm`
   (`δ 1 s ↦ f 0`) yields THE ENDPOINT-BOUNDARY FORMULA: the boundary of
   the path generator is the difference of the endpoint generators.

2. THE DUAL DIFFERENTIAL (§2).  The cochain complex is the linear-Yoneda
   dual of the chain complex (the Stage-2F definition); its degree-0
   differential is precomposition with the boundary
   (`ChainComplex.linearYonedaObj_d`, the finite-point lane's verified
   name).  The kernel condition on a cochain is vanishing on the
   boundaries of the path generators; the converse is the colimit
   extensionality `SSet.chainComplex_hom_ext` with `ModuleCat.hom_injective`
   and `LinearMap.ext_ring` at the legs — every composite is closed by
   pure rfl-defeq bridges at default transparency, never by rewriting
   through `≫`-composites (the instance-spelling war).

3. THE BOTTOM-DEGREE HOMOLOGY (§3).  For a cochain complex indexed `up ℕ`,
   the incoming differential at degree zero is the shape-zero map, so the
   pinned canonical isomorphism `HomologicalComplex.isoHomologyπ 0 0`
   identifies `homology 0` with `cycles 0` — no quotient by boundaries
   appears at all.  The cycles of the degree-zero short complex of modules
   are the kernel of the outgoing map `g` — the pinned
   `ShortComplex.moduleCatCyclesIso` and the `@[simps!]` `K`-field
   `ShortComplex.moduleCatLeftHomologyData_K`.  The kernel submodule is
   defined at the plain differential spelling and the final leg is bridged
   by a tactic-level `show` at default transparency.

4. THE KERNEL-COCYCLE ISO (§4).  A degree-zero cochain kills the boundary
   of every path generator iff it takes equal values at the endpoints of
   every path (engine 1), iff it descends along `ZerothHomotopy.mk`
   (the pinned path-component quotient of
   `Mathlib/Topology/Connected/PathConnected.lean`).  The forward direction
   is `ZerothHomotopy.lift` with the endpoint formula; the backward direction
   is the coproduct lift (`IsColimit.desc` through
   `SSet.isColimitChainComplexXCofan`) of a component function, which kills
   every boundary because a function cannot distinguish
   `ZerothHomotopy.sound`-equal points.

## Honesty ledger

Every statement is proved unconditionally.  No `sorry`, no new axioms, no
`native_decide`.  The GitHub CI lane `gst-positive-dimensional-live-core-law.yml`
owns the kernel check.
-/

import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import HCUniverse2.GSTGeometricRealizationStage2F

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Simplicial
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F

namespace GSTComponentCohomologyZero

variable {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V)

/-! ## §0 Pinned shape facts for the up-ℕ bottom degree -/

theorem upNext_zero : (ComplexShape.up ℕ).next 0 = 1 :=
  CochainComplex.next ℕ 0

theorem upPrev_zero : (ComplexShape.up ℕ).prev 0 = 0 :=
  CochainComplex.prev_nat_zero

theorem upNotRel_zero_zero : ¬ (ComplexShape.up ℕ).Rel 0 0 := by
  simp [ComplexShape.up_Rel]

/-! ## §0.5 The dual differential presentation -/

/-- AUDIT(2): the degree-zero differential of the cochain complex is
precomposition with the boundary (the pinned
`ChainComplex.linearYonedaObj_d`, the finite-point lane's verified name). -/
theorem cochains_d_zero_one (A : AnalytificationData V) :
    (rationalSingularCochains A).d 0 1 =
      ModuleCat.ofHom
        (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
          ((rationalSingularChains A).d 1 0)) := by
  unfold rationalSingularCochains
  exact ChainComplex.linearYonedaObj_d
    (rationalSingularChains A) ℚ (ModuleCat.of ℚ ℚ) 0 1

/-- **THE ADJUNCTION-STYLE EVALUATION.**  The underlying linear map of the
dual differential applied to a cochain is the precomposition. -/
theorem dual_eval (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0)
    (z : (rationalSingularChains A).X 1) :
    ((rationalSingularCochains A).d 0 1 φ).hom z =
      φ.hom ((rationalSingularChains A).d 1 0 z) := by
  rw [cochains_d_zero_one A]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply]
  rfl

/-! ## §1 The generator interface and the endpoint-boundary formula -/

/-- AUDIT(1): the rational singular chains, presented as the
simplicial-set chain complex of the singular simplicial set (the
`SSet.chainComplexFunctor` unfolding through the deprecated
`singularChainComplexFunctor` alias; reducible at the pin). -/
theorem chains_eq (A : AnalytificationData V) :
    rationalSingularChains A =
      (TopCat.toSSet.obj A.space).chainComplex
        (ModuleCat.of ℚ ℚ) := rfl

/-- The generator inclusion of a point: the summand injection of the
0-simplex carried by the point `x`. -/
def ιPoint (A : AnalytificationData V) (x : ↥A.space) :
    ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 0 :=
  (TopCat.toSSet.obj A.space).ιChainComplex
    (TopCat.toSSetObj₀Equiv.symm x)

/-- The generator inclusion of a path: the summand injection of the
1-simplex carried by the path morphism `f`. -/
def ιPath (A : AnalytificationData V) (f : TopCat.I ⟶ A.space) :
    ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 1 :=
  (TopCat.toSSet.obj A.space).ιChainComplex
    (TopCat.toSSetObj₁Equiv.symm f)

/-- **THE ENDPOINT-BOUNDARY FORMULA.**  The boundary of the path generator
is the difference of the endpoint point generators.  AUDIT(4). -/
theorem ιPath_d (A : AnalytificationData V) (f : TopCat.I ⟶ A.space) :
    ιPath A f ≫ (rationalSingularChains A).d 1 0 =
      ιPoint A (f 1) - ιPoint A (f 0) := by
  -- the boundary formula at the goal's own spelling (defeq at default)
  have hgen : ιPath A f ≫ (rationalSingularChains A).d 1 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) •
        (TopCat.toSSet.obj A.space).ιChainComplex
          ((TopCat.toSSet.obj A.space).δ i
            (TopCat.toSSetObj₁Equiv.symm f)) :=
    (TopCat.toSSet.obj A.space).ιChainComplex_d (ModuleCat.of ℚ ℚ)
      (TopCat.toSSetObj₁Equiv.symm f)
  rw [hgen, Fin.sum_univ_two]
  have hface0 : (TopCat.toSSet.obj A.space).δ 0
      (TopCat.toSSetObj₁Equiv.symm f) =
      TopCat.toSSetObj₀Equiv.symm (f 1) :=
    TopCat.δ_zero_toSSetObj₁Equiv.symm f
  have hface1 : (TopCat.toSSet.obj A.space).δ 1
      (TopCat.toSSetObj₁Equiv.symm f) =
      TopCat.toSSetObj₀Equiv.symm (f 0) :=
    TopCat.δ_one_toSSetObj₁Equiv.symm f
  rw [hface0, hface1]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul]
  rw [sub_eq_add_neg]
  rfl

/-- The element-level form of the endpoint-boundary formula. -/
theorem d_path_element (A : AnalytificationData V) (f : TopCat.I ⟶ A.space) :
    (rationalSingularChains A).d 1 0 ((ιPath A f).hom (1 : ℚ)) =
      (ιPoint A (f 1)).hom (1 : ℚ) - (ιPoint A (f 0)).hom (1 : ℚ) := by
  have h := congrArg
    (fun (u : ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 0) =>
      u.hom (1 : ℚ)) (ιPath_d A f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub,
    LinearMap.sub_apply] at h
  exact h

/-! ## §2 The kernel condition at the generators -/

/-- **LEMMA A (the morphism-level generator extension).**  If a cochain's
underlying linear map kills the boundary of every path generator, then the
precomposition morphism is the zero morphism.

The proof is the pinned colimit extensionality
`SSet.chainComplex_hom_ext`; the leg composites are compared through
`ModuleCat.hom_injective` and `LinearMap.ext_ring`, with the value-at-1
bridge stated by a `show` whose defeq chain
(`hom_comp`/`hom_ofHom`/`zero_comp` are all rfl at the pin) runs entirely
at default transparency — no `≫`-composite is ever rewritten. -/
theorem precomp_zero_of_generator (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0)
    (hgen : ∀ f : TopCat.I ⟶ A.space,
      φ.hom ((rationalSingularChains A).d 1 0
        ((ιPath A f).hom (1 : ℚ))) = 0) :
    ModuleCat.ofHom
      ((φ.hom).comp
        ((rationalSingularChains A).d 1 0).hom) = 0 := by
  refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj A.space)
    (R := ModuleCat.of ℚ ℚ) (fun σ => ?_)
  obtain ⟨f, rfl⟩ := (A.space.toSSetObj₁Equiv.symm).surjective σ
  apply ModuleCat.hom_injective
  apply LinearMap.ext_ring
  exact hgen f

/-- AUDIT(2): the `leftComp` application defeq — the precomposition
cochain IS the wrapped precomposition linear map. -/
theorem leftComp_apply_eq (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
        ((rationalSingularChains A).d 1 0)) φ =
      ModuleCat.ofHom
        ((φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ).comp
          ((rationalSingularChains A).d 1 0).hom) := rfl

/-- **THE KERNEL CONDITION AT THE GENERATORS.**  A degree-zero cochain
lies in the kernel of the dual differential iff its underlying linear map
kills the boundary of every path generator. -/
theorem cochain_ker_iff (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    (rationalSingularCochains A).d 0 1 φ = 0 ↔
      ∀ f : TopCat.I ⟶ A.space,
        φ.hom ((rationalSingularChains A).d 1 0
          ((ιPath A f).hom (1 : ℚ))) = 0 := by
  constructor
  · intro hφ f
    have h0 : ((rationalSingularCochains A).d 0 1 φ).hom
        ((ιPath A f).hom (1 : ℚ)) = 0 := by
      rw [hφ]
      rfl
    rw [dual_eval] at h0
    exact h0
  · intro hgen
    show ModuleCat.ofHom
      ((φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ).comp
        ((rationalSingularChains A).d 1 0).hom) = 0
    exact precomp_zero_of_generator A φ hgen

/-! ## §3 The bottom-degree homology -/

/-- The kernel submodule of the dual differential. -/
def kerDual (A : AnalytificationData V) :
    Submodule ℚ ((rationalSingularCochains A).X 0) :=
  LinearMap.ker ((rationalSingularCochains A).d 0 1).hom

/-- AUDIT(2): membership in the kernel submodule is the element equation. -/
theorem mem_kerDual_iff (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    φ ∈ kerDual A ↔ (rationalSingularCochains A).d 0 1 φ = 0 := Iff.rfl

/-- **THE BOTTOM-DEGREE HOMOLOGY.**  The homology of the cochain complex
at degree zero is the kernel of the outgoing differential.

The proof is the two-step pinned canonical assembly:

* `HomologicalComplex.isoHomologyπ 0 0` — when the INCOMING differential
  `d 0 0` is zero (the `up ℕ` shape at the bottom degree), the pinned
  canonical isomorphism gives `homology 0 ≅ cycles 0` — no quotient by
  boundaries appears at all;

* `ShortComplex.moduleCatCyclesIso` — the cycles of the degree-zero
  short complex of modules are the kernel of `g`, explicitly
  `of ℚ ↥(ker g.hom)` through the pinned `@[simps!]` data.  The final leg
  to the `kerDual` spelling is a tactic-level `show` at default
  transparency (the `g`-field of the degree-zero short complex IS the
  outgoing differential by the colimit-cone construction). -/
noncomputable def homologyZeroIsoKer (A : AnalytificationData V) :
    (rationalSingularCochains A).homology 0 ≅
      ModuleCat.of ℚ ↥(kerDual A) := by
  refine ((rationalSingularCochains A).isoHomologyπ 0 0 upPrev_zero
      ((rationalSingularCochains A).shape 0 0 upNotRel_zero_zero)).symm ≪≫ ?_
  refine ((rationalSingularCochains A).sc 0).moduleCatCyclesIso ≪≫ ?_
  rw [ShortComplex.moduleCatLeftHomologyData_K]
  unfold HomologicalComplex.sc HomologicalComplex.shortComplexFunctor
  unfold HomologicalComplex.shortComplexFunctor'
  rw [upNext_zero]
  rfl

/-! ## §4 The kernel-cocycle iso -/

/-- The function on points carried by a degree-zero cochain. -/
def cochainComponentFun (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) : ↥A.space → ℚ :=
  fun x => φ.hom ((ιPoint A x).hom (1 : ℚ))

/-- **PATH-CONSTANCY OF KERNEL COCHAINS.**  A kernel cochain takes equal
values at the endpoints of every path: the endpoint-boundary formula turns
the path into a boundary, and the kernel condition kills it. -/
theorem cochainComponentFun_sound (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A)
    (x y : ↥A.space) (p : Path x y) :
    cochainComponentFun A φ x = cochainComponentFun A φ y := by
  set f : TopCat.I ⟶ A.space := (TopCat.pathEquiv.symm p).hom with hf
  have h0 : f 0 = x := (TopCat.pathEquiv.symm p).hom₀
  have h1 : f 1 = y := (TopCat.pathEquiv.symm p).hom₁
  have hd : (rationalSingularCochains A).d 0 1 φ = 0 :=
    (mem_kerDual_iff A φ).mp hφ
  have hgen := (cochain_ker_iff A φ).mp hd f

  rw [d_path_element A f, map_sub, sub_eq_zero] at hgen
  calc cochainComponentFun A φ x = φ.hom ((ιPoint A x).hom (1 : ℚ)) := rfl
    _ = φ.hom ((ιPoint A (f 0)).hom (1 : ℚ)) := by rw [h0]
    _ = φ.hom ((ιPoint A (f 1)).hom (1 : ℚ)) := hgen.symm
    _ = cochainComponentFun A φ y := by rw [h1]; rfl

/-- The component function of a kernel cochain: the descent along the
path-component quotient. -/
def componentFunOf (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A) :
    ZerothHomotopy ↥A.space → ℚ :=
  ZerothHomotopy.lift (cochainComponentFun A φ)
    (fun _ _ p => cochainComponentFun_sound A φ hφ _ _ p)

/-- The leg morphism of a component function at a 0-simplex: the scalar
multiplication by the component's value. -/
def componentLeg (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ)
    (σ : (TopCat.toSSet.obj A.space) _⦋0⦌) :
    ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom
    { toFun := fun r => r • g (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv σ))
      map_add' := by
        intro r₁ r₂
        simp only [add_smul]
      map_smul' := by
        intro q r
        simp only [smul_eq_mul, RingHom.id_apply, mul_assoc] }

/-- The value of a component leg at the generator `1` is the component
function's value on the point class (through the equiv roundtrip). -/
theorem componentLeg_one (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) (x : ↥A.space) :
    (componentLeg A g (TopCat.toSSetObj₀Equiv.symm x)).hom (1 : ℚ) =
      g (ZerothHomotopy.mk x) := by
  have hround : TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm x) = x :=
    (TopCat.toSSetObj₀Equiv (X := A.space)).apply_symm_apply x
  show (1 : ℚ) • g (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv
      (TopCat.toSSetObj₀Equiv.symm x))) = g (ZerothHomotopy.mk x)
  rw [hround, one_smul]

/-- The coproduct lift of a component function: the unique morphism from
the degree-zero chains whose leg values are the component function's
values on the point classes. -/
def componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    (rationalSingularChains A).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  ((TopCat.toSSet.obj A.space).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) 0).desc
    (Cofan.mk _
      (fun σ => componentLeg A g σ))

/-- **THE LEG EQUATION.**  The coproduct lift evaluates at a point
generator as the component function's value on the point class.  The
cocone index is `Discrete`-wrapped (the pinned colimit cocone API). -/
theorem ιPoint_comp_componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) (x : ↥A.space) :
    ιPoint A x ≫ componentCochainMorph A g =
      componentLeg A g (TopCat.toSSetObj₀Equiv.symm x) :=
    ((TopCat.toSSet.obj A.space).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) 0).fac
      (Cofan.mk _ (fun σ => componentLeg A g σ))
      ⟨TopCat.toSSetObj₀Equiv.symm x⟩

/-- **THE COMPONENT COCHAIN IS A KERNEL ELEMENT.**  The coproduct lift of
a component function kills every path boundary: its leg values cannot
distinguish `ZerothHomotopy.sound`-equal points. -/
theorem componentCochainMorph_mem_kerDual (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    componentCochainMorph A g ∈ kerDual A := by
  refine (mem_kerDual_iff A (componentCochainMorph A g)).mpr ?_
  refine (cochain_ker_iff A (componentCochainMorph A g)).mpr ?_
  intro f
  rw [d_path_element A f, map_sub, sub_eq_zero]
  -- both endpoint evaluations are leg values of sound-equal points
  have hpath : Path (f 0) (f 1) :=
    TopCat.pathEquiv { hom := f, hom₀ := rfl, hom₁ := rfl }
  have hsound : ZerothHomotopy.mk (f 0) = ZerothHomotopy.mk (f 1) :=
    ZerothHomotopy.sound hpath
  have hleg1 : (componentCochainMorph A g).hom
      ((ιPoint A (f 1)).hom (1 : ℚ)) =
      g (ZerothHomotopy.mk (f 1)) := by
    rw [show (componentCochainMorph A g).hom ((ιPoint A (f 1)).hom (1 : ℚ)) =
        (ιPoint A (f 1) ≫ componentCochainMorph A g).hom (1 : ℚ) from rfl,
      ιPoint_comp_componentCochainMorph A g (f 1),
      componentLeg_one A g (f 1)]
  have hleg0 : (componentCochainMorph A g).hom
      ((ιPoint A (f 0)).hom (1 : ℚ)) =
      g (ZerothHomotopy.mk (f 0)) := by
    rw [show (componentCochainMorph A g).hom ((ιPoint A (f 0)).hom (1 : ℚ)) =
        (ιPoint A (f 0) ≫ componentCochainMorph A g).hom (1 : ℚ) from rfl,
      ιPoint_comp_componentCochainMorph A g (f 0),
      componentLeg_one A g (f 0)]
  rw [hleg1, hleg0, ← hsound]

/-- **THE FIRST TRIANGLE.**  The component function of the coproduct lift
of `g` is `g` itself. -/
theorem componentFunOf_componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    componentFunOf A (componentCochainMorph A g)
      (componentCochainMorph_mem_kerDual A g) = g := by
  funext z
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
  rw [show componentFunOf A (componentCochainMorph A g)
      (componentCochainMorph_mem_kerDual A g) (ZerothHomotopy.mk x) =
    cochainComponentFun A (componentCochainMorph A g) x from rfl,
    show cochainComponentFun A (componentCochainMorph A g) x =
      (componentCochainMorph A g).hom ((ιPoint A x).hom (1 : ℚ)) from rfl,
    show (componentCochainMorph A g).hom ((ιPoint A x).hom (1 : ℚ)) =
      (ιPoint A x ≫ componentCochainMorph A g).hom (1 : ℚ) from rfl,
    ιPoint_comp_componentCochainMorph A g x,
    componentLeg_one A g x]

/-- **THE SECOND TRIANGLE.**  The coproduct lift of the component
function of a kernel cochain is the cochain itself (by the uniqueness of
the coproduct lift). -/
theorem componentCochainMorph_componentFunOf (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A) :
    componentCochainMorph A (componentFunOf A φ hφ) = φ := by
  refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj A.space)
    (R := ModuleCat.of ℚ ℚ) ?_
  intro σ
  obtain ⟨x, rfl⟩ := (A.space.toSSetObj₀Equiv.symm).surjective σ
  -- both morphisms have the same leg values
  show ιPoint A x ≫ componentCochainMorph A (componentFunOf A φ hφ) =
      ιPoint A x ≫ φ
  rw [ιPoint_comp_componentCochainMorph]
  apply ModuleCat.hom_injective
  apply LinearMap.ext_ring
  rw [componentLeg_one A (componentFunOf A φ hφ) x]
  show (componentFunOf A φ hφ) (ZerothHomotopy.mk x) =
      φ.hom ((ιPoint A x).hom (1 : ℚ))
  rfl

/-- **THE KERNEL-COCYCLE ISO.**  The kernel of the dual differential is
the function space on the path components. -/
noncomputable def kerDualEquiv (A : AnalytificationData V) :
    ↥(kerDual A) ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ) where
  toFun φ := componentFunOf A (φ : (rationalSingularCochains A).X 0) φ.2
  map_add' φ ψ := by
    funext z
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
    show cochainComponentFun A ((φ : (rationalSingularCochains A).X 0) +
        (ψ : (rationalSingularCochains A).X 0)) x =
      cochainComponentFun A (φ : (rationalSingularCochains A).X 0) x +
        cochainComponentFun A (ψ : (rationalSingularCochains A).X 0) x
    rfl
  map_smul' q φ := by
    funext z
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
    show cochainComponentFun A (q • (φ : (rationalSingularCochains A).X 0)) x =
      q • cochainComponentFun A (φ : (rationalSingularCochains A).X 0) x
    rfl
  invFun g := ⟨componentCochainMorph A g,
    componentCochainMorph_mem_kerDual A g⟩
  left_inv φ := by
    apply Subtype.ext
    exact componentCochainMorph_componentFunOf A (φ : _) φ.2
  right_inv g := componentFunOf_componentCochainMorph A g

/-! ## §5 THE MAIN THEOREM -/

/-- **THE COMPONENT H⁰ MACHINE.**  The degree-zero rational singular
cohomology of any analytification is the function space on its path
components — computed from the genuine singular chain complex, with no
discreteness, no vanishing, and no dimension assumption.  This is the
positive-dimensional beachhead: the first cohomology computation of the
campaign that applies to positive-dimensional worlds. -/
noncomputable def componentCohomologyZeroEquiv (A : AnalytificationData V) :
    RationalSingularCohomology A 0 ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ) :=
  ((homologyZeroIsoKer A).toLinearEquiv).trans (kerDualEquiv A)

/-- **THE FINITE-RANK SPECIALIZATION.**  With a component identification
against `Fin M`, the degree-zero cohomology is the free rank-M function
space.  This is the live rank-M weight-0 fiber of the wave-45 frozen
design. -/
noncomputable def componentCohomologyZeroEquivFinM
    (A : AnalytificationData V) (M : ℕ)
    (e : ZerothHomotopy ↥A.space ≃ Fin M) :
    RationalSingularCohomology A 0 ≃ₗ[ℚ] (Fin M → ℚ) :=
  LinearEquiv.ofBijective
    { toFun := fun x i => componentCohomologyZeroEquiv A x (e.symm i)
      map_add' := by
        intro x y
        funext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro q x
        funext i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply] }
    (by
      constructor
      · intro x y hxy
        have h : ∀ z : ZerothHomotopy ↥A.space,
            componentCohomologyZeroEquiv A x z =
              componentCohomologyZeroEquiv A y z := by
          intro z
          have hz := congrFun hxy (e z)
          simpa using hz
        exact (componentCohomologyZeroEquiv A).injective (funext h)
      · intro f
        refine ⟨(componentCohomologyZeroEquiv A).symm
          (fun z => f (e z)), ?_⟩
        funext i
        have h := (componentCohomologyZeroEquiv A).apply_symm_apply
          (fun z => f (e z))
        simpa using congrFun h (e.symm i))

end GSTComponentCohomologyZero
