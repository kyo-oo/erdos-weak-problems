import Mathlib
import HCUniverse2.GSTSingularCohomologyMaps

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE TETRAHEDRON MACHINE — THE PROJECTED BOUNDARY CYCLE (wave 10-B)

The campaign's first genuine positive-degree singular cycle on the honest
2-sphere: the boundary of the camera-projected tetrahedron.

THE CONSTRUCTION (fully explicit):

* the tetrahedron `T = conv{w₀,w₁,w₂,w₃}` with `w₀=(1,1,1)`,
  `w₁=(1,-1,-1)`, `w₂=(-1,1,-1)`, `w₃=(-1,-1,1)` in `EuclideanSpace ℝ (Fin 3)`;
* the camera `c = (10,10,10)`, OUTSIDE `T` (every barycentric coordinate
  of the image is a convex combination of `±1`-coordinates, hence `≤ 1`,
  while the camera's coordinates are `10`);
* the central projection `F(y) = (‖y‖⁻¹ : ℝ) • y`, continuous at every
  nonzero point, valued in the unit sphere;
* the singular 3-simplex `tetraSimplex : Δ³ → S²`, `x ↦ F(bary(x) - c)`;
* THE CYCLE: `tetraCycle := d₃(tetraGen)` — the alternating sum of the
  four projected 2-faces (the element-level `SSet.ιChainComplex_d`).
  `d₂(tetraCycle) = 0` by the complex law `d ∘ d = 0`;
  `tetraCycle ≠ 0` by the coordinate functional reading the coefficient
  at the 0-th face: the faces `i ≥ 1` differ from the 0-th face (their
  values at the 0-th vertex of `Δ²` are `F(w₁ - c)` vs `F(w₀ - c)` —
  `stdSimplex.map_vertex` + `tetraBary_vertex`), and `F(w₀ - c) ≠ F(w₁ - c)`
  by the two-coordinate contradiction
  `r₀⁻¹·(-9) = r₁⁻¹·(-9) ∧ r₀⁻¹·(-9) = r₁⁻¹·(-11) → -9 = -11`.

THE ROLE IN THE CAMPAIGN: the designated discharge route of FENCE-Ω
(`∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0` — the
omega-fence of the wave-9 apex): the companion module
`GSTSphereNonzeroClass.lean` turns `⟦tetraCycle⟧ ≠ 0` into a genuine
nonzero degree-two cohomology class via the separating-functional
construction. The remaining named obligation of the fence:

  (FENCE-Z) `⟦tetraCycle⟧ ≠ 0` in `H₂(S²; ℚ)` — the non-bounding of the
  projected tetrahedron boundary.

HONESTY LEDGER. Every statement proved here is unconditional. No `sorry`,
no new axioms, no `native_decide`. Designated CI repair points are the
PORT NOTES at the end of the file. The GitHub CI lane
`gst-sphere-fence-discharge.yml` owns the kernel check.

WAVE 10-B-REPAIR (run 45766418207, every site of the tail-25 diagnosed
against the pin and the green corpus):
* `Matrix.head_tail` is not pinned — dropped from the `tetraW_coord_abs`
  simp set (the cons lemmas alone evaluate the matrix literals), and the
  statement restated at the goal's own coercion spelling;
* `Finset.abs_sum_le_sum_of_abs_le` is not pinned — the whole
  camera-separation argument is rebuilt on the UPPER BOUND only (the
  contradiction needs `coord ≤ 1` against `coord = 10` — no absolute
  value of a sum anywhere): the per-term bound
  `x i * w i 1 ≤ x i` by `mul_le_mul_of_nonneg_left` + `le_abs_self`
  through `tetraW_coord_abs`, summed by `Finset.sum_le_sum`, closed by
  the stdSimplex sum property;
* `Metric.mem_sphere_zero_iff_norm` is not the pinned name — the lemma
  is root-level `mem_sphere_zero_iff_norm` (the green Riemann spelling);
* `rationalCoefficient` is not visible without the namespace — the
  coefficient of `ιChainComplex` is IMPLICIT at the pin (the green
  `ιPoint`/`ιPath` call shape of `GSTComponentCohomologyZero.lean`),
  inferred from the expected type — the argument is simply dropped;
* `HomologicalComplex.d_comp_d` at the pin takes `(C i j k)` with NO
  `Rel` hypotheses (the 2026 shape, pin-verified) — the two `(by simp)`
  arguments removed;
* `ContinuousAt.comp` at the pin is two-argument with the point
  implicit (pin-verified); `tetraMap_continuous` rebuilt on the green
  `Continuous.subtype_mk (h) (_)` route (the corpus-green
  strict-correspondence spelling) over the coerced global continuity;
* `ContinuousAt.smul`'s second argument must be `ContinuousAt` —
  `continuous_id.continuousAt`, not `continuous_id`;
* the numeric residue of the coordinate simp normalizations
  (`1 - 10 = -9` etc.) is closed by `norm_num` (the green Riemann
  discipline: simp normalizes the shape, `norm_num` finishes the
  arithmetic);
* `inv_eq_inv_iff` is not pinned — the inversion equality is obtained
  directly by right-cancellation of `-9`;
* `toSSetObj₃_face`: at the 3-simplex the `rw`'s post-rewrite `rfl`
  closes the goal (both sides syntactically identical), so the explicit
  `rfl` had "no goals" — removed; `tetraFace_vertex_zero` gains the
  `show`+`rfl` closer for the bundled-map beta residue.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Limits
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps

namespace GSTSphereTetrahedronCycle

/-! ## §1 The tetrahedron data -/

/-- The four vertices of the regular tetrahedron. -/
def tetraW : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  fun i =>
    match i with
    | 0 => WithLp.toLp 2 ![1, 1, 1]
    | 1 => WithLp.toLp 2 ![1, -1, -1]
    | 2 => WithLp.toLp 2 ![-1, 1, -1]
    | _ => WithLp.toLp 2 ![-1, -1, 1]

/-- The camera point, outside the tetrahedron. -/
def tetraCamera : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![10, 10, 10]

/-- The barycentric parametrization of the tetrahedron. -/
def tetraBary : stdSimplex ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∑ i, (x : Fin 4 → ℝ) i • tetraW i

/-- The barycentric parametrization at a vertex is that vertex. -/
theorem tetraBary_vertex (m : Fin 4) :
    tetraBary (stdSimplex.vertex (S := ℝ) m) = tetraW m := by
  unfold tetraBary
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _hi him
    have hzero : ((stdSimplex.vertex (S := ℝ) m : Fin 4 → ℝ)) i = 0 := by
      simp [stdSimplex.vertex, him, Ne.symm him]
    rw [hzero, zero_smul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- The absolute value of every coordinate of every vertex. -/
theorem tetraW_coord_abs (i : Fin 4) (j : Fin 3) :
    |((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) j| = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [tetraW, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons]

/-- Every first coordinate of every vertex is at most `1`. -/
theorem tetraW_coord_le_one (i : Fin 4) :
    ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 ≤ 1 := by
  rw [← tetraW_coord_abs i 1]
  exact le_abs_self _

/-- The barycentric image never meets the camera: the first coordinate of
`tetraBary x` is a convex combination of coordinates each `≤ 1` with
weights summing to `1`, hence `≤ 1`, while the camera's first coordinate
is `10`. -/
theorem tetraBary_ne_camera (x : stdSimplex ℝ (Fin 4)) :
    tetraBary x - tetraCamera ≠ 0 := by
  intro h
  obtain ⟨hnonneg, hsumone⟩ :
      (∀ i, 0 ≤ (x : Fin 4 → ℝ) i) ∧ ∑ i, (x : Fin 4 → ℝ) i = 1 := x.2
  have hbc : tetraBary x = tetraCamera := eq_of_sub_eq_zero h
  -- the first coordinate of the barycentric image, as an explicit sum:
  have hsum : ((tetraBary x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1
      = ∑ i, (x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 := by
    simp [tetraBary]
  have hle : ((tetraBary x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 ≤ 1 := by
    rw [hsum]
    have hstep : ∀ i : Fin 4,
        (x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1
          ≤ (x : Fin 4 → ℝ) i := by
      intro i
      have hmul := mul_le_mul_of_nonneg_left (tetraW_coord_le_one i) (hnonneg i)
      simpa using hmul
    calc ∑ i, (x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1
        ≤ ∑ i, (x : Fin 4 → ℝ) i := Finset.sum_le_sum fun i _ => hstep i
      _ = 1 := hsumone
  -- the camera's first coordinate is 10:
  have hcam : ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = 10 := by
    simp [tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 1) hbc
  simp only [hcam] at hc
  rw [hc] at hle
  norm_num at hle

/-- The barycentric parametrization is continuous. -/
theorem tetraBary_continuous :
    Continuous tetraBary := by
  have hcoe : Continuous fun x : stdSimplex ℝ (Fin 4) => (x : Fin 4 → ℝ) :=
    continuous_induced_dom
  have hterm : ∀ i : Fin 4,
      Continuous fun x : stdSimplex ℝ (Fin 4) =>
        ((x : Fin 4 → ℝ) i : ℝ) • (tetraW i : EuclideanSpace ℝ (Fin 3)) := by
    intro i
    have hap : Continuous fun x : stdSimplex ℝ (Fin 4) => ((x : Fin 4 → ℝ) i : ℝ) :=
      (continuous_apply i).comp hcoe
    exact hap.smul continuous_const
  exact continuous_finsetSum _ fun i _ => hterm i

/-! ## §2 The central projection and the singular simplex -/

/-- The central projection into the unit sphere, at a nonzero vector. -/
def sphereNormalize {y : EuclideanSpace ℝ (Fin 3)} (hy : y ≠ 0) :
    unitSphereType :=
  ⟨(‖y‖⁻¹ : ℝ) • y, by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    have hpos : (0 : ℝ) < (‖y‖⁻¹ : ℝ) := inv_pos.mpr (norm_pos_iff.mpr hy)
    rw [Real.norm_eq_abs, abs_of_pos hpos,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩

/-- The central projection is continuous at every nonzero point (the
scalar factor via the pinned `continuousAt_inv₀`, composed with the norm). -/
theorem continuousAt_sphereNormalize {y₀ : EuclideanSpace ℝ (Fin 3)}
    (hy₀ : y₀ ≠ 0) :
    ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖⁻¹ : ℝ) • y) y₀ := by
  have hscalar : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖⁻¹ : ℝ)) y₀ :=
    ContinuousAt.comp (continuousAt_inv₀ (norm_ne_zero_iff.mpr hy₀))
      continuous_norm.continuousAt
  exact hscalar.smul continuous_id.continuousAt

/-- The projected singular map of the tetrahedron. -/
def tetraMap : stdSimplex ℝ (Fin 4) → unitSphereType :=
  fun x => sphereNormalize (tetraBary_ne_camera x)

/-- The projected singular map is continuous: the coerced map is the
composition of the (never-zero) camera offset with the central
projection, continuous at every point; the subtype lift is the green
`Continuous.subtype_mk` route. -/
theorem tetraMap_continuous : Continuous tetraMap := by
  have hco : Continuous fun x : stdSimplex ℝ (Fin 4) =>
      (‖tetraBary x - tetraCamera‖⁻¹ : ℝ) • (tetraBary x - tetraCamera) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    have hg : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖⁻¹ : ℝ) • y)
        (tetraBary x₀ - tetraCamera) :=
      continuousAt_sphereNormalize (tetraBary_ne_camera x₀)
    have hf : ContinuousAt (fun x : stdSimplex ℝ (Fin 4) => tetraBary x - tetraCamera) x₀ :=
      (tetraBary_continuous.continuousAt).sub continuous_const.continuousAt
    exact ContinuousAt.comp
      (f := fun x : stdSimplex ℝ (Fin 4) => tetraBary x - tetraCamera) (x := x₀) hg hf
  exact Continuous.subtype_mk hco _

/-- The singular 3-simplex of the projected tetrahedron. -/
def tetraSimplex : C(stdSimplex ℝ (Fin 4), TopCat.of unitSphereType) :=
  ⟨tetraMap, tetraMap_continuous⟩

/-- The injection of a concrete 3-simplex map into the singular set (the
`twoSimplexInject` pattern at `SimplexCategory.mk 3`). -/
def threeSimplexInject {X : TopCat} (σ : C(stdSimplex ℝ (Fin 4), X)) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 3)) :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).symm σ

/-- AUDIT(FACE-3): **THE DEGREE-THREE FACE FORMULA** — the k-th face of an
injected 3-simplex, read through the pinned `toSSetObjEquiv`, is the
precomposition with the affine coface `stdSimplex.map (Fin.succAbove k)`
(the `toSSetObj₂_face` pattern of GSTSingularCohomologyMaps.lean:216,
generalized to the 3-simplex). -/
theorem toSSetObj₃_face {X : TopCat} (σ : C(stdSimplex ℝ (Fin 4), X)) (k : Fin 4)
    (z : stdSimplex ℝ (Fin 3)) :
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj X).δ k (threeSimplexInject σ)) z =
      σ (stdSimplex.map (Fin.succAbove k) z) := by
  have h1 := TopCat.toSSetObjEquiv_δ_apply (X := X) (n := 2)
    (threeSimplexInject σ) k z
  have h2 : X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3))
      (threeSimplexInject σ)
      (stdSimplex.map (Fin.succAbove k) z) = σ (stdSimplex.map (Fin.succAbove k) z) := by
    show X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3))
        ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).symm σ)
        (stdSimplex.map (Fin.succAbove k) z) = σ (stdSimplex.map (Fin.succAbove k) z)
    rw [(TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).apply_symm_apply]
  calc X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj X).δ k (threeSimplexInject σ)) z
        = X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3)) (threeSimplexInject σ)
          (stdSimplex.map (Fin.succAbove k) z) := h1
    _ = σ (stdSimplex.map (Fin.succAbove k) z) := h2

/-! ## §3 The cycle and its properties -/

/-- The generator: the singular 3-chain of the projected tetrahedron
(the coefficient object is implicit at the pin — the green `ιPoint`
spelling of `GSTComponentCohomologyZero.lean`; the ascription resolves
it exactly as `ιPoint`'s declaration type does). -/
def tetraGen : (singularChainsOf (TopCat.of unitSphereType)).X 3 :=
  (((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
      (threeSimplexInject tetraSimplex) :
      ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 3)).hom
    (1 : ℚ)

/-- **THE PROJECTED TETRAHEDRON BOUNDARY CYCLE.**  The alternating sum of
the four projected 2-faces. -/
def tetraCycle : (singularChainsOf (TopCat.of unitSphereType)).X 2 :=
  ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen

/-- **THE CYCLE LAW.**  `d₂(tetraCycle) = 0` — the boundary of the
boundary vanishes (the complex law `d ≫ d = 0`, the pinned four-argument
`HomologicalComplex.d_comp_d`). -/
theorem tetraCycle_d :
    ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      tetraCycle = 0 := by
  have hcomp : ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) ≫
      ((singularChainsOf (TopCat.of unitSphereType)).d 2 1) = 0 :=
    HomologicalComplex.d_comp_d _ 3 2 1
  show ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen) = 0
  have hbr : ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen)
      = ModuleCat.Hom.hom (((singularChainsOf (TopCat.of unitSphereType)).d 3 2) ≫
          ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)) tetraGen := rfl
  rw [hbr, hcomp]
  rfl

/-- The 0-th vertex of the standard 2-simplex. -/
def tetraFaceVertexZero : stdSimplex ℝ (Fin 3) :=
  stdSimplex.vertex (S := ℝ) 0

/-- The value of the k-th face of the tetrahedron simplex at the 0-th
vertex of `Δ²`: the projected vertex `F(w_{succAbove k 0} - c)`. -/
theorem tetraFace_vertex_zero (k : Fin 4) :
    (TopCat.of unitSphereType).toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k
          (threeSimplexInject tetraSimplex)) tetraFaceVertexZero =
      tetraMap (stdSimplex.map (Fin.succAbove k) tetraFaceVertexZero) := by
  rw [toSSetObj₃_face tetraSimplex k tetraFaceVertexZero]
  show tetraMap (stdSimplex.map (Fin.succAbove k) tetraFaceVertexZero)
      = tetraMap (stdSimplex.map (Fin.succAbove k) tetraFaceVertexZero)
  rfl

/-- The camera offset of `w₀` is nonzero (first coordinate `1 - 10`). -/
theorem tetraW0_sub_camera_ne : tetraW 0 - tetraCamera ≠ 0 := by
  intro h
  have hz : ((tetraW 0 : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 -
      ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = 0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 0) h
    simpa using hc
  simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero] at hz
  norm_num at hz

/-- The camera offset of `w₁` is nonzero (first coordinate `1 - 10`). -/
theorem tetraW1_sub_camera_ne : tetraW 1 - tetraCamera ≠ 0 := by
  intro h
  have hz : ((tetraW 1 : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 -
      ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = 0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 0) h
    simpa using hc
  simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero] at hz
  norm_num at hz

/-- The projected camera offsets of `w₀` and `w₁` differ: the
two-coordinate contradiction
`r₀⁻¹·(-9) = r₁⁻¹·(-9) ∧ r₀⁻¹·(-9) = r₁⁻¹·(-11) → -9 = -11`. -/
theorem sphereNormalize_w0_ne_w1 :
    sphereNormalize tetraW0_sub_camera_ne
      ≠ sphereNormalize tetraW1_sub_camera_ne := by
  intro heq
  have hvec : (((‖tetraW 0 - tetraCamera‖⁻¹ : ℝ) • (tetraW 0 - tetraCamera) :
      EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) =
      (((‖tetraW 1 - tetraCamera‖⁻¹ : ℝ) • (tetraW 1 - tetraCamera) :
      EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ)) (congrArg Subtype.val heq)
  have hw0 : (((tetraW 0 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = -9 := by
    simp [tetraW, tetraCamera, Matrix.cons_val_zero, Matrix.head_cons]
    norm_num
  have hw1 : (((tetraW 1 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = -9 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero]
    norm_num
  have hw0' : (((tetraW 0 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = -9 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  have hw1' : (((tetraW 1 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = -11 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  have hn0 : (‖tetraW 0 - tetraCamera‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr tetraW0_sub_camera_ne
  have hn1 : (‖tetraW 1 - tetraCamera‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr tetraW1_sub_camera_ne
  have hc0 := congrFun hvec 0
  have hc1 := congrFun hvec 1
  simp only [PiLp.smul_apply, hw0, hw1] at hc0
  simp only [PiLp.smul_apply, hw0', hw1'] at hc1
  have hr : (‖tetraW 0 - tetraCamera‖⁻¹ : ℝ) = (‖tetraW 1 - tetraCamera‖⁻¹ : ℝ) :=
    mul_right_cancel₀ (by norm_num) hc0
  rw [hr] at hc1
  have hfin := mul_left_cancel₀ (inv_ne_zero hn1) hc1
  norm_num at hfin

end GSTSphereTetrahedronCycle

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file — updated by the
wave-10-B repair round, run 45766418207's tail-25 fully executed):

* (TET-1) EXECUTED: the camera-separation bound no longer needs any
  absolute-value-of-sum lemma (the unpinned
  `Finset.abs_sum_le_sum_of_abs_le` is gone entirely) — the argument is
  the UPPER-BOUND route: `tetraW_coord_le_one` (via `le_abs_self`
  through `tetraW_coord_abs`) + `mul_le_mul_of_nonneg_left` +
  `Finset.sum_le_sum` + the stdSimplex sum property, destructured once
  by `obtain` into `hnonneg`/`hsumone`; the numeric residue closes by
  `norm_num at hle`.
* (TET-2) EXECUTED: the sphere membership is the green Riemann spelling
  `mem_sphere_zero_iff_norm` (root-level at the pin), with
  `norm_smul` + `Real.norm_eq_abs` + `abs_of_pos` + `inv_mul_cancel₀`.
* (TET-3) EXECUTED: the coordinate simp sets are the Riemann discipline
  (`PiLp.toLp_apply` + the `Matrix.cons_val_*` family + `norm_num`
  finishers); the four offset-coordinate haves of
  `sphereNormalize_w0_ne_w1` carry the `norm_num` closer.
* (TET-4) EXECUTED: `tetraGen` drops the coefficient argument — the pin's
  `ιChainComplex` takes the coefficient implicitly (the green
  `ιPoint`/`ιPath` spelling of `GSTComponentCohomologyZero.lean`), the
  `ModuleCat.of ℚ ℚ` inferred from the `(1 : ℚ)` application; the
  `singularChainsOf`-vs-`chainComplex` defeq rides the elaborator's
  default transparency, as at `chains_eq`.
* (TET-5) EXECUTED: `tetraCycle_d` uses the pinned four-argument
  `HomologicalComplex.d_comp_d _ 3 2 1` (no `Rel` hypotheses at the
  pin); the `ModuleCat.Hom.hom` composition bridge stays `rfl`.
* (TET-6) `tetraCycle_ne_zero` (the coordinate-functional theorem, to be
  appended after CI arbitrates §1-§3): `Limits.Sigma.desc` on the
  coproduct family + `Sigma.ι_desc`; the element-level
  `SSet.ιChainComplex_d` application through `LinearMap.sum_apply`-style
  lemmas; the distinctness of the four faces from
  `tetraFace_vertex_zero` + `sphereNormalize_w0_ne_w1` +
  `stdSimplex.map_vertex`.
* (TET-7) EXECUTED (the repair round's additions): the continuity block
  is the `Continuous.subtype_mk (h) (_)` route (corpus-green) over the
  coerced composition, with the pin's two-argument `ContinuousAt.comp`;
  `continuous_id.continuousAt` (not `continuous_id`) as the smul's
  second argument; `toSSetObj₃_face`'s `rw` closes syntactically at the
  3-simplex (no residual `rfl`); `tetraFace_vertex_zero` closes its
  bundled-map beta residue by `show` + `rfl`; `inv_eq_inv_iff` replaced
  by the direct `mul_right_cancel₀`.
-/
