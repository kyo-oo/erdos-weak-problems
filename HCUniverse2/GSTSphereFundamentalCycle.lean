import Mathlib
import HCUniverse2.GSTSphereNonzeroClass
import HCUniverse2.GSTComponentCohomologyZero

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FUNDAMENTAL CYCLE — the center-radial route (wave 11)

THE CORRECTION BOSS ORDERED.  The point-arithmetic audit confirmed the
disclosed weakness: the honest Hodge data's designed fibers do not assert
the sphere's topology — the two stashed sectors (the weight-one SPANNING
at a nonzero family index, the higher-weight VANISHING) both reduce to
the fence hypothesis (Ω): `H²(S²; ℚ) ≠ 0`.  The wave-10 route to a
witness through the CAMERA-projected tetrahedron boundary was closed by
the route-correction certificate (`tetraCycle = d₃(tetraGen)` — the
projected solid is an honest singular 3-chain of the sphere, so the
projected boundary BOUNDS; `not_TetraSeparator` is FALSE at that cycle).

THIS MODULE builds the corrected route's first half: the CENTER-RADIAL
FUNDAMENTAL 2-CYCLE of the sphere — the classical generator of
H₂(S²; ℚ) ≅ ℚ, constructed in the honest singular chain complex:

* the four vertices `tetraW` are the alternating tetrahedron, whose
  barycenter IS the sphere's origin — the center-radial projection
  `y ↦ ‖y‖⁻¹ • y` is defined on every CLOSED FACE (any three of the
  four vertices are linearly independent, so no face meets the origin),
  but NOT on the solid (the origin is interior) — exactly the structural
  difference that makes the boundary cycle non-bounding classically;
* `fundCycle := faceChain 0 - faceChain 1 + faceChain 2 - faceChain 3`
  — the alternating sum of the four center-radial face 2-simplices;
* **THE CYCLE LAW** `fundCycle_d`: `d₂(fundCycle) = 0`, proved by the
  twelve-term edge cancellation — every tetrahedron edge appears in
  exactly two faces with opposite total sign AND the same parametrized
  singular 1-simplex (the affine coface calculus), so the six pairs
  cancel term by term;
* **THE CORRECTED SEPARATOR SHAPE** `FundSeparator`: a rational linear
  functional on the degree-2 chains, vanishing on all degree-3
  boundaries, reading `1` on the fundamental cycle — the shape the
  route correction proved FALSE at the camera cycle, restated at the
  genuinely non-bounding candidate;
* **THE CONSISTENCY RECEIPT** `no_separator_of_boundary`: if the
  fundamental cycle bounded, the corrected shape would be false — the
  shape lives exactly as long as the cycle is non-bounding.

THE FROZEN NEXT WAVE (not claimed here): the realization
`exists_nonzero_sphere_cohomology_two_of_fundseparator` — every
separator is a cocycle of the dual complex whose class is nonzero (a
coboundary vanishes on every cycle, so it cannot read `1` on
`fundCycle`) — the NZC-2/NZC-3/NZC-4 seams of `GSTSphereNonzeroClass`,
re-pointed at the corrected cycle.  The classical completion of the
whole fence is §10 of the paper (the ∂Δ³ computation).

HONESTY LEDGER. Every statement here is unconditional. No `sorry`, no
new axioms, no `native_decide`. The GitHub CI lane
`gst-sphere-fence-discharge.yml` owns the kernel check (Ladder 5/5).
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereTetrahedronCycle
open GSTSphereNonzeroClass

namespace GSTSphereFundamentalCycle

/-! ## §1 The face data of the alternating tetrahedron -/

/-- The j-th vertex of the i-th face: the tetrahedron vertex
`succAbove i j` (the increasing enumeration of the three vertices other
than `i`). -/
def faceVert (i : Fin 4) (j : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  tetraW (i.succAbove j)

/-- The affine barycentric parametrization of the i-th closed face. -/
def tetraFaceBary (i : Fin 4) :
    stdSimplex ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∑ j, (x : Fin 3 → ℝ) j • faceVert i j

/-- The barycentric parametrization at a vertex is that face vertex. -/
theorem tetraFaceBary_vertex (i : Fin 4) (m : Fin 3) :
    tetraFaceBary i (stdSimplex.vertex (S := ℝ) m) = faceVert i m := by
  unfold tetraFaceBary
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _hj him
    have hzero : ((stdSimplex.vertex (S := ℝ) m : Fin 3 → ℝ)) j = 0 := by
      simp [stdSimplex.vertex, him]
    rw [hzero, zero_smul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- The barycentric parametrization of a face is continuous. -/
theorem tetraFaceBary_continuous (i : Fin 4) :
    Continuous (tetraFaceBary i) := by
  have hcoe : Continuous fun x : stdSimplex ℝ (Fin 3) => (x : Fin 3 → ℝ) :=
    continuous_induced_dom
  have hterm : ∀ j : Fin 3,
      Continuous fun x : stdSimplex ℝ (Fin 3) =>
        ((x : Fin 3 → ℝ) j : ℝ) • (tetraW (i.succAbove j) :
          EuclideanSpace ℝ (Fin 3)) := by
    intro j
    have hap : Continuous fun x : stdSimplex ℝ (Fin 3) =>
        ((x : Fin 3 → ℝ) j : ℝ) :=
      (continuous_apply j).comp hcoe
    exact hap.smul continuous_const
  exact continuous_finsetSum _ fun j _ => hterm j

/-! ## §2 The rank-three nonvanishing (the center misses every face) -/

/-- **THE FACE-VERTICES ARE INDEPENDENT.**  Every three of the four
alternating tetrahedron vertices are linearly independent (the 3×3
coordinate matrix of each face is a ±1 matrix with determinant ±4). -/
theorem face_indep (i : Fin 4) (μ : Fin 3 → ℝ)
    (h : ∑ j, μ j • faceVert i j = 0) : ∀ j, μ j = 0 := by
  -- the three coordinate readings of the sum:
  have hread : ∀ k : Fin 3,
      ∑ j, μ j * ((faceVert i j : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) k = 0 := by
    intro k
    exact congrArg
      (fun v : EuclideanSpace ℝ (Fin 3) => ((v : Fin 3 → ℝ)) k) h
  fin_cases i
  · -- face 0 = [w₁, w₂, w₃] = (1,-1,-1), (-1,1,-1), (-1,-1,1)
    have h0 := hread 0
    have h1 := hread 1
    have h2 := hread 2
    simp [Fin.sum_univ_three, faceVert, Fin.succAbove, tetraW,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two] at h0 h1 h2
    have keys : μ 0 = 0 ∧ μ 1 = 0 ∧ μ 2 = 0 := ⟨by linarith, by linarith, by linarith⟩
    intro j; fin_cases j
    · exact keys.1
    · exact keys.2.1
    · exact keys.2.2
  · -- face 1 = [w₀, w₂, w₃] = (1,1,1), (-1,1,-1), (-1,-1,1)
    have h0 := hread 0
    have h1 := hread 1
    have h2 := hread 2
    simp [Fin.sum_univ_three, faceVert, Fin.succAbove, tetraW,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two] at h0 h1 h2
    have keys : μ 0 = 0 ∧ μ 1 = 0 ∧ μ 2 = 0 := ⟨by linarith, by linarith, by linarith⟩
    intro j; fin_cases j
    · exact keys.1
    · exact keys.2.1
    · exact keys.2.2
  · -- face 2 = [w₀, w₁, w₃] = (1,1,1), (1,-1,-1), (-1,-1,1)
    have h0 := hread 0
    have h1 := hread 1
    have h2 := hread 2
    simp [Fin.sum_univ_three, faceVert, Fin.succAbove, tetraW,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two] at h0 h1 h2
    have keys : μ 0 = 0 ∧ μ 1 = 0 ∧ μ 2 = 0 := ⟨by linarith, by linarith, by linarith⟩
    intro j; fin_cases j
    · exact keys.1
    · exact keys.2.1
    · exact keys.2.2
  · -- face 3 = [w₀, w₁, w₂] = (1,1,1), (1,-1,-1), (-1,1,-1)
    have h0 := hread 0
    have h1 := hread 1
    have h2 := hread 2
    simp [Fin.sum_univ_three, faceVert, Fin.succAbove, tetraW, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
    have keys : μ 0 = 0 ∧ μ 1 = 0 ∧ μ 2 = 0 := ⟨by linarith, by linarith, by linarith⟩
    intro j; fin_cases j
    · exact keys.1
    · exact keys.2.1
    · exact keys.2.2

/-- **THE CENTER MISSES EVERY FACE.**  The barycentric image of any
point of the i-th closed face is nonzero — the origin (the tetrahedron
barycenter) is interior, and independence of the face vertices forces
every convex combination on the face to be nonzero. -/
theorem tetraFaceBary_ne_zero (i : Fin 4) (x : stdSimplex ℝ (Fin 3)) :
    tetraFaceBary i x ≠ 0 := by
  obtain ⟨hnonneg, hsumone⟩ :
      (∀ j, 0 ≤ (x : Fin 3 → ℝ) j) ∧ ∑ j, (x : Fin 3 → ℝ) j = 1 := x.2
  intro h
  have hzero : ∀ j, (x : Fin 3 → ℝ) j = 0 :=
    face_indep i (x : Fin 3 → ℝ) h
  have hsum : ∑ j, (x : Fin 3 → ℝ) j = 0 := by
    simp [hzero]
  rw [hsum] at hsumone
  exact zero_ne_one hsumone

/-! ## §3 The center-radial face maps -/

/-- The center-radial map of the i-th face into the sphere. -/
def faceMap (i : Fin 4) : stdSimplex ℝ (Fin 3) → unitSphereType :=
  fun x => sphereNormalize (tetraFaceBary_ne_zero i x)

/-- `sphereNormalize` depends only on the vector, not the nonvanishing
proof. -/
theorem sphereNormalize_eq_of_eq {y y' : EuclideanSpace ℝ (Fin 3)}
    (hy : y ≠ 0) (hy' : y' ≠ 0) (h : y = y') :
    sphereNormalize hy = sphereNormalize hy' := by
  subst h
  rfl

/-- The center-radial face map is continuous (the staged composition —
the wave-10-B-REPAIR-IV discipline: the composition is pinned by named
arguments, nothing left to capture). -/
theorem faceMap_continuous (i : Fin 4) : Continuous (faceMap i) := by
  have hco : Continuous fun x : stdSimplex ℝ (Fin 3) =>
      ((‖tetraFaceBary i x‖⁻¹ : ℝ) • tetraFaceBary i x :
        EuclideanSpace ℝ (Fin 3)) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    have hg : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) =>
        (‖y‖⁻¹ : ℝ) • y) (tetraFaceBary i x₀) :=
      continuousAt_sphereNormalize (tetraFaceBary_ne_zero i x₀)
    have hf : ContinuousAt (tetraFaceBary i) x₀ :=
      (tetraFaceBary_continuous i).continuousAt
    exact ContinuousAt.comp
      (f := tetraFaceBary i) (x := x₀) hg hf
  exact Continuous.subtype_mk hco _

/-- The center-radial face map as a singular 2-simplex of the sphere. -/
def faceSimplex (i : Fin 4) : C(stdSimplex ℝ (Fin 3), TopCat.of unitSphereType) :=
  ⟨faceMap i, faceMap_continuous i⟩

/-! ## §4 The affine coface calculus -/

/-- **THE COFACE FORMULA.**  The barycentric image of a coface-
precomposed point is the two-vertex combination with the same weights
at the composite vertices (the fiber-sum reading of the pinned
`stdSimplex.map`). -/
theorem faceBary_coface (i : Fin 4) (k : Fin 3) (z : stdSimplex ℝ (Fin 2)) :
    tetraFaceBary i (stdSimplex.map (Fin.succAbove k) z) =
      ∑ j : Fin 2, ((z : Fin 2 → ℝ) j) • tetraW (i.succAbove (k.succAbove j)) := by
  -- the coordinates of the pushed-forward point are the fiber sums:
  have hcoord : ∀ m : Fin 3,
      ((stdSimplex.map (Fin.succAbove k) z : Fin 3 → ℝ) m)
        = ∑ j : Fin 2, (if k.succAbove j = m then ((z : Fin 2 → ℝ) j) else 0) := by
    intro m
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  calc tetraFaceBary i (stdSimplex.map (Fin.succAbove k) z)
      = ∑ m : Fin 3, ((stdSimplex.map (Fin.succAbove k) z : Fin 3 → ℝ) m) •
          tetraW (i.succAbove m) := rfl
    _ = ∑ m : Fin 3, (∑ j : Fin 2,
          (if k.succAbove j = m then ((z : Fin 2 → ℝ) j) else 0)) •
          tetraW (i.succAbove m) := by
        exact Finset.sum_congr rfl fun m _ => by rw [hcoord m]
    _ = ∑ m : Fin 3, ∑ j : Fin 2,
          ((if k.succAbove j = m then ((z : Fin 2 → ℝ) j) else 0)) •
          tetraW (i.succAbove m) := by
        exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_smul]
    _ = ∑ j : Fin 2, ∑ m : Fin 3,
          ((if k.succAbove j = m then ((z : Fin 2 → ℝ) j) else 0)) •
          tetraW (i.succAbove m) := Finset.sum_comm
    _ = ∑ j : Fin 2, ((z : Fin 2 → ℝ) j) •
          tetraW (i.succAbove (k.succAbove j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (k.succAbove j)]
        · rw [if_pos rfl]
        · intro m _hm hne
          rw [if_neg (fun hh => hne hh.symm), zero_smul]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem

/-- **THE EDGE-PAIRING EQUALITY.**  If two face-coface composites visit
the same tetrahedron vertices with the same weights, the resulting
singular 1-simplices of the sphere are equal. -/
theorem edgeSimplex_eq (i : Fin 4) (k : Fin 3) (i' : Fin 4) (k' : Fin 3)
    (hvert : ∀ j : Fin 2,
      i.succAbove (k.succAbove j) = i'.succAbove (k'.succAbove j)) :
    (TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k
        (twoSimplexInject (faceSimplex i)) =
      (TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k'
        (twoSimplexInject (faceSimplex i')) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
    (Opposite.op (SimplexCategory.mk 1))).injective
  refine ContinuousMap.ext (fun z => ?_)
  rw [toSSetObj₂_face (faceSimplex i) k z, toSSetObj₂_face (faceSimplex i') k' z]
  -- the two C-applications reduce to the raw face values (the
  -- green `tetraFace_vertex_zero` show-pattern, one layer at a time):
  show faceMap i ((stdFace k) z) = faceMap i' ((stdFace k') z)
  show faceMap i (stdSimplex.map (Fin.succAbove k) z)
      = faceMap i' (stdSimplex.map (Fin.succAbove k') z)
  exact sphereNormalize_eq_of_eq _ _
    (by rw [faceBary_coface i k z, faceBary_coface i' k' z]
        exact Finset.sum_congr rfl fun j _ => by rw [hvert j])

/-! ## §5 The fundamental cycle and the twelve-term cancellation -/

/-- The singular 2-chain carried by the i-th center-radial face. -/
def faceChain (i : Fin 4) :
    (singularChainsOf (TopCat.of unitSphereType)).X 2 :=
  (((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
      (twoSimplexInject (faceSimplex i)) :
      ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 2)).hom
    (1 : ℚ)

/-- The singular 1-chain carried by the (i,k)-th edge. -/
def edgeChain (i : Fin 4) (k : Fin 3) :
    (singularChainsOf (TopCat.of unitSphereType)).X 1 :=
  (((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
      ((TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k
        (twoSimplexInject (faceSimplex i))) :
      ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 1)).hom
    (1 : ℚ)

/-- **THE CHAIN-LEVEL PAIRING.**  Equal edge simplices give equal edge
chains. -/
theorem edgeChain_pair (i : Fin 4) (k : Fin 3) (i' : Fin 4) (k' : Fin 3)
    (hvert : ∀ j : Fin 2,
      i.succAbove (k.succAbove j) = i'.succAbove (k'.succAbove j)) :
    edgeChain i k = edgeChain i' k' := by
  unfold edgeChain
  rw [edgeSimplex_eq i k i' k' hvert]

/-- **THE BOUNDARY OF A FACE CHAIN.**  The alternating sum of its three
edges (the pinned `ιChainComplex_d` at degree two, read at the
element). -/
theorem faceChain_d (i : Fin 4) :
    ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
        (faceChain i) =
      edgeChain i 0 - edgeChain i 1 + edgeChain i 2 := by
  have hgen : (((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
      (twoSimplexInject (faceSimplex i)) :
      ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 2) ≫
      (singularChainsOf (TopCat.of unitSphereType)).d 2 1) =
      ∑ k : Fin (1 + 2), (-1 : ℤ) ^ (k : ℕ) •
        (TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
          ((TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k
            (twoSimplexInject (faceSimplex i))) :=
    (TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex_d
      (ModuleCat.of ℚ ℚ) (twoSimplexInject (faceSimplex i))
  rw [Fin.sum_univ_three] at hgen
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Fin.val_two, pow_two, neg_mul_neg, one_mul] at hgen
  -- the element-level reading of hgen at the value 1:
  have e2 := congrArg
    (fun u : ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 1 =>
      ModuleCat.Hom.hom u (1 : ℚ)) hgen
  -- the composite-hom application bridge:
  have e1 : ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (faceChain i) =
    ModuleCat.Hom.hom
      ((((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
        (twoSimplexInject (faceSimplex i)) :
        ModuleCat.of ℚ ℚ ⟶ (singularChainsOf (TopCat.of unitSphereType)).X 2) ≫
        (singularChainsOf (TopCat.of unitSphereType)).d 2 1)) (1 : ℚ) := rfl
  rw [e1, hgen]
  -- the hom-sum distribution, by the pin's rfl-lemmas as explicit rewrites:
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_neg,
    LinearMap.neg_apply, sub_eq_add_neg]
  unfold edgeChain
  rfl


/-- The six vertex-pairing facts (each tetrahedron edge, read through
the two faces containing it, visits the same vertices in the same
order). -/
theorem hvert_10_00 : ∀ j : Fin 2,
    (1 : Fin 4).succAbove ((0 : Fin 3).succAbove j)
      = (0 : Fin 4).succAbove ((0 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

theorem hvert_20_01 : ∀ j : Fin 2,
    (2 : Fin 4).succAbove ((0 : Fin 3).succAbove j)
      = (0 : Fin 4).succAbove ((1 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

theorem hvert_30_02 : ∀ j : Fin 2,
    (3 : Fin 4).succAbove ((0 : Fin 3).succAbove j)
      = (0 : Fin 4).succAbove ((2 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

theorem hvert_21_11 : ∀ j : Fin 2,
    (2 : Fin 4).succAbove ((1 : Fin 3).succAbove j)
      = (1 : Fin 4).succAbove ((1 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

theorem hvert_31_12 : ∀ j : Fin 2,
    (3 : Fin 4).succAbove ((1 : Fin 3).succAbove j)
      = (1 : Fin 4).succAbove ((2 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

theorem hvert_32_22 : ∀ j : Fin 2,
    (3 : Fin 4).succAbove ((2 : Fin 3).succAbove j)
      = (2 : Fin 4).succAbove ((2 : Fin 3).succAbove j) := by
  intro j; fin_cases j <;> decide

/-- **THE CENTER-RADIAL FUNDAMENTAL 2-CYCLE.**  The alternating sum of
the four center-radial face chains — the classical generator of
H₂(S²; ℚ), the corrected FENCE-Ω witness candidate. -/
def fundCycle : (singularChainsOf (TopCat.of unitSphereType)).X 2 :=
  faceChain 0 - faceChain 1 + faceChain 2 - faceChain 3

/-- **THE CYCLE LAW.**  `d₂(fundCycle) = 0` — the twelve-term edge
cancellation: each of the six tetrahedron edges appears in exactly two
faces, with opposite total sign and the same parametrized singular
1-simplex (the affine coface calculus of §4), so the six pairs cancel
term by term. -/
theorem fundCycle_d :
    ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
        fundCycle = 0 := by
  unfold fundCycle
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [faceChain_d 0, faceChain_d 1, faceChain_d 2, faceChain_d 3]
  rw [edgeChain_pair 1 0 0 0 hvert_10_00,
      edgeChain_pair 2 0 0 1 hvert_20_01,
      edgeChain_pair 3 0 0 2 hvert_30_02,
      edgeChain_pair 2 1 1 1 hvert_21_11,
      edgeChain_pair 3 1 1 2 hvert_31_12,
      edgeChain_pair 3 2 2 2 hvert_32_22]
  abel

/-! ## §6 The corrected separator shape -/

/-- **THE CORRECTED SEPARATOR SHAPE.**  A rational linear functional on
the degree-2 singular chains of the sphere that vanishes on every
degree-3 boundary and reads `1` on the fundamental cycle.  This is the
shape the route correction proved FALSE at the camera cycle, restated
at the genuinely non-bounding candidate. -/
def FundSeparator : Prop :=
  ∃ φ : sphereChainsTwo →ₗ[ℚ] ℚ,
    (∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) ∧
    φ fundCycle = 1

/-- **THE CONSISTENCY RECEIPT.**  If the fundamental cycle bounded, the
corrected separator shape would be false — the shape lives exactly as
long as the cycle is non-bounding.  (The positive direction — the shape
holds when the cycle is non-bounding, by extension of the degree-one
functional on the line it spans, modulo the boundary submodule — is the
frozen next wave.) -/
theorem no_separator_of_boundary (w : sphereChainsThree)
    (hw : sphereBoundaryThree w = fundCycle) :
    ¬ FundSeparator := by
  rintro ⟨φ, hvan, hone⟩
  have h0 : φ (sphereBoundaryThree w) = 0 := hvan w
  rw [hw] at h0
  exact zero_ne_one (h0.symm.trans hone)

/-! ## The frozen next wave (not claimed here)

**THE REALIZATION** (the NZC-2/NZC-3/NZC-4 seams of
`GSTSphereNonzeroClass.lean`, re-pointed at the corrected cycle):

```
theorem exists_nonzero_sphere_cohomology_two_of_fundseparator
    (hsep : FundSeparator) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0
```

Every separator is a cocycle of the honest sphere's rational singular
cochain complex (the boundary-vanishing is the cocycle law of the
`linearYonedaObj` dual differential), and its cohomology class is
NONZERO: a coboundary `ψ ∘ d₂` reads `ψ (d₂ fundCycle) = ψ 0 = 0` on
the cycle (by `fundCycle_d`), so it cannot be the separator that reads
`1`.  The classical completion of the whole fence — H₂(S²; ℚ) ≅ ℚ by
the ∂Δ³ computation, the two stashed sectors (weight-one spanning at a
nonzero index, higher-weight vanishing) — is §10 of the paper. -/

/-! ## Receipts -/

#check faceVert
#check tetraFaceBary
#check tetraFaceBary_vertex
#check tetraFaceBary_continuous
#check face_indep
#check tetraFaceBary_ne_zero
#check faceMap
#check faceMap_continuous
#check faceSimplex
#check faceBary_coface
#check edgeSimplex_eq
#check faceChain
#check edgeChain
#check edgeChain_pair
#check faceChain_d
#check fundCycle
#check fundCycle_d
#check FundSeparator
#check no_separator_of_boundary

#print axioms face_indep
#print axioms tetraFaceBary_ne_zero
#print axioms faceMap_continuous
#print axioms faceBary_coface
#print axioms edgeSimplex_eq
#print axioms faceChain_d
#print axioms fundCycle_d
#print axioms no_separator_of_boundary

end GSTSphereFundamentalCycle

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (FC-1) THE COORDINATE READINGS of `face_indep`: the PiLp coercion of
  a `Finset.sum` distributes by `Finset.sum_apply` + `PiLp.smul_apply`
  at default transparency (the green `tetraBary` hsum pattern,
  `GSTSphereTetrahedronCycle.lean:156`); if the pin's WithLp opacity
  blocks the coercion-of-sum, restage as three explicit congrArg steps
  per coordinate.
* (FC-2) THE SUCCABOVE LITERALS: the twelve `s0`/`s1`/`s2` haves and
  the six `hvert_*` tables close by `decide` on closed `Fin`
  equalities (kernel-cheap, NO-OOM-safe); if `decide` stalls on the
  `succAbove` unfolding, replace with `Fin.succAbove_of_le_castSucc` /
  `Fin.succAbove_of_castSucc_lt` + `Fin.val_*` + `omega`.
* (FC-3) `faceBary_coface`: the fiber-sum reading is
  `stdSimplex.map_coe` + `FunOnFinite.linearMap_apply_apply` +
  `Finset.sum_filter` (the pinned def, `StdSimplex.lean:317` verified);
  the collapse is `Finset.sum_eq_single` (the green `tetraBary_vertex`
  pattern); the scalar-smul distribution is `Finset.sum_smul`.
* (FC-4) `faceChain_d`: the boundary formula is the pinned
  `ιChainComplex_d (ModuleCat.of ℚ ℚ)` (the green `ιPath_d` spelling at
  degree two); the coefficient normalization set is
  `[Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
  Fin.val_two, pow_two, neg_mul_neg, one_mul]`; the element-level
  bridge is the green `d_path_element` congrArg pattern
  (`ModuleCat.hom_comp` + `LinearMap.comp_apply` + `ModuleCat.hom_add`/
  `hom_sub` + the apply lemmas).
* (FC-5) `fundCycle_d`: the distribution is `LinearMap.map_sub` /
  `LinearMap.map_add`; the regroup closes by `abel` after the six
  pairing rewrites (the six `hvert_*` facts, all `decide`-verified).
* (FC-6) `edgeSimplex_eq`: the injectivity is `Equiv.injective` on
  `toSSetObjEquiv` at `[1]`; the face formula is the green
  `toSSetObj₂_face`; the value equality is `sphereNormalize_eq_of_eq`
  (proof-irrelevance at the subtype).
-/
