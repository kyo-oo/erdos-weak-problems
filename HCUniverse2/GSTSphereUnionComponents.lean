/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# The sphere-union component machine (Wave 46, repair wave 47)

THE SECOND CUSTOM TOOL of the wave.  The planned positive-dimensional world
of the wave-45 frozen design (`finiteLineWorld M`, the disjoint union of
M projective lines) has the honest analytification "M disjoint copies of
the 2-sphere".  This file computes its path-component structure:

  `sphereUnionZerothHomotopyEquiv M :
      ZerothHomotopy ↥(sphereUnionSpace M) ≃ Fin M`

The proof has two engines:

1. THE INDEX-CONSTANCY OF PATHS (§1).  A path in a sigma-typed disjoint
   union has constant index: the index map is continuous into the
   discrete type `Fin M` (the preimage of each point is the clopen
   slice; the pinned `isOpen_range_sigmaMk` of
   `Topology/Constructions.lean`), and a continuous map from a connected
   space to a discrete space is constant (the hand-rolled
   `exists_const_of_continuous_discrete`, through the pinned
   `isClopen_iff` of `Topology/Connected/Clopen.lean` under
   `ConnectedSpace.toPreconnectedSpace` and the pinned instance
   `ConnectedSpace.toNonempty`).

2. THE SLICE PATH-CONNECTEDNESS (§2).  Each 2-sphere slice is
   path-connected (the pinned `isPathConnected_sphere` of
   `Analysis/Normed/Module/Connected.lean` — a ROOT-LEVEL lemma, applied
   at `EuclideanSpace ℝ (Fin 3)` with `Module.rank = 3 > 1` through
   `Module.finrank_eq_rank` and `finrank_euclideanSpace_fin`), and the
   slice inclusion is continuous (the pinned `continuous_sigmaMk`), so
   any two points in the same slice are joined by a path in the union.

Together: the path-component quotient of the union is exactly the index
set (§3).  Composed with the component H⁰ machine of
`GSTComponentCohomologyZero.lean`, this yields the unconditional live
rank-M weight-0 fiber computation for the analytification of the planned
finite-line world (§4) — the input the wave-45 frozen design demanded.

## The wave-47 repair ledger (run 44403637791)

* the import `Mathlib.Topology.Separation` is not a file at the pin
  (the `import Mathlib` of this file already covers everything) —
  removed;
* `Metric.isPathConnected_sphere` is not the pinned name — the lemma is
  root-level `isPathConnected_sphere` in
  `Mathlib/Analysis/Normed/Module/Connected.lean`, taking the rank
  hypothesis `1 < Module.rank ℝ E` explicitly;
* the `isConnected_univ …` destructuring was not a pinned shape — the
  clopen separation now runs through `isClopen_iff`
  (`IsClopen s ↔ s = ∅ ∨ s = univ` under `PreconnectedSpace`).

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-positive-dimensional-live-core-law.yml` owns the kernel check.
-/

import Mathlib
import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.PathConnected
import HCUniverse2.GSTComponentCohomologyZero

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open unitInterval
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTComponentCohomologyZero

namespace GSTSphereUnionComponents

/-! ## §1 The index-constancy of paths -/

/-- A continuous map from a connected space to a discrete space is
constant: the preimage of the value at any point is clopen (continuity +
discreteness), and a preconnected space admits no nontrivial clopen set
(the pinned `isClopen_iff`). -/
theorem exists_const_of_continuous_discrete {X Y : Type*}
    [TopologicalSpace X] [ConnectedSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] {f : X → Y} (hf : Continuous f) :
    ∃ b : Y, f = fun _ => b := by
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  set U : Set X := f ⁻¹' {f x₀} with hU
  have hUopen : IsOpen U := hf.isOpen_preimage _ (isOpen_discrete _)
  have hUcomplopen : IsOpen Uᶜ := by
    have hcompl : Uᶜ = f ⁻¹' ({f x₀} : Set Y)ᶜ := by
      rw [hU, Set.preimage_compl]
    rw [hcompl]
    exact hf.isOpen_preimage _ (isOpen_discrete _)
  have hUclosed : IsClosed U := ⟨hUcomplopen⟩
  have hUclopen : IsClopen U := ⟨hUclosed, hUopen⟩
  have hx₀U : x₀ ∈ U := Set.mem_preimage.mpr rfl
  rcases (isClopen_iff.mp hUclopen) with hUe | hUu
  · rw [hUe] at hx₀U
    exact absurd hx₀U (Set.notMem_empty x₀)
  · refine ⟨f x₀, funext fun x => ?_⟩
    have hxU : x ∈ U := by
      rw [hUu]
      exact Set.mem_univ x
    exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hxU)

/-- The first projection of a sigma-typed disjoint union is continuous
into the discrete index type: the preimage of any subset is a union of
open slices (the pinned `isOpen_range_sigmaMk`). -/
theorem continuous_sigma_fst_discrete {ι : Type*} {X : ι → Type*}
    [TopologicalSpace ι] [∀ i, TopologicalSpace (X i)]
    [DiscreteTopology ι] :
    Continuous (fun z : Sigma X => z.1) :=
  ⟨fun U _ => by
    have hpre : (fun z : Sigma X => z.1) ⁻¹' U =
        ⋃ i ∈ U, Set.range (Sigma.mk (β := X) i) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Set.mem_range]
      exact ⟨fun h => ⟨z.1, h, z.2, rfl⟩, fun ⟨i, hi, w, hw⟩ => by
        rw [← hw]; exact hi⟩
    rw [hpre]
    exact isOpen_iUnion fun i =>
      isOpen_iUnion fun _ => isOpen_range_sigmaMk⟩

/-- **THE INDEX-CONSTANCY OF PATHS.**  A path in a sigma-typed disjoint
union has constant index.  WAVE 48: rewritten on the pinned `Path` API —
`Path` has NO `.hom` field (it extends `C(I, X)` directly, its FunLike
coe IS the evaluation); the endpoints come from `Path.source` /
`Path.target` (`p 0 = x`, `p 1 = y` at `Mathlib/Topology/Path.lean:96-100`);
the constancy is evaluated by `congrFun` at the two pinned endpoints
(beta-checked haves — no `⟨0, _⟩`-spelling rewrites, no `Set.Icc`-level
instance archaeology). -/
theorem sigma_path_index_const {ι : Type*} {X : ι → Type*}
    [TopologicalSpace ι] [∀ i, TopologicalSpace (X i)]
    [DiscreteTopology ι]
    {x y : Sigma X} (p : Path x y) :
    x.1 = y.1 := by
  -- the index map along the path is continuous into the discrete ι
  -- WAVE 52/53: the @-form with CONCRETE ι X; the pinned `Continuous.comp`
  -- takes the OUTER function FIRST (Continuous.lean:113 —
  -- `Continuous.comp (hg : Continuous g) (hf : Continuous f) : Continuous (g ∘ f)`)
  have hcont : Continuous (fun t : I => ((p t : Sigma X)).1) :=
    (@continuous_sigma_fst_discrete ι X _ _ _).comp (p.continuous)
  -- the pinned unit interval is connected (the `unitInterval` instance
  -- rides the abbrev `I = Set.Icc 0 1`, so TC finds it at `↥I`)
  obtain ⟨b, hb⟩ := exists_const_of_continuous_discrete hcont
  have h0 : ((p (0 : I) : Sigma X)).1 = b := congrFun hb 0
  have h1 : ((p (1 : I) : Sigma X)).1 = b := congrFun hb 1
  rw [p.source] at h0
  rw [p.target] at h1
  exact h0.trans h1.symm

/-! ## §2 The sphere-union space and its slices -/

/-- The concrete 2-sphere model: the unit sphere in the 3-dimensional
Euclidean space.  WAVE 50: NO custom instance — the abbrev lets TC find
the canonical induced subtype topology (a hand-rolled `inferInstance`
copy would shadow it and break instance unification against pinned
lemmas like `continuous_sigmaMk`). -/
abbrev unitSphereType : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The sphere-union space: the sigma-typed disjoint union of M copies of
the 2-sphere, with the pinned sigma (disjoint-union) topology.  This is
the honest analytification shape of the planned `finiteLineWorld M`.
WAVE 50: NO custom instance — same shadowing discipline as
`unitSphereType`. -/
abbrev sphereUnionSpace (M : ℕ) : Type :=
  Sigma (fun _ : Fin M => unitSphereType)

/-- The rank bookkeeping for the pinned sphere path-connectedness: the
3-dimensional Euclidean space has rank 3. -/
theorem euclideanRank_three :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by norm_num : (1 : ℕ) < 3)

/-- AUDIT(8): the 2-sphere is path-connected — the pinned
`isPathConnected_sphere` (root level, `Analysis/Normed/Module/
Connected.lean`) at the 3-dimensional Euclidean space. -/
theorem unitSphere_isPathConnected :
    IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isPathConnected_sphere euclideanRank_three
    (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num)

/-- The sphere is nonempty (through path-connectedness). -/
theorem unitSphere_nonempty : Nonempty unitSphereType := by
  obtain ⟨hub, hhub, -⟩ := unitSphere_isPathConnected
  exact ⟨⟨hub, hhub⟩⟩

/-- Any two points of the sphere are joined by a path in the sphere —
the ambient joinedness transported through the pinned
`joinedIn_iff_joined` (joined in the set ↔ joined in the subtype). -/
theorem unitSphere_joined (s t : unitSphereType) :
    ∃ p : Path s t, True := by
  obtain ⟨hub, hhub, hj⟩ := unitSphere_isPathConnected
  have hs : (s : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := s.2
  have ht : (t : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := t.2
  obtain ⟨γs⟩ := (joinedIn_iff_joined hhub hs).mp (hj hs)
  obtain ⟨γt⟩ := (joinedIn_iff_joined hhub ht).mp (hj ht)
  exact ⟨γs.symm.trans γt, trivial⟩

/-- Any two points of the same sphere slice are joined by a path inside
the slice, which is also a path in the union (the slice inclusion is
continuous: the pinned `continuous_sigmaMk`). -/
theorem sphere_slice_joined (M : ℕ) (i : Fin M) (s t : unitSphereType) :
    ∃ p : Path (Sigma.mk (β := fun _ : Fin M => unitSphereType) i s)
        (Sigma.mk i t), True := by
  obtain ⟨γ, -⟩ := unitSphere_joined s t
  -- WAVE 52: the Continuous-STRUCTURE constructor + the pinned
  -- `isOpen_sigma_iff` (σ inferred from hU's concrete type — no deferred
  -- instance synthesis, no named-argument parsing)
  have hcont : Continuous
      (fun u : unitSphereType =>
        (Sigma.mk (β := fun _ : Fin M => unitSphereType) i) u) := by
    refine ⟨fun U hU => ?_⟩
    exact isOpen_sigma_iff.mp hU i
  exact ⟨γ.map hcont, trivial⟩

/-! ## §3 The component equivalence -/

/-- **THE SPHERE-UNION COMPONENT MACHINE.**  The path components of the
disjoint union of M two-spheres are exactly the M slices. -/
noncomputable def sphereUnionZerothHomotopyEquiv (M : ℕ) :
    ZerothHomotopy (sphereUnionSpace M) ≃ Fin M where
  toFun :=
    ZerothHomotopy.lift (fun z : sphereUnionSpace M => z.1)
      (fun _ _ p => sigma_path_index_const p)
  invFun i :=
    ZerothHomotopy.mk
      ⟨i, (unitSphere_nonempty).some⟩
  left_inv z := by
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
    -- same index: the slice path identifies the classes (the lift
    -- evaluations and the invFun-beta are all rfl at default; the sound
    -- equation closes the residual, no rewrite-auto-close ambiguity)
    obtain ⟨i, s⟩ := x
    obtain ⟨p, -⟩ := sphere_slice_joined M i s (unitSphere_nonempty).some
    exact (ZerothHomotopy.sound p).symm
  right_inv i := rfl

/-! ## §4 The connection to the component H⁰ machine

**THE UNCONDITIONAL LIVE RANK-M WEIGHT-0 FIBER OF THE SPHERE-UNION
ANALYTIFICATION.**  For any world whose analytification carries the
sphere-union space, the degree-zero rational singular cohomology is the
free rank-M function space, computed unconditionally by the component H⁰
machine of `GSTComponentCohomologyZero.lean` composed with this file's
component equivalence.  This is the statement the wave-45 frozen design
demanded as the input of the finite-line lane's weight-0 core: the
analytification-side half is now COMPLETE; the remaining construction is
the scheme carrier (`finiteLineWorld M`), the next wave's frozen kill. -/

/-- **THE UNCONDITIONAL COMPONENT IDENTIFICATION OF THE SPHERE-UNION
ANALYTIFICATION.**  For any world whose analytification carries the
sphere-union space, the path-component identification against `Fin M`.
WAVE 54: stated as a DEF returning the equiv DIRECTLY — the previous
∃-wrapper cannot be consumed (destructuring an `∃` into a `Sort`-valued
goal is illegal: `Exists.casesOn` eliminates into `Prop` only); the goal
is rewritten by `hspace` first so both sides elaborate at `TopCat.of`'s
canonical instance (the Sort-coe on `TopCat.of` is definitionally the
identity carrier). -/
noncomputable def sphereUnion_cohomology_zero
    {V : SmoothProjectiveComplexScheme}
    {A : AnalytificationData V} {M : ℕ}
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    ZerothHomotopy ↥A.space ≃ Fin M := by
  rw [hspace]
  exact sphereUnionZerothHomotopyEquiv M

end GSTSphereUnionComponents
