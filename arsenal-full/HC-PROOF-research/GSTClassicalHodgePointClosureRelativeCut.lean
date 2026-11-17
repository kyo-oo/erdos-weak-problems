import GSTClassicalHodgePointClosureIrreducible
import GSTClassicalHodgeProperCutCodimensionOne

/-!
# GST CLASSICAL HODGE — RELATIVE CODIMENSION-ONE SUCCESSORS

For an arbitrary generic point `x`, the reduced closure scheme of `x` is an
irreducible Noetherian carrier.  The source-specific principal section cuts
this closure by pullback.  The lifted generic point is not contained in the
cut because its ambient image is exactly `x`, while the chosen separator was
constructed to avoid `x`.

Therefore the cut is a proper closed subset of the irreducible point closure.
The pinned topological Krull theorem then makes its relative coheight-one locus
finite.  These points are the recursive codimension-successor candidates from
which the graded native cut operator is assembled.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgeProperCutCodimensionOne

namespace GSTClassicalHodgePointClosureRelativeCut

/-- Closed subset of the point-closure carrier swept out by the restricted
principal cut. -/
def relativeCutSet
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Set (pointClosureScheme V x) :=
  Set.range (closurePrincipalCutToClosure V x)

/-- The relative cut is closed. -/
theorem relativeCutSet_isClosed
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosed (relativeCutSet V x) := by
  exact (closurePrincipalCutToClosure V x).isClosedEmbedding.isClosed_range

/-- The lifted generic point of the closure is not contained in the restricted
principal cut. -/
theorem closureGenericPoint_not_mem_relativeCut
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    closureGenericPoint V x ∉ relativeCutSet V x := by
  rintro ⟨z, hz⟩
  have hamb :
      principalSectionAtι V x (closurePrincipalCutToSection V x z) = x := by
    have hcond := congrArg (fun f => f z)
      (closurePrincipalCut_condition V x)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz,
      closureGenericPoint_maps_to_source V x] at hcond
    exact hcond.symm
  have hxrange : x ∈ Set.range (principalSectionAtι V x) :=
    ⟨closurePrincipalCutToSection V x z, hamb⟩
  have hxsupport : x ∈
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation).support := by
    exact (Scheme.IdealSheafData.range_subschemeι
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation)).subset hxrange
  exact source_not_mem_principalSection V x hxsupport

/-- The relative principal cut is genuinely proper in the point closure. -/
theorem relativeCutSet_ne_univ
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    relativeCutSet V x ≠ Set.univ := by
  intro h
  apply closureGenericPoint_not_mem_relativeCut V x
  rw [h]
  trivial

/-- The closure of the relative cut is still proper because the cut is closed. -/
theorem closure_relativeCutSet_ne_univ
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    closure (relativeCutSet V x) ≠ Set.univ := by
  rw [(relativeCutSet_isClosed V x).closure_eq]
  exact relativeCutSet_ne_univ V x

/-- The relative coheight-one successor locus is finite. -/
theorem finite_relative_coheight_one
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    {y ∈ relativeCutSet V x | Order.coheight y = 1}.Finite := by
  letI : IrreducibleSpace (pointClosureScheme V x) :=
    pointClosureIrreducibleSpace V x
  letI : IsNoetherian (pointClosureScheme V x) :=
    pointClosureIsNoetherian V x
  letI : NoetherianSpace (pointClosureScheme V x) := by infer_instance
  let C := relativeCutSet V x
  letI : QuasiSober C := Topology.IsClosedEmbedding.quasiSober
    (Topology.IsClosedEmbedding.subtypeVal (relativeCutSet_isClosed V x))
  exact TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    (closure_relativeCutSet_ne_univ V x)

/-- Finite relative successor finset. -/
noncomputable def relativeCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Finset {y : pointClosureScheme V x // Order.coheight y = 1} := by
  classical
  let s : Set (pointClosureScheme V x) :=
    {y ∈ relativeCutSet V x | Order.coheight y = 1}
  have hs : s.Finite := finite_relative_coheight_one V x
  exact hs.toFinset.attach.map
    ⟨fun y => ⟨y.1, by
        have h2 : y.1 ∈ hs.toFinset := y.2
        rw [Set.Finite.mem_toFinset] at h2
        exact (Set.mem_sep_iff.mp h2).2⟩,
      by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h⟩

/-- Relative-successor crown. -/
theorem point_closure_relative_successor_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosed (relativeCutSet V x)
      ∧ relativeCutSet V x ≠ Set.univ
      ∧ {y ∈ relativeCutSet V x | Order.coheight y = 1}.Finite := by
  exact ⟨relativeCutSet_isClosed V x,
    relativeCutSet_ne_univ V x,
    finite_relative_coheight_one V x⟩

/-! ## Target-directed cuts

The canonical relevance separator is useful for forward propagation, but its
choice need not contain a prescribed specialization. Here the equation is
instead derived from the strict inclusion of source and target projective
prime ideals. The resulting ideal sheaf defines an actual closed subscheme
inside the source closure. Every relative coheight-one point belongs to the
finite coheight-one locus of its own directed cut.

The equation below is allowed to be nonhomogeneous: `principalSectionIdeal`
uses the reduced projective zero locus and is defined for every equation.
No assertion that this is an effective Cartier divisor is needed or made.
No Hodge data, cycle-class map, or Hodge-direction preimage enters the cut.
-/

section TargetDirected

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every point in a reduced source closure lies below its generic point. -/
theorem pointClosure_le_generic
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (z : pointClosureScheme V x) :
    z ≤ closureGenericPoint V x := by
  rw [specializationOrder_iff_specializes]
  have hclosure :=
    (pointClosureι V x).isEmbedding.closure_eq_preimage_closure_image
      ({closureGenericPoint V x} : Set (pointClosureScheme V x))
  rw [Set.image_singleton, closureGenericPoint_maps_to_source] at hclosure
  rw [hclosure]
  change pointClosureι V x z ∈ closure ({x} : Set V.X)
  rw [← range_pointClosureι V x]
  exact ⟨z, rfl⟩

/-- The source closure's generic point has relative coheight zero. -/
theorem closureGenericPoint_coheight_zero
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Order.coheight (closureGenericPoint V x) = 0 := by
  apply Order.coheight_eq_zero.mpr
  intro z _hz
  exact pointClosure_le_generic V x z

/-- A strict specialization supplies an actual projective equation vanishing
at the target and not at the source. Unlike the fixed relevance separator,
this equation is chosen using both geometric points. -/
theorem exists_targetedSectionEquation
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    ∃ f : ProjectiveCoordinateRing V.projective.n,
      f ∈ (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal ∧
      f ∉ (V.projective.immersion x).asHomogeneousIdeal := by
  have prime_le_iff : ∀ a b : projectiveSpace V.projective.n,
      a ≤ b ↔ b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
    intro a b
    rw [specializationOrder_iff_specializes]
    have key : ∀ a b : ProjectiveSpectrum (ProjectiveGrading V.projective.n),
        a ∈ closure ({b} : Set (ProjectiveSpectrum (ProjectiveGrading V.projective.n))) ↔
          b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
      intro a b
      rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        ProjectiveSpectrum.vanishingIdeal_singleton]
      exact ProjectiveSpectrum.mem_zeroLocus _ _ _
    exact key a b
  have hyle : pointClosureι V x y ≤ x := by
    have h := (pointClosureι V x).continuous.specialization_monotone
      (pointClosure_le_generic V x y)
    simpa only [closureGenericPoint_maps_to_source] using h
  have hsource : (V.projective.immersion x).asHomogeneousIdeal.toIdeal ≤
      (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal.toIdeal :=
    (prime_le_iff _ _).mp
      (V.projective.immersion.continuous.specialization_monotone hyle)
  have hnot : ¬
      (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal.toIdeal ≤
        (V.projective.immersion x).asHomogeneousIdeal.toIdeal := by
    intro hreverse
    have hprojective : V.projective.immersion (pointClosureι V x y) =
        V.projective.immersion x := by
      apply ProjectiveSpectrum.ext
      exact HomogeneousIdeal.ext (le_antisymm hreverse hsource)
    letI : IsClosedImmersion V.projective.immersion := V.projective.closedImmersion
    have himage : pointClosureι V x y = x :=
      V.projective.immersion.isEmbedding.injective hprojective
    apply hy
    apply (pointClosureι V x).isEmbedding.injective
    rw [himage, closureGenericPoint_maps_to_source]
  obtain ⟨f, hf, hfn⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨f, HomogeneousIdeal.mem_iff.mp hf,
    fun hmem => hfn (HomogeneousIdeal.mem_iff.mpr hmem)⟩

/-- Equation derived from the two geometric points, with no equation input. -/
noncomputable def targetedSectionEquation
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    ProjectiveCoordinateRing V.projective.n :=
  Classical.choose (exists_targetedSectionEquation V x y hy)

theorem targetedSectionEquation_spec
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    targetedSectionEquation V x y hy ∈
        (V.projective.immersion (pointClosureι V x y)).asHomogeneousIdeal ∧
      targetedSectionEquation V x y hy ∉
        (V.projective.immersion x).asHomogeneousIdeal :=
  Classical.choose_spec (exists_targetedSectionEquation V x y hy)

/-- Ideal sheaf of the actual directed cut inside the source closure. -/
noncomputable def targetedRelativeCutIdeal
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    (pointClosureScheme V x).IdealSheafData :=
  (principalSectionIdeal V (targetedSectionEquation V x y hy)).comap
    (pointClosureι V x)

/-- Genuine closed subscheme cut out by the derived equation. -/
noncomputable def targetedRelativeCutScheme
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) : Scheme :=
  (targetedRelativeCutIdeal V x y hy).subscheme

theorem mem_targetedRelativeCut_iff
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x)
    (z : pointClosureScheme V x) :
    z ∈ (targetedRelativeCutIdeal V x y hy).support ↔
      targetedSectionEquation V x y hy ∈
        (V.projective.immersion (pointClosureι V x z)).asHomogeneousIdeal := by
  unfold targetedRelativeCutIdeal
  rw [Scheme.IdealSheafData.support_comap]
  exact mem_principalSection_support_iff V
    (targetedSectionEquation V x y hy) (pointClosureι V x z)

/-- The directed cut really contains the prescribed target point. -/
theorem target_mem_targetedRelativeCut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    y ∈ (targetedRelativeCutIdeal V x y hy).support :=
  (mem_targetedRelativeCut_iff V x y hy y).mpr
    (targetedSectionEquation_spec V x y hy).1

/-- The same cut excludes the generic source, so it is proper. -/
theorem generic_not_mem_targetedRelativeCut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    closureGenericPoint V x ∉ (targetedRelativeCutIdeal V x y hy).support := by
  intro hmem
  have hf := (mem_targetedRelativeCut_iff V x y hy _).mp hmem
  rw [closureGenericPoint_maps_to_source] at hf
  exact (targetedSectionEquation_spec V x y hy).2 hf

/-- The directed cut's relative codimension-one source locus is finite. -/
theorem finite_targetedRelativeCut_coheight_one
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    {z ∈ (targetedRelativeCutIdeal V x y hy).support |
      Order.coheight z = 1}.Finite := by
  letI : IrreducibleSpace (pointClosureScheme V x) :=
    pointClosureIrreducibleSpace V x
  letI : IsNoetherian (pointClosureScheme V x) := pointClosureIsNoetherian V x
  letI : NoetherianSpace (pointClosureScheme V x) := by infer_instance
  apply finite_coheight_one_of_proper_closed
    ((targetedRelativeCutIdeal V x y hy).support : Set (pointClosureScheme V x))
    (targetedRelativeCutIdeal V x y hy).support.isClosed
  intro hall
  apply generic_not_mem_targetedRelativeCut V x y hy
  change closureGenericPoint V x ∈
    ((targetedRelativeCutIdeal V x y hy).support : Set (pointClosureScheme V x))
  rw [hall]
  trivial

/-- All relative coheight-one components of the constructed directed cut. -/
noncomputable def targetedRelativeCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    Finset (pointClosureScheme V x) :=
  (finite_targetedRelativeCut_coheight_one V x y hy).toFinset

@[simp]
theorem mem_targetedRelativeCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x)
    (z : pointClosureScheme V x) :
    z ∈ targetedRelativeCodimensionOneFinset V x y hy ↔
      z ∈ (targetedRelativeCutIdeal V x y hy).support ∧
        Order.coheight z = 1 := by
  classical
  exact Set.Finite.mem_toFinset _

/-- Universal one-step source coverage: EVERY relative coheight-one point
occurs in the finite component locus of a constructed proper cut. This is a
geometric source theorem; it does not assert primitive Hodge spanning. -/
theorem every_relative_codimension_one_point_has_directed_cut
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy1 : Order.coheight y = 1) :
    ∃ hy : y ≠ closureGenericPoint V x,
      y ∈ targetedRelativeCodimensionOneFinset V x y hy := by
  have hy : y ≠ closureGenericPoint V x := by
    intro heq
    rw [heq, closureGenericPoint_coheight_zero] at hy1
    norm_num at hy1
  exact ⟨hy, (mem_targetedRelativeCodimensionOneFinset V x y hy y).mpr
    ⟨target_mem_targetedRelativeCut V x y hy, hy1⟩⟩

/-- The prescribed target as a point of the actual directed cut's support. -/
noncomputable def targetedRelativeCutTarget
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x) :
    ((targetedRelativeCutIdeal V x y hy).support :
      Set (pointClosureScheme V x)) :=
  ⟨y, target_mem_targetedRelativeCut V x y hy⟩

/-- The selected coheight-one target is genuinely a component generic point
of the constructed cut, not merely a point contained in its support. -/
theorem targetedRelativeCutTarget_is_component_generic
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ≠ closureGenericPoint V x)
    (hy1 : Order.coheight y = 1) :
    targetedRelativeCutTarget V x y hy ∈ genericPoints
      ((targetedRelativeCutIdeal V x y hy).support :
        Set (pointClosureScheme V x)) := by
  let C : Set (pointClosureScheme V x) :=
    (targetedRelativeCutIdeal V x y hy).support
  let u : C := targetedRelativeCutTarget V x y hy
  letI : QuasiSober C := Topology.IsClosedEmbedding.quasiSober
    (Topology.IsClosedEmbedding.subtypeVal
      (targetedRelativeCutIdeal V x y hy).support.isClosed)
  have hmax : ∀ z : pointClosureScheme V x, z ∈ C → y ≤ z → z = y := by
    intro z hzC hyz
    by_cases heq : z = y
    · exact heq
    · have hlt : y < z := by
        refine ⟨hyz, fun hzy => ?_⟩
        exact heq (inseparable_iff_eq.mp
          (inseparable_iff_specializes_and.mpr ⟨hyz, hzy⟩))
      have hbound : Order.coheight z ≤
          Order.coheight y := Order.coheight_anti hyz
      have hfinite : Order.coheight z < ⊤ := by
        apply hbound.trans_lt
        rw [hy1]
        exact WithTop.natCast_lt_top 1
      have hstrict := Order.coheight_strictAnti hlt hfinite
      rw [hy1] at hstrict
      have hz0 : Order.coheight z = 0 :=
        Order.lt_one_iff.mp hstrict
      have hzmax : IsMax z :=
        Order.coheight_eq_zero.mp hz0
      have hzg : z = closureGenericPoint V x :=
        inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr
          ⟨hzmax (pointClosure_le_generic V x z), pointClosure_le_generic V x z⟩)
      have hgeneric : closureGenericPoint V x ∈ C := by
        rw [← hzg]
        exact hzC
      exact (generic_not_mem_targetedRelativeCut V x y hy hgeneric).elim
  change closure ({u} : Set C) ∈ irreducibleComponents C
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro W hWirr hleW
  obtain ⟨g, hg⟩ : ∃ g : C, IsGenericPoint g (closure (W : Set C)) :=
    QuasiSober.sober hWirr.closure isClosed_closure
  have huW : u ∈ closure (W : Set C) :=
    subset_closure (hleW (subset_closure (Set.mem_singleton u)))
  have hug : y ≤ (g : pointClosureScheme V x) := by
    have hC : @LE.le C (specializationPreorder C).toLE u g := hg.specializes huW
    have hcont : Continuous (Subtype.val : C → pointClosureScheme V x) :=
      continuous_subtype_val
    have h := hcont.specialization_monotone hC
    change y ≤ (g : pointClosureScheme V x) at h
    exact h
  have hgeq : g = u := by
    apply Subtype.ext
    exact hmax g g.2 hug
  have hclos : closure (W : Set C) = closure ({u} : Set C) := by
    rw [← hgeq]
    exact hg.def.symm
  calc W ⊆ closure (W : Set C) := subset_closure
    _ = closure ({u} : Set C) := hclos

/-- Lift any ambient specialization into the actual reduced source closure. -/
noncomputable def specializationLift
    (V : SmoothProjectiveComplexScheme) (x z : V.X) (hzx : z ≤ x) :
    pointClosureScheme V x :=
  (pointClosureHomeomorph V x).symm
    ⟨z, specializationOrder_iff_specializes.mp hzx⟩

@[simp]
theorem specializationLift_maps
    (V : SmoothProjectiveComplexScheme) (x z : V.X) (hzx : z ≤ x) :
    pointClosureι V x (specializationLift V x z hzx) = z := by
  change ((pointClosureHomeomorph V x)
    (specializationLift V x z hzx)).1 = z
  simp [specializationLift]

/-- An ambient coheight gap of one forces relative coheight one along the
chosen specialization. This needs no global catenarity/additivity premise. -/
theorem specializationLift_coheight_one
    (V : SmoothProjectiveComplexScheme) (p : ℕ)
    (x z : V.X)
    (hx : Order.coheight x = p)
    (hz : Order.coheight z = (p + 1 : ℕ))
    (hzx : z < x) :
    Order.coheight (specializationLift V x z hzx.le) = 1 := by
  let y := specializationLift V x z hzx.le
  have himage : pointClosureι V x y = z := specializationLift_maps V x z hzx.le
  have hyne : y ≠ closureGenericPoint V x := by
    intro heq
    apply hzx.ne
    rw [← himage, heq, closureGenericPoint_maps_to_source]
  have hylt : y < closureGenericPoint V x := by
    refine ⟨pointClosure_le_generic V x y, fun hback => ?_⟩
    exact hyne (inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr
      ⟨hback, pointClosure_le_generic V x y⟩))
  have huniq : ∀ w : pointClosureScheme V x, y < w →
      w = closureGenericPoint V x := by
    intro w hyw
    have hywle : z ≤ pointClosureι V x w := by
      rw [← himage]
      exact (pointClosureι V x).continuous.specialization_monotone hyw.le
    have hywne : z ≠ pointClosureι V x w := by
      intro heq
      apply hyw.ne
      exact (pointClosureι V x).isEmbedding.injective (himage.trans heq)
    have hywlt : z < pointClosureι V x w := by
      refine ⟨hywle, fun hback => ?_⟩
      exact hywne (inseparable_iff_eq.mp
        (inseparable_iff_specializes_and.mpr ⟨hback, hywle⟩))
    have hwle : pointClosureι V x w ≤ x := by
      have h := (pointClosureι V x).continuous.specialization_monotone
        (pointClosure_le_generic V x w)
      simpa only [closureGenericPoint_maps_to_source] using h
    have hwfinite : Order.coheight (pointClosureι V x w) < ⊤ := by
      apply (Order.coheight_anti hywle).trans_lt
      rw [hz]
      exact ENat.natCast_lt_top (p + 1)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hwfinite.ne
    have hlow : p ≤ n := by
      have h := Order.coheight_anti hwle
      rw [hx, ← hn] at h
      exact_mod_cast h
    have hupp : n < p + 1 := by
      have h := Order.coheight_strictAnti hywlt hwfinite
      rw [hz, ← hn] at h
      exact_mod_cast h
    have hnp : n = p := by omega
    have hweq : pointClosureι V x w = x := by
      by_contra hne
      have hwlt : pointClosureι V x w < x := by
        refine ⟨hwle, fun hback => ?_⟩
        exact hne (inseparable_iff_eq.mp
          (inseparable_iff_specializes_and.mpr ⟨hback, hwle⟩))
      have hstrict := Order.coheight_strictAnti hwlt
        (show Order.coheight x < ⊤ by rw [hx]; exact ENat.natCast_lt_top p)
      rw [hx, ← hn, hnp] at hstrict
      exact (lt_irrefl _ hstrict)
    apply (pointClosureι V x).isEmbedding.injective
    rw [hweq, closureGenericPoint_maps_to_source]
  apply le_antisymm
  · rw [Order.coheight_eq_iSup_gt_coheight]
    apply iSup₂_le
    intro w hyw
    rw [huniq w hyw, closureGenericPoint_coheight_zero]
    simp
  · have h := Order.coheight_add_one_le hylt
    rw [closureGenericPoint_coheight_zero] at h
    simpa using h

/-- Every positive-codimension native point has an exact predecessor and is
an actual irreducible component of a derived proper cut in that predecessor's
closure. The equation and predecessor are constructed, not supplied. -/
theorem every_ambient_successor_point_has_directed_cut_component
    (V : SmoothProjectiveComplexScheme) (p : ℕ)
    (z : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X (p + 1)) :
    ∃ x : V.X, Order.coheight x = p ∧
      ∃ hzx : z.1 < x,
      ∃ hy : specializationLift V x z.1 hzx.le ≠ closureGenericPoint V x,
        Order.coheight (specializationLift V x z.1 hzx.le) = 1 ∧
        specializationLift V x z.1 hzx.le ∈
          targetedRelativeCodimensionOneFinset V x
            (specializationLift V x z.1 hzx.le) hy ∧
        targetedRelativeCutTarget V x (specializationLift V x z.1 hzx.le) hy ∈
          genericPoints
            ((targetedRelativeCutIdeal V x
              (specializationLift V x z.1 hzx.le) hy).support :
                Set (pointClosureScheme V x)) := by
  have hfinite : Order.coheight z.1 < ⊤ := by
    rw [z.2]
    exact ENat.natCast_lt_top (p + 1)
  have hlt : (p : ℕ∞) < Order.coheight z.1 := by
    rw [z.2]
    exact_mod_cast Nat.lt_succ_self p
  obtain ⟨x, hzx, hx⟩ :=
    (Order.coe_lt_coheight_iff (x := z.1) (n := p) hfinite).mp hlt
  have hy1 := specializationLift_coheight_one V p x z.1 hx z.2 hzx
  obtain ⟨hy, hmem⟩ := every_relative_codimension_one_point_has_directed_cut
    V x (specializationLift V x z.1 hzx.le) hy1
  exact ⟨x, hx, hzx, hy, hy1, hmem,
    targetedRelativeCutTarget_is_component_generic V x
      (specializationLift V x z.1 hzx.le) hy hy1⟩

/-- Every finite-codimension ambient point has an exact graded geometric
flag up to a codimension-zero generic point. Each adjacent pair has coheight
gap one, so the directed component construction applies along the flag. -/
theorem every_ambient_point_has_exact_coheight_flag
    (V : SmoothProjectiveComplexScheme) (p : ℕ)
    (z : V.X) (hz : Order.coheight z = p) :
    ∃ s : LTSeries V.X, s.head = z ∧ s.length = p ∧
      ∀ i : Fin (s.length + 1), Order.coheight (s i) = (i.rev : ℕ) := by
  obtain ⟨s, hs, hlength⟩ := Order.exists_series_of_coheight_eq_coe z hz
  refine ⟨s, hs, hlength, ?_⟩
  intro i
  exact Order.coheight_eq_index_of_length_eq_head_coheight
    (by rw [hs, hz, hlength]) i

#check targetedRelativeCutScheme
#check every_relative_codimension_one_point_has_directed_cut
#check targetedRelativeCutTarget_is_component_generic
#print axioms exists_targetedSectionEquation
#print axioms target_mem_targetedRelativeCut
#print axioms finite_targetedRelativeCut_coheight_one
#print axioms every_relative_codimension_one_point_has_directed_cut
#print axioms targetedRelativeCutTarget_is_component_generic
#check every_ambient_successor_point_has_directed_cut_component
#print axioms specializationLift_coheight_one
#print axioms every_ambient_successor_point_has_directed_cut_component
#check every_ambient_point_has_exact_coheight_flag
#print axioms every_ambient_point_has_exact_coheight_flag

end TargetDirected

#check relativeCutSet
#check closureGenericPoint_not_mem_relativeCut
#check relativeCutSet_ne_univ
#check finite_relative_coheight_one
#check relativeCodimensionOneFinset
#check point_closure_relative_successor_crown

#print axioms closureGenericPoint_not_mem_relativeCut
#print axioms relativeCutSet_ne_univ
#print axioms finite_relative_coheight_one
#print axioms point_closure_relative_successor_crown

end GSTClassicalHodgePointClosureRelativeCut
