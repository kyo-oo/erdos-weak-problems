import GSTClassicalHodgeSeparatorRelativeCover
import GSTClassicalHodgeSeparatorRelativeCutLanding
import Mathlib.Order.KrullDimension

/-!
# GST CLASSICAL HODGE — EXACT RELATIVE COHEIGHT ONE OF THE SEPARATOR SUCCESSOR

The separator successor is a genuine point of the relative principal cut and
its only strict generalization inside the reduced source closure is the
canonical generic source point.  This file converts that cover statement into
the exact numerical grading used by the recursive successor finset:

  `Order.coheight successor = 1`.

The order-theoretic core is independent of algebraic geometry: if an element
has a strict generalization and every strict generalization is the same point,
then every strict chain beginning at that element has length at most one, while
the existing strict step gives length at least one.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeRelativeSuccessorLowerBound
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorPointClosureLift
open GSTClassicalHodgeSeparatorRelativeCutLanding
open GSTClassicalHodgeSeparatorRelativeCover

namespace GSTClassicalHodgeSeparatorRelativeCoheightOne

/-- Pure order lemma: an element with exactly one strict point above it has
coheight at most one. -/
theorem coheight_le_one_of_unique_strictAbove
    {α : Type*} [PartialOrder α]
    (a top : α)
    (huniq : ∀ z : α, a < z → z = top) :
    Order.coheight a ≤ 1 := by
  apply Order.coheight_le
  intro s hs
  by_contra hnot
  have hlen : 2 ≤ s.length := by
    push_neg at hnot
    have h2 : (1 : ℕ∞) < ↑s.length := hnot
    have h1 : (1 : ℕ) < s.length := by exact_mod_cast h2
    omega
  let i0 : Fin (s.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (s.length + 1) := ⟨1, by omega⟩
  let i2 : Fin (s.length + 1) := ⟨2, by omega⟩
  have hi0 : s i0 = s.head := by
    rfl
  have h01 : s i0 < s i1 := by
    exact s.step ⟨0, by omega⟩
  have h12 : s i1 < s i2 := by
    exact s.step ⟨1, by omega⟩
  have ha1 : a < s i1 := by
    rw [← hs, ← hi0]
    exact h01
  have ha2 : a < s i2 := lt_trans ha1 h12
  have h1top := huniq (s i1) ha1
  have h2top := huniq (s i2) ha2
  exact (ne_of_lt h12) (h1top.trans h2top.symm)

attribute [local instance] specializationOrder

/-- The separator successor is strictly below the canonical generic source
inside the reduced point-closure specialization order. -/
theorem separatorSuccessor_lt_generic
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    pointClosureSeparatorSuccessor V x hlive < closureGenericPoint V x := by
  let y := pointClosureSeparatorSuccessor V x hlive
  let η := closureGenericPoint V x
  have hycut : y ∈ relativeCutSet V x :=
    pointClosureSeparatorSuccessor_mem_relativeCut V x hlive
  have himageLt : pointClosureι V x y < x :=
    relativeCut_image_lt_source V x y hycut
  have hle : y ≤ η := by
    rw [specializationOrder_iff_specializes]
    have himageMem : pointClosureι V x y ∈ closure ({x} : Set V.X) :=
      (specializationOrder_iff_specializes.mp himageLt.le)
    have hclosure :=
      (pointClosureι V x).isEmbedding.closure_eq_preimage_closure_image
        ({η} : Set (pointClosureScheme V x))
    have himageSingleton :
        pointClosureι V x '' ({η} : Set (pointClosureScheme V x)) = ({x} : Set V.X) := by
      ext z
      simp [η, closureGenericPoint_maps_to_source]
    rw [himageSingleton] at hclosure
    have : y ∈ (pointClosureι V x) ⁻¹' closure ({x} : Set V.X) := himageMem
    rwa [← hclosure] at this
  exact lt_of_le_of_ne hle
    (pointClosureSeparatorSuccessor_ne_generic V x hlive)

/-- **EXACT RELATIVE COHEIGHT ONE.** -/
theorem pointClosureSeparatorSuccessor_coheight_one
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    Order.coheight (pointClosureSeparatorSuccessor V x hlive) = 1 := by
  let y := pointClosureSeparatorSuccessor V x hlive
  let η := closureGenericPoint V x
  have hlt : y < η := separatorSuccessor_lt_generic V x hlive
  have hlower : (1 : ℕ∞) ≤ Order.coheight y := by
    have h := Order.coheight_add_one_le hlt
    have hη0 : Order.coheight η = 0 := by
      apply Order.coheight_eq_zero.mpr
      intro z hz
      rw [specializationOrder_iff_specializes]
      have himageMem : pointClosureι V x z ∈ closure ({x} : Set V.X) := by
        rw [← range_pointClosureι V x]
        exact ⟨z, rfl⟩
      have hclosure :=
        (pointClosureι V x).isEmbedding.closure_eq_preimage_closure_image
          ({η} : Set (pointClosureScheme V x))
      have himageSingleton :
          pointClosureι V x '' ({η} : Set (pointClosureScheme V x)) =
            ({x} : Set V.X) := by
        ext w
        simp [η, closureGenericPoint_maps_to_source]
      rw [himageSingleton] at hclosure
      have hmem : z ∈ (pointClosureι V x) ⁻¹' closure ({x} : Set V.X) :=
        himageMem
      rwa [← hclosure] at hmem
    rw [hη0] at h
    simpa using h
  have hupper : Order.coheight y ≤ 1 :=
    coheight_le_one_of_unique_strictAbove y η
      (no_intermediate_above_separatorSuccessor V x hlive)
  have hne : Order.coheight y ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact absurd hupper (by simp)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hupper hlower ⊢
  have hn1 : n ≤ 1 := ENat.coe_le_coe.mp hupper
  have hn2 : 1 ≤ n := ENat.coe_le_coe.mp hlower
  rw [← ENat.coe_one]
  exact congrArg ((↑) : ℕ → ℕ∞) (le_antisymm (α := ℕ) hn1 hn2)

/-- The constructed successor therefore determines an actual member of the
relative coheight-one subtype used by the recursive cut operator. -/
noncomputable def relativeHeightOneSeparatorSuccessor
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    {y : pointClosureScheme V x // Order.coheight y = 1} :=
  ⟨pointClosureSeparatorSuccessor V x hlive,
    pointClosureSeparatorSuccessor_coheight_one V x hlive⟩

#check coheight_le_one_of_unique_strictAbove
#check separatorSuccessor_lt_generic
#check pointClosureSeparatorSuccessor_coheight_one
#check relativeHeightOneSeparatorSuccessor

#print axioms coheight_le_one_of_unique_strictAbove
#print axioms pointClosureSeparatorSuccessor_coheight_one
#print axioms relativeHeightOneSeparatorSuccessor

end GSTClassicalHodgeSeparatorRelativeCoheightOne
