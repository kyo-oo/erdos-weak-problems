import GSTClassicalHodgePrincipalSectionNoetherian

/-!
# GST CLASSICAL HODGE — PRINCIPAL-SECTION CLOSED-SET DESCENT

The generator-specific principal section avoids its source point.  Therefore,
inside any closed algebraic region containing that source, intersection with
the principal section is a genuine strict closed descent.

This file isolates that mechanism at the level needed for recursive support
cutting.  It does not use Hodge theory or any cycle-class statement.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePrincipalSectionNoetherian

namespace GSTClassicalHodgePrincipalSectionDescent

/-- Support in `V` of the positive-degree principal section selected by `x`. -/
def cutSupport
    (V : SmoothProjectiveComplexScheme) (x : V.X) : Set V.X :=
  (principalSectionIdeal V
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation).support

/-- The source point is never in its own selected cut support. -/
theorem source_not_mem_cutSupport
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    x ∉ cutSupport V x := by
  exact source_not_mem_principalSection V x

/-- Restrict the source-specific cut to an arbitrary region `C`. -/
def descendSet
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (C : Set V.X) : Set V.X :=
  C ∩ cutSupport V x

/-- Descending never creates points outside the original region. -/
theorem descendSet_subset
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (C : Set V.X) :
    descendSet V x C ⊆ C := by
  intro y hy
  exact hy.1

/-- If the source lies in `C`, then the descent is genuinely strict. -/
theorem descendSet_ssubset
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (C : Set V.X) (hx : x ∈ C) :
    descendSet V x C ⊂ C := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨descendSet_subset V x C, ?_⟩
  intro hEq
  have hxdesc : x ∈ descendSet V x C := by
    rw [hEq]
    exact hx
  exact source_not_mem_cutSupport V x hxdesc.2

/-- Closed regions descend to closed regions under a principal cut. -/
theorem descendSet_isClosed
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (C : Set V.X) (hC : IsClosed C) :
    IsClosed (descendSet V x C) := by
  apply hC.inter
  exact (principalSectionIdeal V
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation).support.isClosed

/-- Bundled strict closed descent crown. -/
theorem strict_closed_descent
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (C : Set V.X) (hC : IsClosed C) (hx : x ∈ C) :
    IsClosed (descendSet V x C) ∧ descendSet V x C ⊂ C := by
  exact ⟨descendSet_isClosed V x C hC,
    descendSet_ssubset V x C hx⟩

/-- The whole projective carrier admits a strict first descent at every point. -/
theorem univ_strict_descent
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosed (descendSet V x Set.univ)
      ∧ descendSet V x Set.univ ⊂ (Set.univ : Set V.X) := by
  exact strict_closed_descent V x Set.univ isClosed_univ (by trivial)

#check cutSupport
#check descendSet
#check descendSet_subset
#check descendSet_ssubset
#check descendSet_isClosed
#check strict_closed_descent
#check univ_strict_descent

#print axioms source_not_mem_cutSupport
#print axioms descendSet_ssubset
#print axioms descendSet_isClosed
#print axioms strict_closed_descent
#print axioms univ_strict_descent

end GSTClassicalHodgePrincipalSectionDescent
