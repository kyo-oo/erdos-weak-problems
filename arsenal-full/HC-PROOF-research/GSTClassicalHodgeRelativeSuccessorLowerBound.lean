import GSTClassicalHodgePrincipalCutSuccessorOperator
import Mathlib.Topology.Sober

/-!
# GST CLASSICAL HODGE — AMBIENT LOWER BOUND FOR RELATIVE SUCCESSORS

A relative codimension-one point in the principal cut of `closure {x}` is a
strict specialization of the generic source `x` after mapping back to the
ambient projective scheme.  Therefore its ambient coheight is at least one
larger than the coheight of `x`.

This theorem is pure specialization-order geometry.  It supplies the lower
half of the exact grading statement needed by the successor operator; the
local regular/principal-ideal engine supplies the matching upper bound.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator

namespace GSTClassicalHodgeRelativeSuccessorLowerBound

/-- Every point of the point-closure scheme maps into the ambient closure of
its source generic point. -/
theorem pointClosure_image_mem_closure
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x) :
    pointClosureι V x y ∈ closure ({x} : Set V.X) := by
  rw [← range_pointClosureι V x]
  exact ⟨y, rfl⟩

/-- Hence every point of the closure scheme specializes from the source point
in the ambient specialization order. -/
theorem pointClosure_image_le_source
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x) :
    pointClosureι V x y ≤ x := by
  -- Membership in `closure {x}` is exactly specialization below `x`.
  simpa [specializationOrder_iff_specializes] using
    pointClosure_image_mem_closure V x y

/-- A point in the restricted principal cut cannot map back to the source
point itself. -/
theorem relativeCut_image_ne_source
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ∈ relativeCutSet V x) :
    pointClosureι V x y ≠ x := by
  intro h
  have hygen : y = closureGenericPoint V x := by
    apply (pointClosureι V x).isEmbedding.injective
    rw [h, closureGenericPoint_maps_to_source V x]
  subst y
  exact closureGenericPoint_not_mem_relativeCut V x hy

/-- Relative-cut points are strict ambient specializations of the source. -/
theorem relativeCut_image_lt_source
    (V : SmoothProjectiveComplexScheme) (x : V.X)
    (y : pointClosureScheme V x)
    (hy : y ∈ relativeCutSet V x) :
    pointClosureι V x y < x := by
  refine ⟨pointClosure_image_le_source V x y, fun h => ?_⟩
  exact relativeCut_image_ne_source V x y hy
    (inseparable_iff_eq.mp (inseparable_iff_specializes_and.mpr
      ⟨h, pointClosure_image_le_source V x y⟩))

/-- **AMBIENT CODIMENSION LOWER BOUND.**
If `x` has ambient codimension `p`, every point in its proper relative
principal cut has ambient coheight at least `p+1`. -/
theorem ambient_coheight_ge_succ
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : pointClosureScheme V x.1)
    (hy : y ∈ relativeCutSet V x.1) :
    (p + 1 : ℕ∞) ≤ Order.coheight (pointClosureι V x.1 y) := by
  have hlt : pointClosureι V x.1 y < x.1 :=
    relativeCut_image_lt_source V x.1 y hy
  have hstep := Order.coheight_add_one_le hlt
  simpa [x.2, Nat.cast_add, Nat.cast_one] using hstep

/-- In particular the lower bound applies to every relative coheight-one
successor candidate selected by the cutting engine. -/
theorem relative_codim_one_ambient_ge_succ
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : pointClosureScheme V x.1)
    (hycut : y ∈ relativeCutSet V x.1)
    (hy1 : Order.coheight y = 1) :
    (p + 1 : ℕ∞) ≤ Order.coheight (pointClosureι V x.1 y) := by
  exact ambient_coheight_ge_succ V p x y hycut

#check pointClosure_image_mem_closure
#check pointClosure_image_le_source
#check relativeCut_image_ne_source
#check relativeCut_image_lt_source
#check ambient_coheight_ge_succ
#check relative_codim_one_ambient_ge_succ

#print axioms pointClosure_image_le_source
#print axioms relativeCut_image_lt_source
#print axioms ambient_coheight_ge_succ
#print axioms relative_codim_one_ambient_ge_succ

end GSTClassicalHodgeRelativeSuccessorLowerBound
