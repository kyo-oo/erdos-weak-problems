import GSTCompactNativeCyclePresentation
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — COMPACT NATIVE PRESENTATION ROUNDTRIP

On a smooth projective carrier every native algebraic cycle has finite support.
`presentationOfNativeCycle` already records its actual rational coefficient at
each genuine codimension point, but the repository had only used that map in
the forward direction.

This file records the missing exactness statement: realizing the extracted
finite presentation gives back the original native codimension cycle.

This matters for the canonical principal-cut spine.  The successor operator
re-presents its input at every weight.  The roundtrip theorem proves that this
step loses no coefficient information, so positivity/support arguments may be
carried through the recursive cut tower rather than restarted after every cut.
-/

open GSTClassicalHodgePointNormalForm

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCompactPresentationRoundtrip

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation

local instance (V : SmoothProjectiveComplexScheme) : CompactSpace V.X :=
  smoothProjectiveCompactSpace V

/-- **EXACT COMPACT PRESENTATION ROUNDTRIP.**
Extract the genuine finite coefficient presentation of a native codimension-p
cycle on a smooth projective scheme and realize it again: the cycle is unchanged. -/
theorem realize_presentationOfNativeCycle
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (Z : codimensionCycles V.X p) :
    realizeFiniteCodimensionPresentation V.X p
        (presentationOfNativeCycle V.X p Z) = Z := by
  apply Subtype.ext
  ext y
  by_cases hy : Order.coheight y = p
  · show (realizeFiniteCodimensionPresentation V.X p
        (presentationOfNativeCycle V.X p Z) : AlgebraicCycle V.X ℚ) y
      = (Z.1 : AlgebraicCycle V.X ℚ) y
    rw [realizeFiniteCodimensionPresentation_apply V.X p
      (presentationOfNativeCycle V.X p Z) y]
    simp only [Finsupp.sum, smul_eq_mul]
    refine (Finset.sum_eq_single (⟨y, hy⟩ : CodimensionPoint V.X p) ?_ ?_).trans ?_
    · intro b _ hb
      have hne : y ≠ b.1 := by
        intro heq
        exact hb (Subtype.ext heq.symm)
      simp [hne]
    · intro hout
      simp [Finsupp.notMem_support_iff.mp hout]
    · simp [presentationOfNativeCycle_apply]
  · have hZy : (Z.1 : AlgebraicCycle V.X ℚ) y = 0 := by
      by_contra hne
      have hySupport : y ∈ (Z.1 : AlgebraicCycle V.X ℚ).support := hne
      exact hy (Z.2 hySupport)
    show (realizeFiniteCodimensionPresentation V.X p
      (presentationOfNativeCycle V.X p Z) : AlgebraicCycle V.X ℚ) y
      = (Z.1 : AlgebraicCycle V.X ℚ) y
    rw [realizeFiniteCodimensionPresentation_apply V.X p
      (presentationOfNativeCycle V.X p Z) y, hZy]
    simp only [Finsupp.sum, smul_eq_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : y ≠ x.1 := by
      intro heq
      apply hy
      rw [heq]
      exact x.2
    simp [hne]

/-- The extracted presentation is injective: two native cycles with the same
finite coefficient table are literally the same cycle. -/
theorem presentationOfNativeCycle_injective
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    Function.Injective (presentationOfNativeCycle V.X p) := by
  intro Z W hZW
  calc
    Z = realizeFiniteCodimensionPresentation V.X p
        (presentationOfNativeCycle V.X p Z) :=
      (realize_presentationOfNativeCycle V p Z).symm
    _ = realizeFiniteCodimensionPresentation V.X p
        (presentationOfNativeCycle V.X p W) := by rw [hZW]
    _ = W := realize_presentationOfNativeCycle V p W

#check realize_presentationOfNativeCycle
#check presentationOfNativeCycle_injective

#print axioms realize_presentationOfNativeCycle
#print axioms presentationOfNativeCycle_injective

end GSTClassicalHodgeCompactPresentationRoundtrip
