import GSTClassicalHodgePointClosureRelativeCut
import GSTClassicalHodgeSchemeCodimensionStalk
import GSTCompactNativeCyclePresentation
import GSTGeometricRealizationStage2D
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — EXACT-STRATUM PRINCIPAL-CUT SUCCESSOR OPERATOR

The relative principal-cut engine gives finitely many codimension-one successor
candidates inside the irreducible closure of every source point.  Their ambient
codimension need not be guessed: the native cycle space already has an exact
coheight grading, equivalently an exact stalk-Krull-dimension grading.

For a source atom of ambient codimension `p`, this module maps all relative
successors back to the ambient smooth projective scheme and retains precisely
those lying in the exact ambient codimension `p+1` stratum.  The resulting
finite presentation is therefore unconditionally a native codimension-`p+1`
presentation.  Free linear extension and the compact point-normal form then
produce a genuine native graded operator

    codimensionCycles V.X p -> codimensionCycles V.X (p+1).

No Hodge data and no cycle-class map occur in this construction.  The later
nonvanishing/exhaustion theorem must prove that the exact-stratum filter really
captures the projective principal-cut successors required for Lefschetz
propagation; it is not assumed here.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSchemeCodimensionStalk
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgePointKernelOperatorLift

namespace GSTClassicalHodgePrincipalCutSuccessorOperator

/-- Ambient image of one relative codimension-one successor candidate. -/
noncomputable def ambientSuccessorPoint
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (y : {y : pointClosureScheme V x // Order.coheight y = 1}) : V.X :=
  pointClosureι V x y.1

/-- Exact-stratum contribution of one relative successor candidate.  It is a
unit atom when the ambient codimension is exactly one greater than the source
codimension, and zero otherwise. -/
noncomputable def successorAtomPresentation
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    FiniteCodimensionPresentation V.X (p + 1) := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · exact Finsupp.single ⟨ambientSuccessorPoint V x.1 y, hy⟩ 1
  · exact 0

/-- Finite exact-ambient-codimension successor presentation of one source atom. -/
noncomputable def successorPresentation
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    FiniteCodimensionPresentation V.X (p + 1) := by
  classical
  exact (relativeCodimensionOneFinset V x.1).sum
    (successorAtomPresentation V p x)

/-- If a relative successor has the expected ambient codimension, its unit
point presentation occurs as its direct generator contribution. -/
theorem successorAtomPresentation_eq_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorAtomPresentation V p x y =
      Finsupp.single
        (⟨ambientSuccessorPoint V x.1 y, hy⟩ : CodimensionPoint V.X (p + 1)) 1 := by
  classical
  simp [successorAtomPresentation, hy]

/-- Wrong ambient grading contributes zero rather than contaminating the
codimension-p+1 cycle space. -/
theorem successorAtomPresentation_eq_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : Order.coheight (ambientSuccessorPoint V x.1 y) ≠ p + 1) :
    successorAtomPresentation V p x y = 0 := by
  classical
  simp [successorAtomPresentation, hy]

/-- Free linear extension of the exact-stratum successor kernel to finite
codimension-p point presentations. -/
noncomputable def successorPresentationOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X (p + 1) where
  toFun φ := φ.sum fun x q => q • successorPresentation V p x
  map_add' := by
    intro φ ψ
    classical
    rw [Finsupp.sum_add_index']
    · intro i; simp
    · intro i b₁ b₂; simp [add_smul]
  map_smul' := by
    intro q φ
    classical
    rw [RingHom.id_apply]
    first
    | rw [Finsupp.sum_smul_index]
      intro i
      simp
    | by_cases hq : q = 0
      · subst q
        simp
      · have hsup : (q • φ).support = φ.support := by
          ext a
          simp [Finsupp.mem_support_iff, mul_ne_zero_iff, hq]
        simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul,
          Finset.smul_sum, smul_smul]
        rw [hsup]
    | simp [Finsupp.sum, Finset.smul_sum, smul_eq_mul, smul_smul,
      RingHom.id_apply, mul_comm, mul_assoc, mul_left_comm, mul_ne_zero]

@[simp]
theorem successorPresentationOperator_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (q : ℚ) :
    successorPresentationOperator V p (Finsupp.single x q) =
      q • successorPresentation V p x := by
  classical
  simp [successorPresentationOperator]

/-- Realize the successor presentation as an actual native target cycle. -/
noncomputable def successorFiniteNativeOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      codimensionCycles V.X (p + 1) where
  toFun φ :=
    realizeFiniteCodimensionPresentation V.X (p + 1)
      (successorPresentationOperator V p φ)
  map_add' := by
    intro φ ψ
    classical
    have hop : successorPresentationOperator V p (φ + ψ) =
        successorPresentationOperator V p φ +
          successorPresentationOperator V p ψ :=
      (successorPresentationOperator V p).map_add φ ψ
    rw [hop, realizeFiniteCodimensionPresentation_add]
  map_smul' := by
    intro q φ
    classical
    rw [RingHom.id_apply]
    have hop : successorPresentationOperator V p (q • φ) =
        q • successorPresentationOperator V p φ :=
      (successorPresentationOperator V p).map_smul q φ
    rw [hop, realizeFiniteCodimensionPresentation_smul]

/-- **UNCONDITIONAL GEOMETRY-BUILT GRADED SUCCESSOR OPERATOR.** -/
noncomputable def successorNativeOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ]
      codimensionCycles V.X (p + 1) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (successorFiniteNativeOperator V p).comp
    (presentationOfNativeCycleLinear V.X p)

/-- Point-generator formula. -/
theorem successorNativeOperator_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) =
      realizeFiniteCodimensionPresentation V.X (p + 1)
        (successorPresentation V p x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [successorNativeOperator, LinearMap.comp_apply,
    successorFiniteNativeOperator, successorPresentationOperator,
    presentationOfNativeCycleLinear_apply, presentationOfNativeCycle_point,
    successorPresentationOperator_single]

/-- Every generator image is explicitly represented by finitely many exact
ambient codimension-p+1 point atoms. -/
theorem successorNativeOperator_has_finite_target
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    ∃ φ : FiniteCodimensionPresentation V.X (p + 1),
      successorNativeOperator V p (codimensionPointCycle V.X p x) =
        realizeFiniteCodimensionPresentation V.X (p + 1) φ := by
  exact ⟨successorPresentation V p x,
    successorNativeOperator_point V p x⟩

#check ambientSuccessorPoint
#check successorAtomPresentation
#check successorPresentation
#check successorPresentationOperator
#check successorFiniteNativeOperator
#check successorNativeOperator
#check successorNativeOperator_point
#check successorNativeOperator_has_finite_target

#print axioms successorAtomPresentation_eq_single
#print axioms successorPresentationOperator_single
#print axioms successorNativeOperator_point
#print axioms successorNativeOperator_has_finite_target

end GSTClassicalHodgePrincipalCutSuccessorOperator
