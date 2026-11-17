import GSTClassicalHodgePrincipalCutNativeCycle
import GSTCompactNativeCyclePresentation
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT GRADED NATIVE OPERATOR

The projective principal-cut construction is linearized into a genuine native
graded cycle operator.  On each codimension-zero generic point it outputs the
finite codimension-one cycle cut out by the point-specific positive-degree
projective separator.  Free finite presentations extend this generator action
linearly; compactness of the smooth projective carrier then extends it to every
native codimension-zero algebraic cycle.

This is an actual geometry-built `codimension 0 -> codimension 1` operator.
It is independent of Hodge semantics and of the cycle-class map.  Later
naturality modules compare its induced class with the limitless Lefschetz
transport.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeAtomicSpan
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgePrincipalCutNativeCycle

namespace GSTClassicalHodgePrincipalCutGradedOperator

variable (V : SmoothProjectiveComplexScheme)
variable [IrreducibleSpace V.X]

/-- Generator kernel: a codimension-zero point is sent to the finite
codimension-one presentation produced by its selected principal cut. -/
noncomputable def zeroToOnePointKernel
    (x : CodimensionPoint V.X 0) :
    FiniteCodimensionPresentation V.X 1 :=
  principalCutPresentation V x.1

/-- Free linear extension on finite point presentations. -/
noncomputable def zeroToOnePresentationOperator :
    FiniteCodimensionPresentation V.X 0 →ₗ[ℚ]
      FiniteCodimensionPresentation V.X 1 where
  toFun φ := φ.sum fun x q => q • zeroToOnePointKernel V x
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
theorem zeroToOnePresentationOperator_single
    (x : CodimensionPoint V.X 0) (q : ℚ) :
    zeroToOnePresentationOperator V (Finsupp.single x q) =
      q • zeroToOnePointKernel V x := by
  classical
  simp [zeroToOnePresentationOperator]

/-- Realize the finite target presentation as an actual native
codimension-one cycle. -/
noncomputable def zeroToOneFiniteNative :
    FiniteCodimensionPresentation V.X 0 →ₗ[ℚ]
      codimensionCycles V.X 1 where
  toFun φ :=
    realizeFiniteCodimensionPresentation V.X 1
      (zeroToOnePresentationOperator V φ)
  map_add' := by
    intro φ ψ
    classical
    have hop : zeroToOnePresentationOperator V (φ + ψ) =
        zeroToOnePresentationOperator V φ + zeroToOnePresentationOperator V ψ :=
      (zeroToOnePresentationOperator V).map_add φ ψ
    rw [hop, realizeFiniteCodimensionPresentation_add]
  map_smul' := by
    intro q φ
    classical
    rw [RingHom.id_apply]
    have hop : zeroToOnePresentationOperator V (q • φ) =
        q • zeroToOnePresentationOperator V φ :=
      (zeroToOnePresentationOperator V).map_smul q φ
    rw [hop, realizeFiniteCodimensionPresentation_smul]

/-- **NATIVE PRINCIPAL-CUT GRADED OPERATOR.**
Every native codimension-zero cycle has a finite point normal form; apply the
principal-cut kernel generatorwise and realize the result in codimension one. -/
noncomputable def zeroToOneNativeOperator :
    codimensionCycles V.X 0 →ₗ[ℚ] codimensionCycles V.X 1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (zeroToOneFiniteNative V).comp
    (presentationOfNativeCycleLinear V.X 0)

/-- Point-generator formula for the native graded operator. -/
theorem zeroToOneNativeOperator_point
    (x : CodimensionPoint V.X 0) :
    zeroToOneNativeOperator V (codimensionPointCycle V.X 0 x) =
      principalCutCycle V x.1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [zeroToOneNativeOperator, LinearMap.comp_apply,
    zeroToOneFiniteNative, zeroToOnePresentationOperator,
    zeroToOnePointKernel, presentationOfNativeCycleLinear_apply,
    presentationOfNativeCycle_point, zeroToOnePresentationOperator_single,
    principalCutCycle]

/-- The operator is geometrically generated on every codimension-zero atom by
an actual projective principal section. -/
theorem zeroToOneNativeOperator_generator_crown :
    ∀ x : CodimensionPoint V.X 0,
      zeroToOneNativeOperator V (codimensionPointCycle V.X 0 x) =
        principalCutCycle V x.1 := by
  exact zeroToOneNativeOperator_point V

#check zeroToOnePointKernel
#check zeroToOnePresentationOperator
#check zeroToOneFiniteNative
#check zeroToOneNativeOperator
#check zeroToOneNativeOperator_point
#check zeroToOneNativeOperator_generator_crown

#print axioms zeroToOnePresentationOperator_single
#print axioms zeroToOneNativeOperator_point
#print axioms zeroToOneNativeOperator_generator_crown

end GSTClassicalHodgePrincipalCutGradedOperator
