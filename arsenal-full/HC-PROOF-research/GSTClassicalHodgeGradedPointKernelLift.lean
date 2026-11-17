import GSTClassicalHodgePointKernelOperatorLift
import GSTClassicalHodgeGradedNativeCohomologyRealization

/-!
# GST CLASSICAL HODGE — GRADED POINT-KERNEL LIFT

A geometric Lefschetz/intersection operator is most naturally specified on
irreducible cycle generators.  This module makes that generator-level input
sufficient.

For codimensions p and q, a graded point kernel assigns to each genuine
codimension-p generic point a finite rational presentation of genuine
codimension-q points.  Free linearity extends the kernel to finite
presentations; compactness of a smooth projective carrier identifies those
presentations with all native algebraic cycles.

If the pointwise cycle-class equation agrees with a graded cohomological
operator, the full cycle-class naturality square follows by linearity.  Hence a
future projective hyperplane-section construction only has to prove its formula
on genuine point generators.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGradedNativeCohomologyRealization

namespace GSTClassicalHodgeGradedPointKernelLift

universe u v w

variable {X : Scheme.{u}}
variable {CohP : Type v} [AddCommGroup CohP] [Module ℚ CohP]
variable {CohQ : Type w} [AddCommGroup CohQ] [Module ℚ CohQ]
variable {p q : Nat}
variable {clP : codimensionCycles X p →ₗ[ℚ] CohP}
variable {clQ : codimensionCycles X q →ₗ[ℚ] CohQ}

/-- Pure geometric generator data: one finite codimension-q presentation for
every codimension-p generic point. -/
abbrev GradedPointKernel (X : Scheme.{u}) (p q : Nat) :=
  CodimensionPoint X p → FiniteCodimensionPresentation X q

/-- A graded point transition together with its exact class formula. -/
structure GradedPointClassTransitionKernel
    (T : CohP →ₗ[ℚ] CohQ) where
  transition : GradedPointKernel X p q
  transition_spec :
    ∀ x : CodimensionPoint X p,
      (finitePointCycleClassMap q clQ) (transition x) =
        T (clP (codimensionPointCycle X p x))

namespace GradedPointClassTransitionKernel

variable {T : CohP →ₗ[ℚ] CohQ}

/-- Free linear extension of the graded point kernel. -/
noncomputable def presentationOperator
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T) :
    FiniteCodimensionPresentation X p →ₗ[ℚ]
      FiniteCodimensionPresentation X q :=
  Finsupp.linearCombination ℚ K.transition

@[simp]
theorem presentationOperator_single
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T)
    (x : CodimensionPoint X p) :
    K.presentationOperator (Finsupp.single x 1) = K.transition x := by
  simp [presentationOperator]

/-- The free presentation operator already intertwines the source and target
point-class maps. -/
theorem finitePointClass_natural
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T) :
    (finitePointCycleClassMap q clQ).comp K.presentationOperator =
      T.comp (finitePointCycleClassMap p clP) := by
  apply Finsupp.lhom_ext
  intro x c
  have hspec : (Finsupp.linearCombination ℚ
      (fun y => clQ (codimensionPointCycle X q y))) (K.transition x)
      = T (clP (codimensionPointCycle X p x)) := K.transition_spec x
  simp [presentationOperator, finitePointCycleClassMap, hspec]

/-- On a compact carrier, conjugate the graded presentation operator through
the exact cycle/presentation normal forms. -/
noncomputable def nativeCycleOperator
    [CompactSpace X]
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T) :
    codimensionCycles X p →ₗ[ℚ] codimensionCycles X q :=
  (realizePresentationLinear X q).comp
    (K.presentationOperator.comp
      (presentationOfNativeCycleLinear X p))

/-- The derived native graded operator acts on a point generator exactly by
realizing the prescribed target presentation. -/
@[simp]
theorem nativeCycleOperator_point
    [CompactSpace X]
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T)
    (x : CodimensionPoint X p) :
    K.nativeCycleOperator (codimensionPointCycle X p x) =
      realizeFiniteCodimensionPresentation X q (K.transition x) := by
  simp [nativeCycleOperator, LinearMap.comp_apply,
    realizePresentationLinear_apply, presentationOfNativeCycleLinear_apply,
    presentationOfNativeCycle_point, presentationOperator_single]

/-- **GRADED POINT KERNEL -> FULL CYCLE-CLASS NATURALITY.** -/
theorem nativeCycleOperator_natural
    [CompactSpace X]
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T) :
    clQ.comp K.nativeCycleOperator = T.comp clP := by
  apply LinearMap.ext
  intro Z
  let phi := presentationOfNativeCycle X p Z
  have hZ : realizeFiniteCodimensionPresentation X p phi = Z :=
    realize_presentationOfNativeCycle X p Z
  have hfree := LinearMap.congr_fun K.finitePointClass_natural phi
  change clQ (K.nativeCycleOperator Z) = T (clP Z)
  rw [← hZ]
  simpa [nativeCycleOperator, phi,
    finitePointCycleClassMap_eq_cycleClass_realize,
    realizePresentationLinear_apply,
    presentation_realizeFiniteCodimensionPresentation]
    using hfree

/-- The derived graded native operator is automatically kernel-stable. -/
theorem nativeCycleOperator_kernelStable
    [CompactSpace X]
    (K : GradedPointClassTransitionKernel
      (X := X) (p := p) (q := q) (clP := clP) (clQ := clQ) T) :
    ∀ Z : codimensionCycles X p,
      clP Z = 0 → clQ (K.nativeCycleOperator Z) = 0 := by
  intro Z hZ
  have hnat := LinearMap.congr_fun K.nativeCycleOperator_natural Z
  simp only [LinearMap.comp_apply] at hnat
  rw [hZ] at hnat
  simpa using hnat

end GradedPointClassTransitionKernel

/-! ## Smooth-projective Stage-2G specialization -/

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A generatorwise graded kernel on a smooth projective carrier produces the
exact cross-weight operator pair used by the limitless Lefschetz propagation. -/
noncomputable def GradedPointClassTransitionKernel.toGradedCycleClassOperatorPair
    {T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * q)}
    (K : GradedPointClassTransitionKernel
      (X := V.X) (p := p) (q := q)
      (clP := H.cycleClass p) (clQ := H.cycleClass q) T) :
    GradedCycleClassOperatorPair V H p q := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact {
    cycleOperator := K.nativeCycleOperator
    cohomologyOperator := T
    cycleClass_natural := by
      intro Z
      have h := LinearMap.congr_fun K.nativeCycleOperator_natural Z
      exact h
  }

#check GradedPointKernel
#check GradedPointClassTransitionKernel
#check GradedPointClassTransitionKernel.presentationOperator
#check GradedPointClassTransitionKernel.finitePointClass_natural
#check GradedPointClassTransitionKernel.nativeCycleOperator
#check GradedPointClassTransitionKernel.nativeCycleOperator_point
#check GradedPointClassTransitionKernel.nativeCycleOperator_natural
#check GradedPointClassTransitionKernel.nativeCycleOperator_kernelStable
#check GradedPointClassTransitionKernel.toGradedCycleClassOperatorPair

#print axioms GradedPointClassTransitionKernel.finitePointClass_natural
#print axioms GradedPointClassTransitionKernel.nativeCycleOperator_point
#print axioms GradedPointClassTransitionKernel.nativeCycleOperator_natural
#print axioms GradedPointClassTransitionKernel.nativeCycleOperator_kernelStable
#print axioms GradedPointClassTransitionKernel.toGradedCycleClassOperatorPair

end GSTClassicalHodgeGradedPointKernelLift
