import GSTClassicalHodgeAtomicOperatorAlgebra
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — POINT-KERNEL OPERATOR LIFT

On a compact scheme, native codimension-p rational algebraic cycles are
exactly finite rational combinations of genuine codimension-p points.
The existing reconstruction theorem gives the right inverse; pointwise
coefficient recovery gives the left inverse.  Hence the two spaces are
rational-linearly equivalent.

This makes the generatorwise transition interface fully equivalent to the
older native-operator interface:

* a point-transition kernel extends freely to finite presentations;
* conjugating by the compact presentation equivalence gives a linear operator
  on all native codimension-p cycles;
* the pointwise transition equations imply the full cycle-class commuting
  square by linearity.

Therefore a point-transition kernel automatically manufactures the complete
`CycleClassOperatorPair` needed by native polynomial spectral extraction.
No independent operator on arbitrary cycles has to be supplied.

The companion `GSTClassicalHodgeNativePointRelationDescent` upgrades this
direction further. It starts with a raw native point transition, constructs
the cohomological action from preservation of finite point-class relations,
and derives this file's `PointClassTransitionKernel` and its point action
equation. Thus the ambient operator need not precede the native construction.
-/

set_option maxHeartbeats 10000000
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
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeCycleOperatorNaturality

namespace GSTClassicalHodgePointKernelOperatorLift

universe u v

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}

/-- Linear realization of finite point presentations as native cycles. -/
noncomputable def realizePresentationLinear
    (X : Scheme.{u}) (p : Nat) :
    FiniteCodimensionPresentation X p →ₗ[ℚ] codimensionCycles X p :=
  Finsupp.linearCombination ℚ
    (fun x => codimensionPointCycle X p x)

@[simp]
theorem realizePresentationLinear_apply
    (X : Scheme.{u}) (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    realizePresentationLinear X p φ =
      realizeFiniteCodimensionPresentation X p φ := by
  rfl

/-- On a compact scheme, coefficient extraction from a native cycle is a
rational linear map. -/
noncomputable def presentationOfNativeCycleLinear
    (X : Scheme.{u}) [CompactSpace X] (p : Nat) :
    codimensionCycles X p →ₗ[ℚ] FiniteCodimensionPresentation X p where
  toFun := presentationOfNativeCycle X p
  map_add' := by
    intro Z W
    apply Finsupp.ext
    intro x
    simp [presentationOfNativeCycle_apply]
  map_smul' := by
    intro q Z
    apply Finsupp.ext
    intro x
    simp [presentationOfNativeCycle_apply]

@[simp]
theorem presentationOfNativeCycleLinear_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (Z : codimensionCycles X p) :
    presentationOfNativeCycleLinear X p Z =
      presentationOfNativeCycle X p Z :=
  rfl

/-- Coefficient extraction after realization recovers the original finite
presentation exactly. -/
theorem presentation_realizeFiniteCodimensionPresentation
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    presentationOfNativeCycle X p
      (realizeFiniteCodimensionPresentation X p φ) = φ := by
  classical
  apply Finsupp.ext
  intro x
  show (realizeFiniteCodimensionPresentation X p φ : AlgebraicCycle X ℚ) x.1
      = φ x
  rw [realizeFiniteCodimensionPresentation_apply X p φ x.1]
  simp only [Finsupp.sum, smul_eq_mul]
  by_cases hx : x ∈ φ.support
  · have hsingle : ∑ b ∈ φ.support, φ b * (if x.1 = b.1 then (1 : ℚ) else 0)
        = φ x * (if x.1 = x.1 then (1 : ℚ) else 0) :=
      Finset.sum_eq_single (a := x)
      (fun b _ hb => by
        have hne : x.1 ≠ b.1 := by
          intro heq
          exact hb (Subtype.ext heq.symm)
        simp [hne])
      (fun hcon => absurd hx hcon)
    rw [hsingle]
    simp
  · have hxφ : φ x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hxφ]
    refine Finset.sum_eq_zero fun y hy => ?_
    have hne : x.1 ≠ y.1 := by
      intro heq
      apply hx
      have hxy : x = y := Subtype.ext heq
      rw [hxy]
      exact hy
    simp [hne]

/-- **COMPACT CYCLE/PRESENTATION LINEAR EQUIVALENCE.** -/
noncomputable def compactCyclePresentationLinearEquiv
    (X : Scheme.{u}) [CompactSpace X] (p : Nat) :
    FiniteCodimensionPresentation X p ≃ₗ[ℚ] codimensionCycles X p where
  toLinearMap := realizePresentationLinear X p
  invFun := presentationOfNativeCycle X p
  left_inv := presentation_realizeFiniteCodimensionPresentation X p
  right_inv := realize_presentationOfNativeCycle X p

@[simp]
theorem compactCyclePresentationLinearEquiv_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    compactCyclePresentationLinearEquiv X p φ =
      realizeFiniteCodimensionPresentation X p φ :=
  rfl

@[simp]
theorem compactCyclePresentationLinearEquiv_symm_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (Z : codimensionCycles X p) :
    (compactCyclePresentationLinearEquiv X p).symm Z =
      presentationOfNativeCycle X p Z :=
  rfl

/-- Free linear extension of a point-transition kernel to arbitrary finite
point presentations. -/
noncomputable def
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.presentationOperator
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    FiniteCodimensionPresentation X p →ₗ[ℚ]
      FiniteCodimensionPresentation X p :=
  Finsupp.linearCombination ℚ K.transition

@[simp]
theorem
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.presentationOperator_single
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T)
    (x : CodimensionPoint X p) :
    K.presentationOperator (Finsupp.single x 1) = K.transition x := by
  simp [PointClassTransitionKernel.presentationOperator]

/-- The freely extended presentation operator intertwines the free point-class
map with the cohomological observable on every finite presentation. -/
theorem
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.finitePointClass_natural
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    (finitePointCycleClassMap p cl).comp K.presentationOperator =
      T.comp (finitePointCycleClassMap p cl) := by
  apply Finsupp.lhom_ext
  intro x q
  have hspec : (Finsupp.linearCombination ℚ
      (fun y => cl (codimensionPointCycle X p y))) (K.transition x)
      = T (cl (codimensionPointCycle X p x)) := K.transition_spec x
  simp [PointClassTransitionKernel.presentationOperator,
    finitePointCycleClassMap, hspec]

/-- Conjugate the free presentation operator through the compact cycle/
presentation equivalence to obtain an operator on all native cycles. -/
noncomputable def
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.nativeCycleOperator
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    codimensionCycles X p →ₗ[ℚ] codimensionCycles X p :=
  (compactCyclePresentationLinearEquiv X p).toLinearMap.comp
    (K.presentationOperator.comp
      (compactCyclePresentationLinearEquiv X p).symm.toLinearMap)

/-- **POINT KERNEL → FULL CYCLE-CLASS NATURALITY.**
The native cycle operator induced from the point-transition kernel commutes
exactly with the supplied cycle-class map on every native cycle. -/
theorem
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.nativeCycleOperator_natural
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    cl.comp K.nativeCycleOperator = T.comp cl := by
  apply LinearMap.ext
  intro Z
  let φ := presentationOfNativeCycle X p Z
  have hZ : realizeFiniteCodimensionPresentation X p φ = Z :=
    realize_presentationOfNativeCycle X p Z
  have hfree := LinearMap.congr_fun K.finitePointClass_natural φ
  change cl (K.nativeCycleOperator Z) = T (cl Z)
  rw [← hZ]
  simpa [PointClassTransitionKernel.nativeCycleOperator, φ,
    finitePointCycleClassMap_eq_cycleClass_realize,
    presentation_realizeFiniteCodimensionPresentation]
    using hfree

/-- Package the derived native operator and the original cohomological
observable into the exact commuting-square interface used by the constructive
spectral landing. -/
noncomputable def
    _root_.GSTClassicalHodgeGeneratorwiseAtomicStability.PointClassTransitionKernel.toCycleClassOperatorPair
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (K : PointClassTransitionKernel
      (p := p) (cl := H.cycleClass p) T) :
    CycleClassOperatorPair V H p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact {
    cycleOperator := K.nativeCycleOperator
    cohomologyOperator := T
    cycleClass_natural := K.nativeCycleOperator_natural
  }

/-- Every raw spectral observable equipped only with a point-transition kernel
therefore upgrades to the old full native spectral-cycle operator package. -/
noncomputable def
    GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable
      V H p ι)
    (K : S.PointTransitionKernel) :
    SpectralCycleOperator V H p ι where
  operatorPair := K.toCycleClassOperatorPair
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector

#check realizePresentationLinear
#check presentationOfNativeCycleLinear
#check presentation_realizeFiniteCodimensionPresentation
#check compactCyclePresentationLinearEquiv
#check PointClassTransitionKernel.presentationOperator
#check PointClassTransitionKernel.finitePointClass_natural
#check PointClassTransitionKernel.nativeCycleOperator
#check PointClassTransitionKernel.nativeCycleOperator_natural
#check PointClassTransitionKernel.toCycleClassOperatorPair
#check GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel

#print axioms presentation_realizeFiniteCodimensionPresentation
#print axioms compactCyclePresentationLinearEquiv
#print axioms PointClassTransitionKernel.finitePointClass_natural
#print axioms PointClassTransitionKernel.nativeCycleOperator_natural
#print axioms PointClassTransitionKernel.toCycleClassOperatorPair
#print axioms GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel

end GSTClassicalHodgePointKernelOperatorLift
