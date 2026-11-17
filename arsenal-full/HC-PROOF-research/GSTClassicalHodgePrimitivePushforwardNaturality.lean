import GSTClassicalHodgeKernelStableOperatorAlgebra
import GSTClassicalHodgeProjectivePointTransport
import GSTClassicalHodgeGeneratorwiseAtomicStability

/-!
# GST CLASSICAL HODGE — PRIMITIVE PUSHFORWARD NATURALITY

The projective correspondence algebra should not carry kernel-stability as an
independent property.  For an actual scheme endomorphism `f : X ⟶ X`, it is
enough to know the standard primitive geometric square: the cohomological
pushforward of the class of a native cycle equals the class of the native
pushforward cycle.

This module proves that this primitive square immediately implies kernel
stability, atomic-span stability, and the canonical ambient cohomological
realization of the corresponding projective operator.  Because the previous
operator-algebra module closes kernel stability under rational combinations,
checking functoriality on actual geometric generators is sufficient for the
entire correspondence algebra.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeKernelStableOperatorAlgebra

namespace GSTClassicalHodgePrimitivePushforwardNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Primitive functoriality square for one actual scheme endomorphism.  This is
strictly an operator-naturality law: it does not assert that any new Hodge
class is algebraic. -/
structure GeometricPushforwardNaturality
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (f : V.X ⟶ V.X) where
  cohomologyPushforward :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  naturality :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass p (smoothProjectiveNativePushforward V f p Z) =
        cohomologyPushforward (H.cycleClass p Z)

namespace GeometricPushforwardNaturality

/-- Primitive functoriality forces kernel preservation of the actual native
pushforward. -/
theorem kernelStable
    {f : V.X ⟶ V.X}
    (N : GeometricPushforwardNaturality V H p f) :
    KernelStable (H := H) (smoothProjectiveNativePushforward V f p) := by
  intro Z hZ
  rw [N.naturality, hZ]
  exact N.cohomologyPushforward.map_zero

/-- The actual scheme pushforward and supplied functorial cohomology action
form a complete cycle-class operator pair. -/
noncomputable def operatorPair
    {f : V.X ⟶ V.X}
    (N : GeometricPushforwardNaturality V H p f) :
    GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair V H p where
  cycleOperator := smoothProjectiveNativePushforward V f p
  cohomologyOperator := N.cohomologyPushforward
  cycleClass_natural := by
    ext Z
    exact N.naturality Z

/-- Hence the genuine atomic point-cycle span is stable under the geometric
cohomology pushforward. -/
theorem atomicSpan_stable
    {f : V.X ⟶ V.X}
    (N : GeometricPushforwardNaturality V H p f) :
    ∀ x,
      x ∈ GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) →
        N.cohomologyPushforward x ∈
          GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) :=
  N.operatorPair.atomicSpan_stable

end GeometricPushforwardNaturality

/-- If primitive cycle-class functoriality is available for every actual
scheme endomorphism, every generator of the projective correspondence algebra
is kernel-stable. -/
theorem all_geometricGenerators_kernelStable
    (N : ∀ f : V.X ⟶ V.X,
      GeometricPushforwardNaturality V H p f) :
    ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (geometricGenerator V p f) := by
  intro f
  simpa [geometricGenerator] using (N f).kernelStable

/-- Therefore the entire rational projective correspondence span is
kernel-stable. -/
theorem projectiveCorrespondenceSpan_kernelStable
    (N : ∀ f : V.X ⟶ V.X,
      GeometricPushforwardNaturality V H p f) :
    ∀ A : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.NativeCycleEnd V p,
      A ∈ projectiveCorrespondenceSpan V p →
        KernelStable (H := H) A :=
  projectiveCorrespondence_kernelStable
    (all_geometricGenerators_kernelStable N)

/-- Every projective-correspondence operator consequently obtains a canonical
ambient cohomology realization with exact cycle-class naturality. -/
noncomputable def correspondenceOperatorPair
    (N : ∀ f : V.X ⟶ V.X,
      GeometricPushforwardNaturality V H p f)
    (K : ProjectiveNativeKernel V p) :=
  projectiveKernelToOperatorPair K
    (projectiveCorrespondenceSpan_kernelStable N K.1 K.2)

#check GeometricPushforwardNaturality
#check GeometricPushforwardNaturality.kernelStable
#check GeometricPushforwardNaturality.operatorPair
#check GeometricPushforwardNaturality.atomicSpan_stable
#check all_geometricGenerators_kernelStable
#check projectiveCorrespondenceSpan_kernelStable
#check correspondenceOperatorPair

#print axioms GeometricPushforwardNaturality.kernelStable
#print axioms GeometricPushforwardNaturality.atomicSpan_stable
#print axioms projectiveCorrespondenceSpan_kernelStable
#print axioms correspondenceOperatorPair

end GSTClassicalHodgePrimitivePushforwardNaturality
