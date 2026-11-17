import GSTClassicalHodgeFiniteClosedCorrespondence
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — FINITE CLOSED CORRESPONDENCE OPERATORS

`GSTClassicalHodgeFiniteClosedCorrespondence` constructs the genuinely
geometric point image of a finite closed correspondence in `X × X`.  This
module promotes that point action to the whole native codimension-p cycle
space.

The construction is geometry first:

1. enumerate the finite left fiber of the closed correspondence;
2. push each fiber point through the right projection with its genuine right
   residue-degree weight;
3. extend that transition freely over finite point presentations;
4. conjugate through the compact cycle/presentation equivalence.

No Hodge-basis read/write map is used in the native operator.

We then prove two structural facts.

* Graph consistency: the corrected graph correspondence recovers the existing
  native pushforward of its endomorphism.
* Pointwise cohomology realization: if a cohomological operator agrees with
  the correspondence on genuine point cycles, the point-kernel theorem
  upgrades this automatically to an exact cycle-class-natural operator pair
  on ALL native cycles.

Finally we admit finite rational correspondence cycles.  This is the correct
linear arena for algebraic correspondences: subtraction and rational scaling
occur at the correspondence-cycle level rather than as arbitrary Hodge
coordinate operators.  It strictly enlarges the old span generated only by
scheme endomorphism graphs while respecting Astra's native-descent
obstruction.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

set_option allowUnsafeReducibility true in
attribute [local reducible]
  GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.graphCorrespondence

namespace GSTClassicalHodgeFiniteClosedCorrespondenceOperator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeAtomicSpan

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

end GSTClassicalHodgeFiniteClosedCorrespondenceOperator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeAtomicSpan

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence

/-- Free linear extension of the finite-correspondence transition from point
atoms to arbitrary finite point presentations. -/
noncomputable def presentationOperator
    (K : FiniteClosedCorrespondence V)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X p :=
  Finsupp.linearCombination ℚ (K.transition p)

@[simp]
theorem presentationOperator_single
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    K.presentationOperator p (Finsupp.single x 1) = K.transition p x := by
  simp [presentationOperator]

/-- **GENUINE CORRESPONDENCE NATIVE OPERATOR.**
Conjugate the free point-transition operator through the exact compact
cycle/presentation linear equivalence. -/
noncomputable def nativeOperator
    (K : FiniteClosedCorrespondence V)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (compactCyclePresentationLinearEquiv V.X p).toLinearMap.comp
    ((K.presentationOperator p).comp
      (compactCyclePresentationLinearEquiv V.X p).symm.toLinearMap)

/-- The promoted native operator has exactly the originally constructed
correspondence action on every genuine point atom. -/
theorem nativeOperator_point
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    K.nativeOperator p (codimensionPointCycle V.X p x) =
      K.nativePointImage p x := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeOperator, nativePointImage,
    compactCyclePresentationLinearEquiv,
    presentationOfNativeCycle_point,
    presentationOperator,
    Finsupp.linearCombination_apply,
    realizeFiniteCodimensionPresentation,
    realizePresentationLinear]

/-! ## Graph consistency -/

/-- The left fiber of a graph correspondence is literally the singleton
containing the source point. -/
theorem graphCorrespondence_leftFiberFinset
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (x : V.X) :
    (graphCorrespondence f).leftFiberFinset x =
      @Finset.cons ↥(graphCorrespondence f).carrier x
        (∅ : Finset ↥(graphCorrespondence f).carrier)
        (Finset.notMem_empty x) := by
  classical
  ext z
  have hmem : z ∈ (graphCorrespondence f).leftFiberFinset x ↔
      (graphCorrespondence f).left z = x :=
    mem_leftFiberFinset (graphCorrespondence f) x z
  rw [hmem]
  simp [graphCorrespondence_left, ConcreteCategory.id_apply]

/-- The corrected target atom of a graph is exactly the genuine point
pushforward presentation of the underlying endomorphism. -/
theorem graphCorrespondence_targetAtom_eq_pointPushforward
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (graphCorrespondence f).targetAtomPresentation p x.1 =
      pointPushforwardPresentation f.hom p x := by
  classical
  simp [targetAtomPresentation, pointPushforwardPresentation,
    graphCorrespondence_right] <;> rfl

/-- Consequently the full graph transition agrees with the old point
pushforward transition. -/
theorem graphCorrespondence_transition_eq_pointPushforward
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (graphCorrespondence f).transition p x =
      pointPushforwardPresentation f.hom p x := by
  classical
  rw [transition_eq_fiber_sum]
  have hc : (graphCorrespondence f).leftFiberFinset x.1 =
      @Finset.cons ↥(graphCorrespondence f).carrier (x.1 : (graphCorrespondence f).carrier)
        (∅ : Finset ↥(graphCorrespondence f).carrier)
        (Finset.notMem_empty (x.1 : (graphCorrespondence f).carrier)) :=
    graphCorrespondence_leftFiberFinset f (x.1 : (graphCorrespondence f).carrier)
  rw [hc]
  simp
  exact graphCorrespondence_targetAtom_eq_pointPushforward f p x

/-- Pointwise native graph action is exactly the existing genuine native
pushforward. -/
theorem graphCorrespondence_nativePointImage_eq
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (graphCorrespondence f).nativePointImage p x =
      nativePointPushforward f.hom p x := by
  unfold nativePointImage nativePointPushforward
  rw [graphCorrespondence_transition_eq_pointPushforward]

/-- At the operator level, graph correspondences recover the old projective
endomorphism pushforward exactly. -/
theorem graphCorrespondence_nativeOperator_eq_pushforward
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (p : Nat) :
    (graphCorrespondence f).nativeOperator p =
      smoothProjectiveNativePushforward V f.hom p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  apply LinearMap.ext
  intro Z
  let φ := presentationOfNativeCycle V.X p Z
  have hZ : realizeFiniteCodimensionPresentation V.X p φ = Z :=
    realize_presentationOfNativeCycle V.X p Z
  rw [← hZ]
  classical
  simp [nativeOperator, presentationOperator,
    smoothProjectiveNativePushforward,
    realizePushforwardPresentation,
    compactCyclePresentationLinearEquiv,
    presentation_realizeFiniteCodimensionPresentation,
    Finsupp.linearCombination_apply,
    realizeFiniteCodimensionPresentation,
    pushforwardPresentation,
    realizePresentationLinear,
    graphCorrespondence_transition_eq_pointPushforward]

/-! ## Exact cohomological realization from point geometry -/

/-- A cohomological operator is realized by K on points when its action on
every genuine point-cycle class is exactly the class of K's genuine finite
correspondence image. -/
def RealizesAmbientOnPoints
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    H.cycleClass p (K.nativePointImage p x) =
      T (H.cycleClass p (codimensionPointCycle V.X p x))

/-- Turn a genuine finite closed correspondence plus its pointwise
cohomological realization theorem into the repository's exact point-class
transition kernel. -/
noncomputable def pointTransitionKernel
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hKT : K.RealizesAmbientOnPoints (H := H) T) :
    PointClassTransitionKernel (p := p) (cl := H.cycleClass p) T where
  transition := K.transition p
  transition_spec := by
    intro x
    rw [finitePointCycleClassMap_eq_cycleClass_realize]
    exact hKT x

/-- **POINTWISE CLOSED CORRESPONDENCE ⇒ FULL NATURALITY.**
Agreement only on genuine point atoms automatically upgrades to an exact
cycle-class commuting square on every native cycle. -/
noncomputable def toCycleClassOperatorPair
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hKT : K.RealizesAmbientOnPoints (H := H) T) :
    CycleClassOperatorPair V H p :=
  (K.pointTransitionKernel T hKT).toCycleClassOperatorPair

/-- The cycle operator manufactured by point-kernel naturality is the same
native correspondence operator constructed directly from K. -/
theorem toCycleClassOperatorPair_cycleOperator
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hKT : K.RealizesAmbientOnPoints (H := H) T) :
    (K.toCycleClassOperatorPair T hKT).cycleOperator = K.nativeOperator p := by
  rfl

/-- Full cycle-class naturality written directly for the genuine closed
correspondence operator. -/
theorem cycleClass_nativeOperator
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hKT : K.RealizesAmbientOnPoints (H := H) T)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (K.nativeOperator p Z) = T (H.cycleClass p Z) := by
  have h := LinearMap.congr_fun
    (K.toCycleClassOperatorPair T hKT).cycleClass_natural Z
  have hcoe : (K.toCycleClassOperatorPair T hKT).cohomologyOperator = T := rfl
  rw [hcoe, toCycleClassOperatorPair_cycleOperator] at h
  exact h

/-! ## Rational cycles of genuine closed correspondences -/

/-- Finite rational linear combinations of genuine finite closed
correspondences.  This is the algebraic-cycle level at which subtraction and
normalization belong. -/
abbrev RationalClosedCorrespondenceCycle
    (V : SmoothProjectiveComplexScheme) :=
  FiniteClosedCorrespondence V →₀ ℚ

/-- Native operator carried by a rational finite correspondence cycle. -/
noncomputable def correspondenceCycleNativeOperator
    (A : RationalClosedCorrespondenceCycle V)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  A.sum fun K q => q • K.nativeOperator p

@[simp]
theorem correspondenceCycleNativeOperator_single
    (K : FiniteClosedCorrespondence V)
    (q : ℚ)
    (p : Nat) :
    correspondenceCycleNativeOperator (Finsupp.single K q) p =
      q • K.nativeOperator p := by
  classical
  simp [correspondenceCycleNativeOperator]

/-- A single graph correspondence embeds the old endomorphism sector into the
new rational closed-correspondence cycle sector. -/
noncomputable def graphCorrespondenceCycle
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    RationalClosedCorrespondenceCycle V :=
  Finsupp.single (graphCorrespondence f) 1

/-- The native operator of a graph correspondence cycle is exactly the old
native projective pushforward. -/
theorem graphCorrespondenceCycle_nativeOperator
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (p : Nat) :
    correspondenceCycleNativeOperator (graphCorrespondenceCycle f) p =
      smoothProjectiveNativePushforward V f.hom p := by
  classical
  rw [graphCorrespondenceCycle, correspondenceCycleNativeOperator_single,
    one_smul, graphCorrespondence_nativeOperator_eq_pushforward]

#check FiniteClosedCorrespondence.presentationOperator
#check FiniteClosedCorrespondence.nativeOperator
#check FiniteClosedCorrespondence.nativeOperator_point
#check FiniteClosedCorrespondence.graphCorrespondence_nativeOperator_eq_pushforward
#check FiniteClosedCorrespondence.RealizesAmbientOnPoints
#check FiniteClosedCorrespondence.pointTransitionKernel
#check FiniteClosedCorrespondence.toCycleClassOperatorPair
#check FiniteClosedCorrespondence.cycleClass_nativeOperator
#check RationalClosedCorrespondenceCycle
#check correspondenceCycleNativeOperator
#check graphCorrespondenceCycle_nativeOperator

#print axioms FiniteClosedCorrespondence.nativeOperator_point
#print axioms FiniteClosedCorrespondence.graphCorrespondence_nativeOperator_eq_pushforward
#print axioms FiniteClosedCorrespondence.cycleClass_nativeOperator
#print axioms graphCorrespondenceCycle_nativeOperator

end GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence
