import GSTClassicalHodgeFullLimitlessExternalization
import GSTClassicalHodgeGeneratorwiseAtomicStability
import GSTClassicalHodgePointKernelOperatorLift
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeFullLimitlessCrown
import GSTClassicalHodgeConcreteFailureDichotomy
import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

/-!
# GST CLASSICAL HODGE — POINTWISE LIMITLESS COSMIC EXTERNALIZATION

The previous full-limitless externalization interface asks one genuine
projective correspondence to agree with the canonical cosmic matrix unit on
*every vector of the Hodge fiber*.  That is much stronger than the no-escape
argument consumes.

The algebraic Hodge fiber is the span of genuine codimension-p point-cycle
classes.  A projective correspondence already preserves that atomic span by
its exact native/cycle-class commuting square.  Therefore it is enough to
identify its cosmic action on the point generators themselves.  Linearity then
forces equality on the entire algebraic fiber, which is precisely the domain
on which canonical cosmic naturality must be proved.

This file pushes the reduction one step further.  A `ProjectiveNativeKernel`
already carries a canonical *finite point presentation* for the image of every
genuine point atom.  Hence the final externalization law may be stated purely
as a finite transition equation:

  class(finite transition of x) = cosmic E_ij(class(x)).

No comparison on arbitrary Hodge vectors, no basis-cycle representative, and
no cycle-class surjectivity statement is requested.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePointwiseCosmicExternalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCanonicalCosmicRealizationEquivalence
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeFullLimitlessExternalization
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Native point-generator form of one cosmic externalization law. -/
def PointAtomCosmicExternalization
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    H.cycleClass p
        (ProjectiveNativeKernel.operator V p K
            (codimensionPointCycle V.X p x)) =
      canonicalCosmicAmbient i j
        (H.cycleClass p (codimensionPointCycle V.X p x))

/-- Strongest finite form: the canonical finite point transition already
carried by the projective kernel has exactly the required cosmic cycle class. -/
def FinitePointCosmicExternalization
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    finitePointCycleClassMap p (H.cycleClass p)
      (ProjectiveNativeKernel.transition V p K x) =
      canonicalCosmicAmbient i j
        (H.cycleClass p (codimensionPointCycle V.X p x))

/-- Finite transition externalization implies the native point-atom law. -/
theorem pointAtom_of_finitePoint
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p)
    (hK : FinitePointCosmicExternalization (H := H) i j K) :
    PointAtomCosmicExternalization (H := H) i j K := by
  intro x
  have hreal := ProjectiveNativeKernel.transition_realize V p K x
  calc
    H.cycleClass p
        (ProjectiveNativeKernel.operator V p K
            (codimensionPointCycle V.X p x)) =
      H.cycleClass p
        (realizeFiniteCodimensionPresentation V.X p
          (ProjectiveNativeKernel.transition V p K x)) := by
          have hreal' :
              realizeFiniteCodimensionPresentation V.X p
                (ProjectiveNativeKernel.transition V p K x) =
                ProjectiveNativeKernel.operator V p K
                  (codimensionPointCycle V.X p x) := hreal
          rw [hreal']
    _ = finitePointCycleClassMap p (H.cycleClass p)
      (ProjectiveNativeKernel.transition V p K x) := by
          symm
          exact finitePointCycleClassMap_eq_cycleClass_realize
            p (H.cycleClass p) (ProjectiveNativeKernel.transition V p K x)
    _ = canonicalCosmicAmbient i j
        (H.cycleClass p (codimensionPointCycle V.X p x)) := hK x

/-- The projective correspondence pair agrees with the canonical cosmic action
on every point-cycle generator as soon as its native operator does. -/
theorem projectivePair_agrees_on_points
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p)
    (hK : PointAtomCosmicExternalization (H := H) i j K) :
    ∀ x : CodimensionPoint V.X p,
      (projectiveCorrespondencePair G K).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) =
        canonicalCosmicAmbient i j
          (H.cycleClass p (codimensionPointCycle V.X p x)) := by
  intro x
  have hnat :=
    (projectiveCorrespondencePair G K).cycleClass_cycleOperator
      (codimensionPointCycle V.X p x)
  have hnative := hK x
  change
    H.cycleClass p
        (ProjectiveNativeKernel.operator V p K
            (codimensionPointCycle V.X p x)) =
      (projectiveCorrespondencePair G K).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) at hnat
  exact hnat.symm.trans hnative

/-- Equality on point generators extends to equality on the complete actual
atomic cycle-class span. -/
theorem projectivePair_agrees_on_atomicSpan
    (G : GeometricCycleClassSpine V H)
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : ProjectiveNativeKernel V p)
    (hK : PointAtomCosmicExternalization (H := H) i j K) :
    ∀ y,
      y ∈ pointCycleClassSpan p (H.cycleClass p) →
      (projectiveCorrespondencePair G K).cohomologyOperator y =
        canonicalCosmicAmbient i j y := by
  let D : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * p)) :=
    (projectiveCorrespondencePair G K).cohomologyOperator -
      canonicalCosmicAmbient i j
  have hspan :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker D := by
    rw [pointCycleClassSpan, Submodule.span_le]
    rintro y ⟨x, rfl⟩
    simp only [LinearMap.mem_ker]
    change
      (projectiveCorrespondencePair G K).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) -
        canonicalCosmicAmbient i j
          (H.cycleClass p (codimensionPointCycle V.X p x)) = 0
    rw [projectivePair_agrees_on_points G i j K hK x]
    simp
  intro y hy
  have hzero : D y = 0 := LinearMap.mem_ker.mp (hspan hy)
  change
    (projectiveCorrespondencePair G K).cohomologyOperator y -
      canonicalCosmicAmbient i j y = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- **POINTWISE EXTERNALIZATION -> CANONICAL COSMIC NATURALITY.**

The point-generator law is enough for the actual no-escape invariant.  The
projective correspondence preserves the atomic span automatically; equality
with the cosmic action is then needed only on vectors already lying in that
span. -/
theorem canonicalCosmicNaturality_of_pointAtomExternalization
    (G : GeometricCycleClassSpine V H)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      PointAtomCosmicExternalization (H := H) i j (K i j)) :
    CanonicalCosmicNaturality (V := V) (H := H) p := by
  intro i j alpha halpha
  have hpairAtomic :
      (projectiveCorrespondencePair G (K i j)).cohomologyOperator alpha.1 ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    (projectiveCorrespondencePair G (K i j)).atomicSpan_stable alpha.1 halpha
  have hagree :=
    projectivePair_agrees_on_atomicSpan G i j (K i j) (hK i j)
      alpha.1 halpha
  rw [hagree, canonicalCosmicAmbient_on_hodge i j alpha] at hpairAtomic
  exact hpairAtomic

/-- Finite point-transition equations are already enough for canonical cosmic
naturality. -/
theorem canonicalCosmicNaturality_of_finitePointExternalization
    (G : GeometricCycleClassSpine V H)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      FinitePointCosmicExternalization (H := H) i j (K i j)) :
    CanonicalCosmicNaturality (V := V) (H := H) p := by
  apply canonicalCosmicNaturality_of_pointAtomExternalization G K
  intro i j
  exact pointAtom_of_finitePoint i j (K i j) (hK i j)

/-- One nonzero algebraic seed plus finite point-transition externalization
saturates the complete genuine Hodge fiber in the requested weight. -/
theorem hodge_weight_of_finitePointExternalization
    (G : GeometricCycleClassSpine V H)
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p)
    (hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      FinitePointCosmicExternalization (H := H) i j (K i j)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact GSTClassicalHodgeCanonicalLimitlessNaturalityCrown.hodge_weight
    hseed (canonicalCosmicNaturality_of_finitePointExternalization G K hK)

/-- Family form for the complete Stage-2G target. -/
theorem bigradedBettiHodge_of_spine_and_finitePointExternalization
    (G : GeometricCycleClassSpine V H)
    (hNV : GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (K : ∀ p : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H p,
        ProjectiveNativeKernel V p)
    (hK : ∀ p : Nat,
      ∀ i j : ClassicalHodgeBasisIndex V H p,
        FinitePointCosmicExternalization (H := H) i j (K p i j)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  by_cases hH : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥
  · have hz : alpha = 0 := by
      have : alpha ∈ (⊥ : Submodule ℚ
          (RationalSingularCohomology H.analytification (2 * q))) := by
        simpa [hH] using halpha
      simpa using this
    subst alpha
    exact ⟨0, by simp⟩
  · have hseed : AlgebraicFiber (V := V) (H := H) (p := q) ≠ ⊥ :=
      GSTClassicalHodgeFullLimitlessCrown.algebraicFiber_ne_bot_of_spineTower
        G hNV q hH
    exact hodge_weight_of_finitePointExternalization
      G hseed (K q) (hK q) halpha

#check PointAtomCosmicExternalization
#check FinitePointCosmicExternalization
#check pointAtom_of_finitePoint
#check projectivePair_agrees_on_points
#check projectivePair_agrees_on_atomicSpan
#check canonicalCosmicNaturality_of_pointAtomExternalization
#check canonicalCosmicNaturality_of_finitePointExternalization
#check hodge_weight_of_finitePointExternalization
#check bigradedBettiHodge_of_spine_and_finitePointExternalization

#print axioms pointAtom_of_finitePoint
#print axioms projectivePair_agrees_on_atomicSpan
#print axioms canonicalCosmicNaturality_of_pointAtomExternalization
#print axioms canonicalCosmicNaturality_of_finitePointExternalization
#print axioms hodge_weight_of_finitePointExternalization
#print axioms bigradedBettiHodge_of_spine_and_finitePointExternalization

end GSTClassicalHodgePointwiseCosmicExternalization
