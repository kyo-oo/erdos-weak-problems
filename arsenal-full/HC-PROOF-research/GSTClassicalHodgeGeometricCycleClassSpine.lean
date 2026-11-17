import GSTClassicalHodgePrimitivePushforwardNaturality
import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgePrincipalCutSuccessorOperator
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import GSTClassicalHodgeStage2GSemanticRigidity

/-!
# GST CLASSICAL HODGE — GENUINE GEOMETRIC CYCLE-CLASS SPINE

The Stage-2G carrier intentionally separated the formal Hodge bigrading from
its still-unconstrained cycle-class map.  The limitless GST proof cannot close
against an arbitrary linear map: the zero-map countermodel proves that inside
Lean.

This module records the geometric laws that distinguish the genuine classical
cycle-class construction from that arbitrary placeholder.  These laws are
standard independent properties of the classical cycle-class formalism; none
of them says that all Hodge classes are algebraic.

The spine has three arteries:

* every algebraic codimension-p cycle has Hodge type (p,p);
* actual projective algebraic transports satisfy the genuine cycle-class
  naturality square;
* the already-constructed projective principal-cut successor is compatible
  with the corresponding graded cohomological Lefschetz transport.

The limitless GST machinery may use these laws as geometric semantics, but no
surjectivity, basis-cycle representative, defect-zero conclusion, or Hodge
conjecture is stored here.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeGeometricCycleClassSpine

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeCodimensionZeroFundamentalCycle

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Genuine geometric semantics for the classical cycle-class map used by the
Hodge landing.  Every field is a standard functorial/type property of cycle
classes; no algebraicity-surjectivity statement occurs. -/
structure GeometricCycleClassSpine
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  /-- Algebraic cycles have Hodge type `(p,p)`. -/
  algebraic_is_hodge :
    ∀ p : Nat, ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)

  /-- Proper/projective self-transport is compatible with cycle classes. -/
  pushforward_naturality :
    ∀ p : Nat, ∀ f : V.X ⟶ V.X,
      GeometricPushforwardNaturality V H p f

  /-- The genuine projective principal-cut successor has a graded
  cohomological realization with an exact cycle-class commuting square. -/
  principalCutPair :
    ∀ p : Nat,
      GradedCycleClassOperatorPair V H p (p + 1)

  /-- The native side of that graded pair is exactly the geometry-built
  principal-cut successor operator. -/
  principalCutPair_native :
    ∀ p : Nat,
      (principalCutPair p).cycleOperator =
        successorNativeOperator V p

  /-- Principal-cut/Lefschetz transport preserves the genuine Hodge sector. -/
  principalCut_hodge :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      (principalCutPair p).cohomologyOperator alpha ∈
        rationalHodgeSubspace (H.hodgeBigrading (p + 1))

namespace GeometricCycleClassSpine

/-- Every genuine point-cycle class is automatically a true Hodge class. -/
theorem pointClass_is_hodge
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    H.cycleClass p (codimensionPointCycle V.X p x) ∈
      rationalHodgeSubspace (H.hodgeBigrading p) :=
  G.algebraic_is_hodge p _

/-- Every actual projective self-map yields a complete genuine cycle/cohomology
operator pair, with no separately supplied kernel-stability hypothesis. -/
noncomputable def projectiveOperatorPair
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (f : V.X ⟶ V.X) :=
  (G.pushforward_naturality p f).operatorPair

/-- The complete rational projective-correspondence span inherits kernel
stability from primitive geometric functoriality. -/
theorem correspondenceSpan_kernelStable
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    ∀ A : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.NativeCycleEnd V p,
      A ∈ GSTClassicalHodgeProjectiveCorrespondenceAlgebra.projectiveCorrespondenceSpan V p →
        GSTClassicalHodgeNativeOperatorCohomologyRealization.KernelStable
          (H := H) A := by
  exact projectiveCorrespondenceSpan_kernelStable
    (fun f => G.pushforward_naturality p f)

/-- The principal-cut pair transports an algebraic Hodge class to an algebraic
Hodge class in the next weight. -/
theorem principalCut_maps_algebraic_hodge
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)
    (halg : alpha ∈
      GSTClassicalHodgeRankFreeArsenalIrreducibility.AlgebraicHodgeSubspace V H p) :
    (⟨(G.principalCutPair p).cohomologyOperator alpha.1,
        G.principalCut_hodge p alpha.1 alpha.2⟩ :
      GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)) ∈
      GSTClassicalHodgeRankFreeArsenalIrreducibility.AlgebraicHodgeSubspace
        V H (p + 1) := by
  exact (G.principalCutPair p).maps_algebraic_hodge
    alpha halg (G.principalCut_hodge p alpha.1 alpha.2)

/-- The canonical codimension-zero fundamental cycle has Hodge type `(0,0)`.
This provides the geometric origin from which the graded limitless tower can
propagate. -/
theorem codimensionZeroFundamentalClass_is_hodge
    (G : GeometricCycleClassSpine V H) :
    H.cycleClass 0 (codimensionZeroFundamentalCycle V) ∈
      rationalHodgeSubspace (H.hodgeBigrading 0) :=
  G.algebraic_is_hodge 0 _

end GeometricCycleClassSpine

/-! ## Semantic separation of the spine itself

The spine laws are compatibility laws.  Compatibility with an unspecified
cohomological action does not by itself fix the cycle-class map: zero still
satisfies every field.  The following construction keeps the native principal
cut exactly as defined; it does not replace native geometry by a zero operator.
-/

/-- The existing zero-cycle-class datum satisfies every current spine law.
Thus a spine is not, by itself, a construction of the geometric cycle class. -/
noncomputable def zeroCycleClassSpine
    (H : HodgeBigradedBettiData V) :
    GeometricCycleClassSpine V
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H) where
  algebraic_is_hodge := by
    intro p Z
    exact Submodule.zero_mem _
  pushforward_naturality := fun p f => {
    cohomologyPushforward := 0
    naturality := by intro Z; rfl
  }
  principalCutPair := fun p => {
    cycleOperator := successorNativeOperator V p
    cohomologyOperator := 0
    cycleClass_natural := by intro Z; rfl
  }
  principalCutPair_native := by intro p; rfl
  principalCut_hodge := by
    intro p alpha halpha
    exact Submodule.zero_mem _

/-- A nonzero Hodge fiber gives a counterexample even after supplying all
current spine laws.  This is about the formal interface, not about the actual
geometrically defined cycle-class map. -/
theorem spine_laws_do_not_force_hodge
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    Nonempty (GeometricCycleClassSpine V
      (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H)) ∧
      ¬ BigradedBettiHodgeStatement V
        (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H) := by
  exact ⟨⟨zeroCycleClassSpine H⟩,
    GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H p alpha halpha halpha0⟩

#print axioms zeroCycleClassSpine
#print axioms spine_laws_do_not_force_hodge

#check GeometricCycleClassSpine
#check GeometricCycleClassSpine.pointClass_is_hodge
#check GeometricCycleClassSpine.projectiveOperatorPair
#check GeometricCycleClassSpine.correspondenceSpan_kernelStable
#check GeometricCycleClassSpine.principalCut_maps_algebraic_hodge
#check GeometricCycleClassSpine.codimensionZeroFundamentalClass_is_hodge

#print axioms GeometricCycleClassSpine.principalCut_maps_algebraic_hodge
#print axioms GeometricCycleClassSpine.codimensionZeroFundamentalClass_is_hodge

end GSTClassicalHodgeGeometricCycleClassSpine
