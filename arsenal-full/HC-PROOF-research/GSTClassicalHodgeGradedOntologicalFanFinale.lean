import GSTClassicalHodgeCodimensionZeroDegreeApex
import GSTClassicalHodgeRootedStrictRelationTree
import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — GRADED ONTOLOGICAL FAN FINALE

The upgraded GST Graph V2 picture is naturally read in three directions:

1. an apex at weight zero;
2. a vertical graded spine carrying one live state through successive Hodge
   weights;
3. horizontal/diagonal strict-relation rays fanning from the live state in each
   weight to all multiplicity directions.

All three mechanisms now exist independently in the repository:

* `codimensionZeroDegreeApex` constructs the weight-zero nonzero algebraic seed
  from one irreducible-component generic point and projective degree, with no
  principal-cut exactness premise;
* `SeedPropagationFamily` propagates algebraicity vertically through genuine
  graded native/cohomology transports;
* `RootedStrictRelationFan` propagates algebraicity horizontally from each live
  seed using only path-local raw strict relations, with no global omniverse
  compiler.

This file fuses those mechanisms.  The only remaining graded geometric burden
is explicit and local:

* one vertical pure-Lefschetz transport at each successor weight;
* one locally materialized strict-relation ray from the propagated seed to each
  target basis direction in that weight.

No independent algebraic seed is postulated at higher weights.  No native-mass
bridge, global primitive compiler, targetwise giant correspondence, cyclicity
axiom, or arbitrary basis-cycle family is used.
-/

set_option maxHeartbeats 140000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedOntologicalFanFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCodimensionZeroDegreeApex
open GSTClassicalHodgeRootedStrictRelationFan
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Any nonzero algebraic Hodge state can be converted back into the exact
native-orbit-seed interface by extracting one genuine cycle from the actual
cycle-class range. -/
noncomputable def orbitSeedOfAlgebraic
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (hne : alpha ≠ 0)
    (halg : alpha ∈ AlgebraicHodgeSubspace V H p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) := by
  have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := halg
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  rcases hrange with ⟨Z, hZ⟩
  exact {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := hne
    class_eq := hZ
  }

/-- The projective-degree apex is algebraic in the precise algebraic-Hodge
subspace consumed by vertical propagation. -/
theorem degreeApex_algebraic
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X] :
    (codimensionZeroDegreeApex G D).hodge ∈
      AlgebraicHodgeSubspace V H 0 := by
  have hrange :
      (codimensionZeroDegreeApex G D).hodge.1 ∈
        LinearMap.range (H.cycleClass 0) :=
    ⟨(codimensionZeroDegreeApex G D).cycle,
      (codimensionZeroDegreeApex G D).class_eq⟩
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H 0] at hrange
  exact hrange

/-- Turn a vertical propagation family whose zero state is the genuine degree
apex into a native nonzero algebraic orbit seed at EVERY weight. -/
noncomputable def propagatedOrbitSeed
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (F : SeedPropagationFamily V H)
    (hzero : F.seed 0 = (codimensionZeroDegreeApex G D).hodge)
    (p : Nat) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) := by
  have h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0 := by
    rw [hzero]
    exact degreeApex_algebraic G D
  have hp : F.seed p ∈ AlgebraicHodgeSubspace V H p :=
    F.algebraic_of_zero_seed h0 p
  exact orbitSeedOfAlgebraic (F.seed p) (F.seed_ne_zero p) hp

/-- The complete graded ontological fan.

The vertical family is the shared spine.  At each weight, `horizontal p` is a
path-local rooted fan whose apex is not separately supplied: it is extracted
from the vertically propagated algebraic seed. -/
structure GradedOntologicalFan
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X] where
  vertical : SeedPropagationFamily V H
  zero_eq : vertical.seed 0 = (codimensionZeroDegreeApex G D).hodge
  horizontal : ∀ p : Nat,
    RootedStrictRelationFan
      (propagatedOrbitSeed G D vertical zero_eq p)

namespace GradedOntologicalFan

/-- Every propagated apex is genuinely algebraic and nonzero; this is derived
from the one degree-certified weight-zero apex and the vertical spine. -/
theorem propagated_apex_algebraic
    (F : GradedOntologicalFan G D)
    (p : Nat) :
    AlgebraicBranchNode (V := V) (H := H) (p := p)
      (rootedFanApex
        (propagatedOrbitSeed G D F.vertical F.zero_eq p)) :=
  rootedFanApex_algebraic
    (propagatedOrbitSeed G D F.vertical F.zero_eq p)

/-- Each individual Hodge weight is closed by its rooted strict-relation fan. -/
theorem hodge_weight
    (F : GradedOntologicalFan G D)
    (p : Nat) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  hodge_weight_of_rootedStrictRelationFan
    (propagatedOrbitSeed G D F.vertical F.zero_eq p)
    (F.horizontal p)

/-- **GRADED ONTOLOGICAL FAN CROWN.**
The apex + vertical spine + horizontal relation rays prove the actual Stage-2G
rational Hodge statement in every weight. -/
theorem bigradedBettiHodge
    (F : GradedOntologicalFan G D) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact F.hodge_weight p halpha

/-- Literal rational Hodge statement: every rational Hodge class is represented
by an actual rational algebraic cycle. -/
theorem everyHodgeClassIsRationalAlgebraic
    (F : GradedOntologicalFan G D) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).2
  exact F.bigradedBettiHodge

/-- Exact finite rational-combination form. -/
theorem everyHodgeClassIsFiniteRationalCombination
    (F : GradedOntologicalFan G D) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  apply (rationalAlgebraic_iff_finiteRationalCombination H).1
  exact F.everyHodgeClassIsRationalAlgebraic

/-- Elementwise constructive terminal form. -/
theorem hodgeClass_has_nativeCycle
    (F : GradedOntologicalFan G D)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha :=
  F.everyHodgeClassIsRationalAlgebraic p alpha halpha

end GradedOntologicalFan

#check orbitSeedOfAlgebraic
#check degreeApex_algebraic
#check propagatedOrbitSeed
#check GradedOntologicalFan
#check GradedOntologicalFan.propagated_apex_algebraic
#check GradedOntologicalFan.hodge_weight
#check GradedOntologicalFan.bigradedBettiHodge
#check GradedOntologicalFan.everyHodgeClassIsRationalAlgebraic
#check GradedOntologicalFan.everyHodgeClassIsFiniteRationalCombination
#check GradedOntologicalFan.hodgeClass_has_nativeCycle

#print axioms orbitSeedOfAlgebraic
#print axioms propagatedOrbitSeed
#print axioms GradedOntologicalFan.bigradedBettiHodge
#print axioms GradedOntologicalFan.everyHodgeClassIsRationalAlgebraic
#print axioms GradedOntologicalFan.hodgeClass_has_nativeCycle

end GSTClassicalHodgeGradedOntologicalFanFinale
