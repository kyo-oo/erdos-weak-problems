import GSTClassicalHodgeSuccessorSeedEscapeDichotomy
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgePointClosurePrincipalCut
import GSTClassicalHodgeHeightOneProjectiveRelevance
import GSTClassicalHodgeSeparatorRelativeCoheightOne
import GSTClassicalHodgeRelativeSuccessorNonempty
import GSTClassicalHodgeFiberedCosmology
import GSTClassicalHodgeSuccessorGroundFloor

/-!
# GST CLASSICAL HODGE — PROJECTIVE DEGREE / BETTI TRACE ARTERY

Stage 2F fixes the actual Betti carrier to rational singular cohomology, but the
current semantic package does not yet expose the classical projective degree
pairing.  This file adds exactly that missing geometric artery and nothing
stronger.

For every codimension q there is a rational Betti trace functional obtained in
classical geometry by pairing with a complementary power of an ample
hyperplane class and evaluating on the projective fundamental class.  A unit
cycle supported on an irreducible codimension-q projective subvariety is sent
to its projective degree, which is strictly positive.

We package only these independent degree facts:

* one rational-linear Betti trace in each codimension;
* the projective degree of every native codimension point is positive;
* tracing its genuine cycle class gives exactly that projective degree.

No Hodge-surjectivity, basis representative, matrix-unit naturality, or Hodge
conclusion is stored here.

The payoff is immediate for the geometry-built principal-cut successor.  Its
finite presentation has coefficients 0 or +1.  Hence one exact surviving
successor gives strictly positive projective degree.  By trace compatibility
its Betti cycle class cannot vanish.  The `PositiveCosmicHomologyEscape` from
the preceding reduction is therefore impossible for separator successors once
this standard projective-degree semantics is materialized.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeProjectiveDegreeTrace

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Genuine projective degree semantics for the actual Betti cycle-class map.
The intended realization of `trace q` is cup product with a complementary
power of the hyperplane class followed by integration over the projective
fundamental class. -/
structure ProjectiveDegreeTraceSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  trace : ∀ q : Nat,
    RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ
  pointDegree : ∀ q : Nat, CodimensionPoint V.X q → ℚ
  pointDegree_pos : ∀ q (x : CodimensionPoint V.X q),
    0 < pointDegree q x
  trace_point_cycleClass : ∀ q (x : CodimensionPoint V.X q),
    trace q (H.cycleClass q (codimensionPointCycle V.X q x)) =
      pointDegree q x

namespace ProjectiveDegreeTraceSemantics

/-- Trace of any finite native point presentation is the corresponding
weighted sum of positive projective point-degrees. -/
theorem trace_realize_presentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (φ : FiniteCodimensionPresentation V.X q) :
    D.trace q
        (H.cycleClass q
          (realizeFiniteCodimensionPresentation V.X q φ)) =
      φ.sum (fun x a => a * D.pointDegree q x) := by
  rw [linearMap_realizeFiniteCodimensionPresentation]
  classical
  simp only [map_finsuppSum, LinearMap.map_smul, smul_eq_mul]
  apply Finsupp.sum_congr
  intro x a
  rw [D.trace_point_cycleClass]

#print axioms trace_realize_presentation
/-! ## Effective native cycles — exact positive Betti detection

The existing projective degree semantics evaluates the class of EVERY finite
native presentation as the weighted sum of projective point degrees.  In
particular, a nonzero effective presentation has strictly positive trace.
This is stronger than the positivity of one principal-cut successor and
never asks for a target Hodge basis cycle, projective matrix unit, ghost
closure, or assumed sheet saturation.
-/

/-- **EFFECTIVE CYCLE TRACE POSITIVITY.**
Every nonzero finite positive combination of genuine codimension-q point
cycles has strictly positive projective Betti trace.  The proof uses the
existing exact native point-presentation constructor, not abstract GST
coordinates. -/
theorem trace_positive_of_effective_presentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (φ : FiniteCodimensionPresentation V.X q)
    (hcoeff : ∀ x : CodimensionPoint V.X q, 0 ≤ φ x)
    (hnz : φ ≠ 0) :
    0 < D.trace q
      (H.cycleClass q
        (realizeFiniteCodimensionPresentation V.X q φ)) := by
  classical
  rw [D.trace_realize_presentation]
  have hex : ∃ x : CodimensionPoint V.X q, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hnz
    ext x
    exact h x
  rcases hex with ⟨x, hx⟩
  have hxm : x ∈ φ.support := Finsupp.mem_support_iff.mpr hx
  have hxp : 0 < φ x := lt_of_le_of_ne (hcoeff x) hx.symm
  change 0 < ∑ y ∈ φ.support, φ y * D.pointDegree q y
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (hcoeff y) (le_of_lt (D.pointDegree_pos q y))
  · exact ⟨x, hxm, mul_pos hxp (D.pointDegree_pos q x)⟩

#print axioms trace_positive_of_effective_presentation
/-- **NO EFFECTIVE NATIVE CYCLE CAN BE BETTI-INVISIBLE.**
Nonzero effective codimension-q native cycles cannot be killed by the
actual cycle-class map when its projective degree semantics is realized.
This excludes positive-cone cancellations without imposing a false
native-mass factorization through cohomology. -/
theorem cycleClass_ne_zero_of_effective_presentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (φ : FiniteCodimensionPresentation V.X q)
    (hcoeff : ∀ x : CodimensionPoint V.X q, 0 ≤ φ x)
    (hnz : φ ≠ 0) :
    H.cycleClass q
      (realizeFiniteCodimensionPresentation V.X q φ) ≠ 0 := by
  intro hzero
  have hpos := D.trace_positive_of_effective_presentation q φ hcoeff hnz
  rw [hzero, map_zero] at hpos
  exact lt_irrefl 0 hpos

#print axioms cycleClass_ne_zero_of_effective_presentation
/-- The restriction of genuine cycle class to the positive cone has
trivial zero fiber.  This is NOT an injectivity claim on arbitrary signed
cycles: rational equivalences can cancel positive and negative classes. -/
theorem effective_presentation_eq_zero_of_cycleClass_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (φ : FiniteCodimensionPresentation V.X q)
    (hcoeff : ∀ x : CodimensionPoint V.X q, 0 ≤ φ x)
    (hzero : H.cycleClass q
      (realizeFiniteCodimensionPresentation V.X q φ) = 0) :
    φ = 0 := by
  by_contra hnz
  exact (D.cycleClass_ne_zero_of_effective_presentation
    q φ hcoeff hnz) hzero

#print axioms effective_presentation_eq_zero_of_cycleClass_zero
/-- Trace contribution of one relative successor candidate: exact survivors
contribute their strictly positive projective degree, while wrong ambient
strata contribute zero. -/
theorem trace_successorAtomPresentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    D.trace (p + 1)
      (H.cycleClass (p + 1)
        (realizeFiniteCodimensionPresentation V.X (p + 1)
          (successorAtomPresentation V p x y))) =
      if hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 then
        D.pointDegree (p + 1)
          (⟨ambientSuccessorPoint V x.1 y, hy⟩ : CodimensionPoint V.X (p + 1))
      else 0 := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [D.trace_point_cycleClass, hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

#print axioms trace_successorAtomPresentation
/-- Exact formula for the Betti trace of the whole geometry-built successor of
one source point atom. -/
theorem trace_successorNativeOperator_point
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    D.trace (p + 1)
      (H.cycleClass (p + 1)
        (successorNativeOperator V p
          (codimensionPointCycle V.X p x))) =
      ∑ y ∈ relativeCodimensionOneFinset V x.1,
        if hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 then
          D.pointDegree (p + 1)
            (⟨ambientSuccessorPoint V x.1 y, hy⟩ :
              CodimensionPoint V.X (p + 1))
        else 0 := by
  rw [successorNativeOperator_point]
  rw [trace_realize_presentation D]
  classical
  unfold successorPresentation
  rw [← Finsupp.sum_finsetSum_index (fun a => zero_mul (D.pointDegree (p + 1) a))
    (fun a b₁ b₂ => add_mul b₁ b₂ (D.pointDegree (p + 1) a))]
  apply Finset.sum_congr rfl
  intro y hyMem
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

#print axioms trace_successorNativeOperator_point
/-- One exact relative successor forces strictly positive projective Betti
trace for the complete successor cycle because every surviving contribution is
positive and no negative coefficient occurs. -/
theorem trace_successor_positive_of_one_exact
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y0 : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy0Mem : y0 ∈ relativeCodimensionOneFinset V x.1)
    (hy0Exact : Order.coheight (ambientSuccessorPoint V x.1 y0) = p + 1) :
    0 < D.trace (p + 1)
      (H.cycleClass (p + 1)
        (successorNativeOperator V p
          (codimensionPointCycle V.X p x))) := by
  rw [trace_successorNativeOperator_point D]
  classical
  apply Finset.sum_pos'
  · intro y hy
    by_cases hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
    · rw [dif_pos hExact]
      exact le_of_lt (D.pointDegree_pos (p + 1)
        (⟨ambientSuccessorPoint V x.1 y, hExact⟩ : CodimensionPoint V.X (p + 1)))
    · rw [dif_neg hExact]
  · refine ⟨y0, hy0Mem, ?_⟩
    rw [dif_pos hy0Exact]
    exact D.pointDegree_pos (p + 1)
      (⟨ambientSuccessorPoint V x.1 y0, hy0Exact⟩ : CodimensionPoint V.X (p + 1))

#print axioms trace_successor_positive_of_one_exact
/-- **PROJECTIVE DEGREE EXCLUDES SEPARATOR HOMOLOGY ESCAPE.**
The canonical separator successor cannot have zero genuine Betti cycle class
once its single relative height-one successor is known to have the exact
ambient codimension. -/
theorem separator_successor_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    H.cycleClass (p + 1)
      (successorNativeOperator V p
        (codimensionPointCycle V.X p x)) ≠ 0 := by
  intro hzero
  have hpos := trace_successor_positive_of_one_exact D p x
    (relativeHeightOneSeparatorSuccessor V x.1 hlive)
    (relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive)
    hExact
  rw [hzero, map_zero] at hpos
  exact lt_irrefl 0 hpos

#print axioms separator_successor_cycleClass_ne_zero
/-- Projective degree upgrades the separator successor directly to the
nonzero algebraic Hodge seed consumed by the synchronized limitless orbit
machine. -/
def separator_successor_nativeHodgeSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) := by
  let Z : codimensionCycles V.X (p + 1) :=
    successorNativeOperator V p (codimensionPointCycle V.X p x)
  let alpha : ClassicalHodgeFiber V H (p + 1) :=
    ⟨H.cycleClass (p + 1) Z, G.algebraic_is_hodge (p + 1) Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  have hval : H.cycleClass (p + 1) Z = 0 := congrArg Subtype.val hz
  exact separator_successor_cycleClass_ne_zero D p x hlive hExact
    (by simpa [Z] using hval)

#print axioms separator_successor_nativeHodgeSeed
/-- Once the two geometry-first GST primitives are available from that source
sheet, the projective-degree-certified successor closes the entire Hodge
weight p+1. -/
theorem hodge_weight_of_separator_successor
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (R : ∀ j : ClassicalHodgeBasisIndex V H (p + 1),
      GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
        (V := V) (H := H)
        (separator_successor_nativeHodgeSeed G D p x hlive hExact).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≤
      LinearMap.range (H.cycleClass (p + 1)) := by
  exact (separator_successor_nativeHodgeSeed G D p x hlive hExact).hodge_weight R

#print axioms hodge_weight_of_separator_successor
/-! ## Ground-floor projective geometric realization

The repository's native coheight transport theorem ALREADY establishes the
exact relative-to-ambient codimension law at p=0 when the projective carrier
is irreducible.  Integrate that theorem directly into degree detection:
no `RelativeSuccessorAmbientExact` or bare `hExact` input survives.

This removes one entire geometric-premise edge from the actual successor
to Hodge-seed construction.  The independent degree-trace and geometric
spine semantics remain visibly stated; neither is manufactured by a
nongeometric GST matrix-unit declaration.
-/

/-- **UNCONDITIONAL GROUND CODIMENSION GEOMETRY + POSITIVE DEGREE.**
The canonical projectively live separator successor of a generic ground
point has strictly positive trace, with exact ambient codimension
constructed by the existing ground-floor theorem. -/
theorem trace_successor_positive_of_ground
    [IrreducibleSpace V.X]
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    0 < D.trace 1
      (H.cycleClass 1
        (successorNativeOperator V 0
          (codimensionPointCycle V.X 0 x))) := by
  let y := relativeHeightOneSeparatorSuccessor V x.1 hlive
  have hmem : y ∈ relativeCodimensionOneFinset V x.1 :=
    relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive
  have hexact :
      Order.coheight (ambientSuccessorPoint V x.1 y) = 0 + 1 :=
    (GSTClassicalHodgeSuccessorGroundFloor.relativeSuccessorAmbientExact_of_coheight_zero
      (V := V) x) y hmem
  exact D.trace_successor_positive_of_one_exact 0 x y hmem hexact

#print axioms trace_successor_positive_of_ground
/-- **GROUND-FLOOR NONVANISHING OF GENUINE BETTI CLASS.**
For the canonical principal-cut native cycle at weight one, the former
separate ambient-exactness hypothesis is now discharged internally. -/
theorem separator_successor_cycleClass_ne_zero_of_ground
    [IrreducibleSpace V.X]
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    H.cycleClass 1
      (successorNativeOperator V 0
        (codimensionPointCycle V.X 0 x)) ≠ 0 := by
  intro hzero
  have hpos := D.trace_successor_positive_of_ground x hlive
  rw [hzero, map_zero] at hpos
  exact lt_irrefl 0 hpos

#print axioms separator_successor_cycleClass_ne_zero_of_ground
/-- **GROUNDED WEIGHT-ONE HODGE SEED.**
One actual projective ground-point cut yields an actual algebraic Hodge
seed at weight one, with no independently supplied exact-stratum
predicate, no guessed target representative and no Hodge-completeness
premise.  The native cycle is the repo's pre-existing principal-cut cycle. -/
noncomputable def separator_successor_nativeHodgeSeed_of_ground
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := 1) := by
  let Z : codimensionCycles V.X 1 :=
    successorNativeOperator V 0 (codimensionPointCycle V.X 0 x)
  let alpha : ClassicalHodgeFiber V H 1 :=
    ⟨H.cycleClass 1 Z, G.algebraic_is_hodge 1 Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hzero
  have hval : H.cycleClass 1 Z = 0 := congrArg Subtype.val hzero
  exact D.separator_successor_cycleClass_ne_zero_of_ground x hlive
    (by simpa [Z] using hval)

#check ProjectiveDegreeTraceSemantics.trace_positive_of_effective_presentation
#check ProjectiveDegreeTraceSemantics.cycleClass_ne_zero_of_effective_presentation
#check ProjectiveDegreeTraceSemantics.effective_presentation_eq_zero_of_cycleClass_zero
#check ProjectiveDegreeTraceSemantics.trace_successor_positive_of_ground
#check ProjectiveDegreeTraceSemantics.separator_successor_cycleClass_ne_zero_of_ground
#check ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed_of_ground

#print axioms ProjectiveDegreeTraceSemantics.trace_positive_of_effective_presentation
#print axioms ProjectiveDegreeTraceSemantics.effective_presentation_eq_zero_of_cycleClass_zero
#print axioms ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed_of_ground

#check ProjectiveDegreeTraceSemantics
#check ProjectiveDegreeTraceSemantics.trace_realize_presentation
#check ProjectiveDegreeTraceSemantics.trace_successorNativeOperator_point
#check ProjectiveDegreeTraceSemantics.trace_successor_positive_of_one_exact
#check ProjectiveDegreeTraceSemantics.separator_successor_cycleClass_ne_zero
#check ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed
#check ProjectiveDegreeTraceSemantics.hodge_weight_of_separator_successor

#print axioms ProjectiveDegreeTraceSemantics.trace_realize_presentation
#print axioms ProjectiveDegreeTraceSemantics.trace_successor_positive_of_one_exact
#print axioms ProjectiveDegreeTraceSemantics.separator_successor_cycleClass_ne_zero
#print axioms ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed

end ProjectiveDegreeTraceSemantics
end GSTClassicalHodgeProjectiveDegreeTrace
