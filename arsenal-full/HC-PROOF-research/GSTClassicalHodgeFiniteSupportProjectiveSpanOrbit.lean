import GSTClassicalHodgeProjectiveSpanWordSaturation
import GSTClassicalHodgeFiniteSupportProjectiveOrbit
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — FINITE-SUPPORT PROJECTIVE-SPAN ORBIT

The per-class brute-force route can be made more geometric still.

A concrete Hodge class has finite basis support.  The previous finite-support
crown asked for one explicit projective operator word on each support sheet.
The projective-span compiler proves that even this is unnecessary syntax: it is
enough to give, on each live support sheet, one native operator lying in the
rational span of genuine projective self-transports together with its exact
cycle-class value on the single synchronized source cycle.

Thus one nonzero Hodge class is attacked using only finite native geometric
data:

  finite relevant spine prefix
    + finitely many genuine projective-span native source equations
      -> finitely many compiled projective words
      -> finitely many exact target basis cycles
      -> exact reconstruction of the requested Hodge class.

No whole-weight basis family, no ambient projective cohomology operator, no
all-Hodge matrix-unit law, and no projective-word syntax is supplied.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteSupportProjectiveSpanOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiniteSpineMomentOrbit
open GSTClassicalHodgeProjectiveSpanWordSaturation
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reconstruct one Hodge class from native projective-span target data only on
its finite live support. -/
noncomputable def finiteSupportProjectiveSpanCycle
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveSpanLiveSourceTarget S i.1) :
    codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    ((classicalHodgeBasis V H p).repr alpha i.1) •
      ((R i).toWordLiveSourceTarget G).targetCycle

/-- **FINITE NATIVE-SPAN RECONSTRUCTION.**
The cycle assembled from only the finitely many live projective-span targets
has genuine cycle class exactly equal to the requested Hodge class. -/
theorem finiteSupportProjectiveSpanCycle_spec
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveSpanLiveSourceTarget S i.1) :
    H.cycleClass p (finiteSupportProjectiveSpanCycle G S alpha R) = alpha.1 := by
  unfold finiteSupportProjectiveSpanCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul,
    ProjectiveWordLiveSourceTarget.targetCycle_spec]
  exact (hodgeClass_eq_support_sum alpha).symm

/-- One concrete Hodge class has an actual native cycle once its finite support
is reachable by native projective-span operators from one live source. -/
theorem hodgeClass_has_cycle_of_finite_projectiveSpan_support
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveSpanLiveSourceTarget S i.1) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨finiteSupportProjectiveSpanCycle G S alpha R,
    finiteSupportProjectiveSpanCycle_spec G S alpha R⟩

/-- **PER-CLASS FINITE NATIVE-GEOMETRY HODGE CROWN.**
For every nonzero Hodge class, only a finite spine detector ending at that
weight and finitely many native projective-span source equations on that
class's support are required. -/
theorem bigradedBettiHodge_of_per_class_finite_projectiveSpan_orbits
    (G : GeometricCycleClassSpine V H)
    (D : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → FiniteSpineMomentChain G q)
    (R : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ halpha : alpha ≠ 0,
      ∀ i : HodgeSupportIndex alpha,
        ProjectiveSpanLiveSourceTarget
          (D q alpha halpha).topOrbitSeed i.1) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact hodgeClass_has_cycle_of_finite_projectiveSpan_support
      G (D q alpha halpha).topOrbitSeed alpha (R q alpha halpha)

/-- Elementwise form of the finite native-span crown. -/
theorem every_hodge_class_has_native_cycle_of_per_class_projectiveSpan
    (G : GeometricCycleClassSpine V H)
    (D : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → FiniteSpineMomentChain G q)
    (R : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ halpha : alpha ≠ 0,
      ∀ i : HodgeSupportIndex alpha,
        ProjectiveSpanLiveSourceTarget
          (D q alpha halpha).topOrbitSeed i.1)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  by_cases halpha : alpha = 0
  · refine ⟨0, ?_⟩
    rw [halpha]
    simp
  · exact hodgeClass_has_cycle_of_finite_projectiveSpan_support
      G (D q alpha halpha).topOrbitSeed alpha (R q alpha halpha)

#check finiteSupportProjectiveSpanCycle
#check finiteSupportProjectiveSpanCycle_spec
#check hodgeClass_has_cycle_of_finite_projectiveSpan_support
#check bigradedBettiHodge_of_per_class_finite_projectiveSpan_orbits
#check every_hodge_class_has_native_cycle_of_per_class_projectiveSpan

#print axioms finiteSupportProjectiveSpanCycle_spec
#print axioms hodgeClass_has_cycle_of_finite_projectiveSpan_support
#print axioms bigradedBettiHodge_of_per_class_finite_projectiveSpan_orbits
#print axioms every_hodge_class_has_native_cycle_of_per_class_projectiveSpan

end GSTClassicalHodgeFiniteSupportProjectiveSpanOrbit
