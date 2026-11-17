import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeLocalCyclicCriterion

/-!
# GST CLASSICAL HODGE — FINITE-SUPPORT PROJECTIVE ORBIT

The unrestricted Hodge basis may have arbitrary cardinality, but every concrete
Hodge class has finite basis support.  Therefore even the one-source
projective-word crown still asks for more geometry than an individual class
needs when it quantifies over every basis direction in a weight.

This module removes that excess.

For one nonzero rational `(p,p)` class `alpha`:

1. a finite spine-moment chain produces one nonzero algebraic source state at
   weight `p`;
2. for each basis direction in the finite support of `alpha`, one finite
   projective operator word transports that source to the requested basis
   direction;
3. the resulting native target cycles are reassembled with the actual support
   coefficients of `alpha`.

Thus the geometric externalization obligation is finite **per requested Hodge
class**, even when the genuine Hodge basis itself is infinite.  Zero classes
need no moment chain and no projective word at all.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteSupportProjectiveOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeFiniteSpineMomentOrbit
open GSTClassicalHodgeProjectiveWordOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reassemble one concrete Hodge class from native target cycles only on its
finite live basis support. -/
noncomputable def finiteSupportTargetCycle
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveWordLiveSourceTarget G S i.1) :
    codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    ((classicalHodgeBasis V H p).repr alpha i.1) •
      (R i).targetCycle

/-- **FINITE-SUPPORT PROJECTIVE RECONSTRUCTION.**
The reassembled native cycle has cycle class exactly equal to the requested
Hodge class. -/
theorem finiteSupportTargetCycle_spec
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveWordLiveSourceTarget G S i.1) :
    H.cycleClass p (finiteSupportTargetCycle G S alpha R) = alpha.1 := by
  unfold finiteSupportTargetCycle
  rw [map_sum]
  simp_rw [LinearMap.map_smul,
    ProjectiveWordLiveSourceTarget.targetCycle_spec]
  exact (hodgeClass_eq_support_sum alpha).symm

/-- One concrete nonzero Hodge class needs projective words only on its own
finite support. -/
theorem hodgeClass_has_cycle_of_finite_projective_support
    (G : GeometricCycleClassSpine V H)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (alpha : ClassicalHodgeFiber V H p)
    (R : ∀ i : HodgeSupportIndex alpha,
      ProjectiveWordLiveSourceTarget G S i.1) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  ⟨finiteSupportTargetCycle G S alpha R,
    finiteSupportTargetCycle_spec G S alpha R⟩

/-- **PER-CLASS FINITE BRUTE-FORCE HODGE CROWN.**

For every nonzero Hodge class, the only cross-weight input is a finite moment
chain ending at that class's weight, and the only within-weight geometric
inputs are projective words indexed by that class's finite live support.
No global basis-index family is requested. -/
theorem bigradedBettiHodge_of_per_class_finite_projective_orbits
    (G : GeometricCycleClassSpine V H)
    (D : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → FiniteSpineMomentChain G q)
    (R : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ halpha : alpha ≠ 0,
      ∀ i : HodgeSupportIndex alpha,
        ProjectiveWordLiveSourceTarget G
          (D q alpha halpha).topOrbitSeed i.1) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact hodgeClass_has_cycle_of_finite_projective_support
      G (D q alpha halpha).topOrbitSeed alpha (R q alpha halpha)

/-- Explicit elementwise form of the per-class finite orbit crown. -/
theorem every_hodge_class_has_native_cycle_of_per_class_finite_orbits
    (G : GeometricCycleClassSpine V H)
    (D : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → FiniteSpineMomentChain G q)
    (R : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ halpha : alpha ≠ 0,
      ∀ i : HodgeSupportIndex alpha,
        ProjectiveWordLiveSourceTarget G
          (D q alpha halpha).topOrbitSeed i.1)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  by_cases halpha : alpha = 0
  · refine ⟨0, ?_⟩
    rw [halpha]
    simp
  · exact hodgeClass_has_cycle_of_finite_projective_support
      G (D q alpha halpha).topOrbitSeed alpha (R q alpha halpha)

#check finiteSupportTargetCycle
#check finiteSupportTargetCycle_spec
#check hodgeClass_has_cycle_of_finite_projective_support
#check bigradedBettiHodge_of_per_class_finite_projective_orbits
#check every_hodge_class_has_native_cycle_of_per_class_finite_orbits

#print axioms finiteSupportTargetCycle_spec
#print axioms hodgeClass_has_cycle_of_finite_projective_support
#print axioms bigradedBettiHodge_of_per_class_finite_projective_orbits
#print axioms every_hodge_class_has_native_cycle_of_per_class_finite_orbits

end GSTClassicalHodgeFiniteSupportProjectiveOrbit