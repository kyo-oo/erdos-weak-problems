import GSTClassicalHodgeFiniteSupportProjectiveSpanOrbit
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — SPINE-NONZERO FINITE-SUPPORT ORBIT

The finite-spine moment package is stronger than the per-class orbit proof
needs.

For a requested weight `q`, the orbit argument consumes only one consequence
of that package: the canonical geometry-built normalized spine Hodge state at
weight `q` is nonzero.  Once that single fact is available, the already-proved
exact cycle-class identity for `spineNativeTower` immediately gives a
synchronized nonzero native/Hodge source.

Therefore this layer removes `FiniteSpineMomentChain` completely from the
per-class brute-force interface.

At a weight with a nonzero Hodge class the remaining data are now exactly:

* nonvanishing of the canonical geometry-built spine state in that weight;
* for each basis direction in the finite support of the requested class, one
  native projective-correspondence-span operator whose source-cycle class is
  the correct scalar multiple of that target sheet.

The native projective-span compiler then manufactures projective words, and
the finite-support reconstruction produces an actual algebraic cycle for the
requested Hodge class.

No detector functional, no finite moment recursion, no all-weight conserved
charge, no ambient projective operator action, and no externally supplied word
syntax is used by this route.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSpineNonzeroFiniteSupportOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeProjectiveSpanWordSaturation
open GSTClassicalHodgeFiniteSupportProjectiveSpanOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Turn the exact geometry-built spine at one weight into a synchronized live
orbit seed using only nonvanishing of that one Hodge state. -/
noncomputable def spineOrbitSeedOfNonzero
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (hne : spineHodgeSeed G q ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) where
  cycle := spineNativeTower G q
  hodge := spineHodgeSeed G q
  hodge_ne_zero := hne
  class_eq := spineNativeTower_cycleClass G q

/-- The seed's native face is definitionally the canonical normalized spine
cycle. -/
@[simp]
theorem spineOrbitSeedOfNonzero_cycle
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (hne : spineHodgeSeed G q ≠ 0) :
    (spineOrbitSeedOfNonzero G q hne).cycle = spineNativeTower G q :=
  rfl

/-- The seed's Hodge face is definitionally the canonical normalized spine
state. -/
@[simp]
theorem spineOrbitSeedOfNonzero_hodge
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (hne : spineHodgeSeed G q ≠ 0) :
    (spineOrbitSeedOfNonzero G q hne).hodge = spineHodgeSeed G q :=
  rfl

/-- One concrete Hodge class is algebraic when the canonical spine at its
weight is nonzero and its finite support is reachable by native
projective-span transports. -/
theorem hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q)
    (hne : spineHodgeSeed G q ≠ 0)
    (R : ∀ i : GSTClassicalHodgeLocalCyclicCriterion.HodgeSupportIndex alpha,
      ProjectiveSpanLiveSourceTarget
        (spineOrbitSeedOfNonzero G q hne) i.1) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  exact hodgeClass_has_cycle_of_finite_projectiveSpan_support
    G (spineOrbitSeedOfNonzero G q hne) alpha R

/-- **WEIGHT-LOCAL BRUTE-FORCE HODGE CROWN.**

Only weights whose genuine `(q,q)` Hodge fiber is nonzero request a spine
nonvanishing proof.  At such a weight, projective-span transports are needed
only on the finite support of the particular Hodge class being reconstructed. -/
theorem bigradedBettiHodge_of_weight_spine_nonzero_finite_projectiveSpan
    (G : GeometricCycleClassSpine V H)
    (N : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
        spineHodgeSeed G q ≠ 0)
    (R : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ i : GSTClassicalHodgeLocalCyclicCriterion.HodgeSupportIndex alpha,
        ProjectiveSpanLiveSourceTarget
          (spineOrbitSeedOfNonzero G q (N q hq)) i.1) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · have hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ := by
      intro hbot
      have hmem : alpha.1 ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
        simpa [hbot] using alpha.2
      have hval : alpha.1 = 0 := by simpa using hmem
      apply halpha
      apply Subtype.ext
      exact hval
    exact hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
      G q alpha (N q hq) (R q hq alpha)

/-- Per-class version: even the nonvanishing assumption is requested only when
the particular Hodge class under attack is nonzero. -/
theorem bigradedBettiHodge_of_per_class_spine_nonzero_projectiveSpan
    (G : GeometricCycleClassSpine V H)
    (N : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 → spineHodgeSeed G q ≠ 0)
    (R : ∀ q : Nat,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ halpha : alpha ≠ 0,
      ∀ i : GSTClassicalHodgeLocalCyclicCriterion.HodgeSupportIndex alpha,
        ProjectiveSpanLiveSourceTarget
          (spineOrbitSeedOfNonzero G q (N q alpha halpha)) i.1) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact ⟨0, by simp⟩
  · exact hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
      G q alpha (N q alpha halpha) (R q alpha halpha)

/-- Explicit native-cycle witness under the weight-local interface. -/
theorem every_hodge_class_has_native_cycle_of_weight_spine_nonzero
    (G : GeometricCycleClassSpine V H)
    (N : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
        spineHodgeSeed G q ≠ 0)
    (R : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ alpha : ClassicalHodgeFiber V H q,
      ∀ i : GSTClassicalHodgeLocalCyclicCriterion.HodgeSupportIndex alpha,
        ProjectiveSpanLiveSourceTarget
          (spineOrbitSeedOfNonzero G q (N q hq)) i.1)
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  by_cases halpha : alpha = 0
  · refine ⟨0, ?_⟩
    rw [halpha]
    simp
  · have hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ := by
      intro hbot
      have hmem : alpha.1 ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
        simpa [hbot] using alpha.2
      have hval : alpha.1 = 0 := by simpa using hmem
      apply halpha
      apply Subtype.ext
      exact hval
    exact hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
      G q alpha (N q hq) (R q hq alpha)

#check spineOrbitSeedOfNonzero
#check spineOrbitSeedOfNonzero_cycle
#check spineOrbitSeedOfNonzero_hodge
#check hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
#check bigradedBettiHodge_of_weight_spine_nonzero_finite_projectiveSpan
#check bigradedBettiHodge_of_per_class_spine_nonzero_projectiveSpan
#check every_hodge_class_has_native_cycle_of_weight_spine_nonzero

#print axioms spineOrbitSeedOfNonzero
#print axioms hodgeClass_has_cycle_of_spine_nonzero_projectiveSpan_support
#print axioms bigradedBettiHodge_of_weight_spine_nonzero_finite_projectiveSpan
#print axioms bigradedBettiHodge_of_per_class_spine_nonzero_projectiveSpan
#print axioms every_hodge_class_has_native_cycle_of_weight_spine_nonzero

end GSTClassicalHodgeSpineNonzeroFiniteSupportOrbit
