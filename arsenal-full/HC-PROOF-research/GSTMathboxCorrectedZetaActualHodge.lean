import GSTMathboxCorrectedZetaInfinite
import GSTClassicalHodgeActualGeometricIrreducibility

/-!
# Mathbox: corrected zeta Equation (3) → actual Hodge target

This combines two earlier independently verified mathematical routes:

(A) The original corrected integer-indexed zeta reciprocal series is
ACTUALLY summable for x=y=2, with infinite sum -1 (not only finite).
A nonzero zeta-at-s value thus gives a nonzero real detector.

(B) The actual rational algebraic Hodge subspace is invariant under
genuinely realized Hodge-compatible closed correspondences. If those
operators are irreducible and a single ACTUAL native codimension-p
cycle has a nonzero cohomology class, then ALL rational Hodge classes
in that fiber have genuine rational algebraic-cycle representatives.

The theorem below uses the corrected infinite scalar equality to
replace the separate nonzero algebraic source hypothesis. It never
assumes an algebraic preimage of the desired target alpha.

The HARD universal inputs remain explicit:
- a geometric native cycle Z with true cohomology readout linked to
  the analytic zeta expression;
- irreducibility of the ACTUAL finite-closed correspondence operators.
Neither follows from numerical summation, so the all-varieties Hodge
conjecture is not declared proved.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeActualGeometricIrreducibility
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaInfinite

namespace GSTMathboxCorrectedZetaActualHodge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A *nonzero actual native algebraic class* suffices under genuine
correspondence irreducibility. This removes the earlier restriction
that the seed must be the special projective-spine tower. -/
theorem hodge_from_any_nonzero_native_seed_and_actual_irreducibility
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (hnz : geometricHodgeClass G Z ≠ 0)
    (hirred : ActualHodgeCorrespondenceIrreducible
      (V := V) (H := H) (p := p))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ C : codimensionCycles V.X p, H.cycleClass p C = alpha := by
  have hmem : geometricHodgeClass G Z ∈
      AlgebraicHodgeSubspace V H p := by
    change (geometricHodgeClass G Z).1 ∈
      pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨Z, rfl⟩
  have hnonzero : AlgebraicHodgeSubspace V H p ≠ ⊥ := by
    intro heq
    have hbot : geometricHodgeClass G Z ∈
        (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
      rw [← heq]
      exact hmem
    apply hnz
    simpa using hbot
  have hstable :
      InvariantUnderActualHodgeCorrespondences
        (AlgebraicHodgeSubspace V H p) :=
    algebraicHodgeSubspace_actual_correspondence_invariant
  have htop : AlgebraicHodgeSubspace V H p = ⊤ := by
    rcases hirred (AlgebraicHodgeSubspace V H p) hstable with hz | ht
    · exact False.elim (hnonzero hz)
    · exact ht
  have htarget :
      (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p) ∈
        AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at htarget
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at htarget
  exact htarget

/-- Exact corrected zeta source certificate: equality of the
geometrically measured RATIONAL coordinate with a convergent,
real zeta-weighted scalar. Nonzero follows from a kernel theorem,
NOT from inserting another nonvanishing hypothesis on the cycle. -/
theorem corrected_zeta_infinite_forces_nonzero_native_class
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (zetaAtS : ℝ) (hZeta : zetaAtS ≠ 0)
    (hMeasure :
      ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
        zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m)) :
    geometricHodgeClass G Z ≠ 0 := by
  have hscalar :
      zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m) ≠ 0 :=
    (corrected_infinite_zeta_amplitude zetaAtS hZeta).2
  intro hz
  apply hscalar
  have hzero : read (geometricHodgeClass G Z) = 0 := by
    rw [hz]
    exact map_zero read
  rw [hzero] at hMeasure
  simpa using hMeasure.symm

/-- Exact arbitrary-rank implication of the user's corrected INFINITE
equation under a genuine geometric readout law and ACTUAL geometric
correspondence irreducibility. All target cycles are derived, not
provided as target-class preimages. -/
theorem corrected_zeta_actual_irreducibility_hodge
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (zetaAtS : ℝ) (hZeta : zetaAtS ≠ 0)
    (hMeasure :
      ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
        zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m))
    (hirred : ActualHodgeCorrespondenceIrreducible
      (V := V) (H := H) (p := p))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ C : codimensionCycles V.X p, H.cycleClass p C = alpha := by
  apply hodge_from_any_nonzero_native_seed_and_actual_irreducibility
    G Z (corrected_zeta_infinite_forces_nonzero_native_class
      G Z read zetaAtS hZeta hMeasure) hirred alpha halpha

/-- Full Stage-2G rational Hodge target from a weight-local ACTUAL zeta
seed certificate and irreducible geometric correspondences at each
active nonzero Hodge fiber. Zero fibers need no seeds. These are
still explicit universal *geometric existence* premises. -/
theorem full_hodge_of_corrected_zeta_actual_geometry
    (G : GeometricCycleClassSpine V H)
    (hirred : ∀ q : Nat,
      ActualHodgeCorrespondenceIrreducible
        (V := V) (H := H) (p := q))
    (hZetaGeometry : ∀ q : Nat,
      (∃ a : ClassicalHodgeFiber V H q, a ≠ 0) →
      ∃ (Z : codimensionCycles V.X q)
        (read : ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ)
        (zetaAtS : ℝ),
        zetaAtS ≠ 0 ∧
        ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
          zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  by_cases hactive : ∃ a : ClassicalHodgeFiber V H q, a ≠ 0
  · obtain ⟨Z, read, zetaAtS, hZeta, hMeasure⟩ :=
      hZetaGeometry q hactive
    exact corrected_zeta_actual_irreducibility_hodge G Z read
      zetaAtS hZeta hMeasure (hirred q) alpha halpha
  · have ha0 : alpha = 0 := by
      by_contra hne
      apply hactive
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro hz
      apply hne
      simpa using congrArg Subtype.val hz
    exact ⟨0, by simp [ha0]⟩

#check hodge_from_any_nonzero_native_seed_and_actual_irreducibility
#check corrected_zeta_infinite_forces_nonzero_native_class
#check corrected_zeta_actual_irreducibility_hodge
#check full_hodge_of_corrected_zeta_actual_geometry

#print axioms corrected_zeta_actual_irreducibility_hodge
#print axioms full_hodge_of_corrected_zeta_actual_geometry

end GSTMathboxCorrectedZetaActualHodge
