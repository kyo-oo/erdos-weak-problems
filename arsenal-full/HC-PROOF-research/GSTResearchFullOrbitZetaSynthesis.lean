import GSTResearchGeometricOrbitSynthesis
import GSTMathboxCorrectedZetaActualHodge

/-!
# Research GST: corrected zeta-certified finite correspondence-orbit Hodge synthesis

The user's third original GST formula was corrected to use
1/(x^n-y^(n+1)); the infinite sum is kernel-proved for x=y=2.
The user's geometric-coordinate and operator-separation laws motivate
using actual geometric readouts and actual finite-closed correspondence
words instead of abstract freely chosen Hodge matrix units.

Mathematical construction here:
  1. A genuine native rational algebraic cycle Z has a rational Hodge
     coordinate whose real realization is EQUAL to the corrected
     infinite zeta scalar. This is an explicit geometric measurement
     equation to be proved for the source variety.
  2. The corrected infinite-series theorem makes this scalar nonzero
     whenever its real coefficient is nonzero.
  3. NativeGeometricOrbitWord inductively manufactures every finite
     native cycle from Z using actual Hodge-compatible finite-closed
     realized correspondences; naturality is proved for all words.
  4. If the geometric correspondence action is actually irreducible,
     those constructed native cycle classes span the full Hodge fiber.
  5. Handle zero fibers separately and conclude the actual rational
     Hodge target at all weights without a prescribed full-rank
     cycle matrix, per-target cycle preimage, sorry, or custom axiom.

A uniform geometric measurement and actual geometric irreducibility
remain explicit hypotheses, not universal theorems. This is a new,
verifiable geometric CONSTRUCTION plus a conditional universal Hodge
route, not the completed unconditional Hodge conjecture.
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
open GSTClassicalHodgeActualGeometricIrreducibility
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaInfinite
open GSTMathboxCorrectedZetaActualHodge
open GSTResearchGeometricOrbitSynthesis

namespace GSTResearchFullOrbitZetaSynthesis

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The author's corrected **infinite** zeta expression supplies a
nonzero native cycle class. Its full geometric correspondence orbit,
constructed using finite words rather than an assumed basis, then
generates every Hodge class under actual geometric irreducibility. -/
theorem every_hodge_class_from_corrected_zeta_constructed_orbit
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X p)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (zetaAtS : ℝ)
    (hZeta : zetaAtS ≠ 0)
    (hActualMeasurement :
      ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
        zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m))
    (hirred : ActualHodgeCorrespondenceIrreducible
      (V := V) (H := H) (p := p))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ C : codimensionCycles V.X p, H.cycleClass p C = alpha := by
  have hseed : geometricHodgeClass G Z ≠ 0 :=
    corrected_zeta_infinite_forces_nonzero_native_class
      G Z read zetaAtS hZeta hActualMeasurement
  exact every_hodge_class_of_constructed_actual_orbit
    G Z hseed hirred alpha halpha

/-- All-weight result with **explicit native orbit synthesis**.
Nonzero Hodge fibers require a certified actual algebraic source
measured by the corrected zeta series and actual correspondence
irreducibility. Vacuous zero fibers need no source. No Hodge-basis
cycle witnesses or full-rank determinant are assumed. -/
theorem full_hodge_of_Research_corrected_zeta_native_orbit
    (G : GeometricCycleClassSpine V H)
    (hirred : ∀ q : Nat,
      ActualHodgeCorrespondenceIrreducible
        (V := V) (H := H) (p := q))
    (hActualZetaSources : ∀ q : Nat,
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
      hActualZetaSources q hactive
    exact every_hodge_class_from_corrected_zeta_constructed_orbit
      G Z read zetaAtS hZeta hMeasure (hirred q) alpha halpha
  · have ha0 : alpha = 0 := by
      by_contra hne
      apply hactive
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro hz
      apply hne
      simpa using congrArg Subtype.val hz
    exact ⟨0, by simp [ha0]⟩

#check every_hodge_class_from_corrected_zeta_constructed_orbit
#check full_hodge_of_Research_corrected_zeta_native_orbit

#print axioms every_hodge_class_from_corrected_zeta_constructed_orbit
#print axioms full_hodge_of_Research_corrected_zeta_native_orbit

end GSTResearchFullOrbitZetaSynthesis
