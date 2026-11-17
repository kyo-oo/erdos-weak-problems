import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeFiniteSupportArsenalConjugation

/-!
# GST CLASSICAL HODGE — ARSENAL ORBIT SATURATION

The rank-free Hodge fiber is not merely irreducible under the complete GST
matrix-unit arsenal: every nonzero vector is cyclic.

For a nonzero genuine rational `(p,p)` class `alpha`, choose one nonzero basis
coordinate `i`.  Applying the matrix unit `E_{i,j}` to `alpha` produces the
nonzero scalar `alpha_i` times the arbitrary target basis vector `e_j`.
Over `Q` that scalar is invertible, hence every basis vector belongs to the
linear span of the single GST arsenal orbit of `alpha`.  Basis reconstruction
then gives the whole Hodge fiber.

This is the rank-free limitless version of the finite-window projector /
Lefschetz / Poincare generation theorem.  The finite-support conjugation file
identifies every finite restriction of these matrix units with the actual GST
full arsenal.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeFiniteSupportArsenalConjugation

namespace GSTClassicalHodgeArsenalOrbitSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The set of all one-step matrix-unit images of one Hodge class. -/
def arsenalOrbit
    (alpha : ClassicalHodgeFiber V H p) :
    Set (ClassicalHodgeFiber V H p) :=
  Set.range (fun ij :
      ClassicalHodgeBasisIndex V H p × ClassicalHodgeBasisIndex V H p =>
    hodgeMatrixUnit ij.1 ij.2 alpha)

/-- Rational linear span of the complete GST matrix-unit orbit. -/
noncomputable def arsenalOrbitSpan
    (alpha : ClassicalHodgeFiber V H p) :
    Submodule ℚ (ClassicalHodgeFiber V H p) :=
  Submodule.span ℚ (arsenalOrbit alpha)

/-- Every matrix-unit image belongs to the orbit span by definition. -/
theorem matrixUnit_mem_arsenalOrbitSpan
    (alpha : ClassicalHodgeFiber V H p)
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j alpha ∈ arsenalOrbitSpan alpha := by
  apply Submodule.subset_span
  exact ⟨(i,j), rfl⟩

/-- If one source coordinate of `alpha` is nonzero, every genuine Hodge basis
vector lies in the span of the single orbit of `alpha`. -/
theorem basis_mem_arsenalOrbitSpan_of_coordinate
    (alpha : ClassicalHodgeFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i alpha ≠ 0) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      classicalHodgeBasis V H p j ∈ arsenalOrbitSpan alpha := by
  intro j
  have horbit := matrixUnit_mem_arsenalOrbitSpan alpha i j
  have hscaled :
      hodgeCoordinate i alpha • classicalHodgeBasis V H p j ∈
        arsenalOrbitSpan alpha := by
    simpa [hodgeMatrixUnit_apply] using horbit
  have hinv := (arsenalOrbitSpan alpha).smul_mem
    ((hodgeCoordinate i alpha)⁻¹) hscaled
  simpa [hi] using hinv

/-- **LIMITLESS CYCLICITY.** Every nonzero genuine rational Hodge class is a
cyclic vector for the complete GST matrix-unit arsenal. -/
theorem arsenalOrbitSpan_eq_top
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    arsenalOrbitSpan alpha = ⊤ := by
  obtain ⟨i, hi⟩ := exists_nonzero_hodgeCoordinate halpha
  apply top_unique
  intro beta _
  have hbasis := basis_mem_arsenalOrbitSpan_of_coordinate alpha i hi
  rw [← (classicalHodgeBasis V H p).linearCombination_repr beta,
    Finsupp.linearCombination_apply, Finsupp.sum]
  exact (arsenalOrbitSpan alpha).sum_mem fun j hj =>
    (arsenalOrbitSpan alpha).smul_mem
      (((classicalHodgeBasis V H p).repr beta) j)
      (hbasis j)

/-- Every target Hodge class is a finite rational linear combination of
matrix-unit images of any fixed nonzero source class. -/
theorem exists_finite_arsenal_expansion
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (beta : ClassicalHodgeFiber V H p) :
    beta ∈ arsenalOrbitSpan alpha := by
  rw [arsenalOrbitSpan_eq_top alpha halpha]
  trivial

/-- The orbit-cyclicity theorem and the finite-support GST conjugation theorem
hold simultaneously for every nonzero Hodge state. -/
theorem limitless_full_arsenal_crown
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    arsenalOrbitSpan alpha = ⊤ ∧
      (∀ r s : Fin (liveRank alpha),
        conjugatedMatrixUnit alpha r s (liveBasisVector alpha r) =
          liveBasisVector alpha s
        ∧ ∀ t : Fin (liveRank alpha), t ≠ r →
          conjugatedMatrixUnit alpha r s (liveBasisVector alpha t) = 0) := by
  exact ⟨arsenalOrbitSpan_eq_top alpha halpha,
    live_support_full_arsenal_receipt alpha⟩

#check arsenalOrbit
#check arsenalOrbitSpan
#check matrixUnit_mem_arsenalOrbitSpan
#check basis_mem_arsenalOrbitSpan_of_coordinate
#check arsenalOrbitSpan_eq_top
#check exists_finite_arsenal_expansion
#check limitless_full_arsenal_crown

#print axioms basis_mem_arsenalOrbitSpan_of_coordinate
#print axioms arsenalOrbitSpan_eq_top
#print axioms exists_finite_arsenal_expansion
#print axioms limitless_full_arsenal_crown

end GSTClassicalHodgeArsenalOrbitSaturation
