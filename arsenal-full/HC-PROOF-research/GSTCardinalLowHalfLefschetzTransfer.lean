import GSTCardinalHilbertComponentSource
import Mathlib

/-!
# GST original-X lower-half source-birth -> higher-weight Hodge algebraicity

Rational Hard Lefschetz: for each 0 <= q <= floor(dim X/2),
cup product by the ACTUAL algebraic ample divisor h^(dim X-2q)
is a rational isomorphism W_q(X) ≃ W_(dim X-q)(X).

The lower-Hodge-to-upper-Hodge surjectivity step is formalized here,
under explicit native and Betti ample maps with CANONICAL naturality.
The geometric Hard Lefschetz theorem and Chow ring are not assumed to
be formalized by importing Mathlib; the actual original-X derivation
is in research/derivations/
GST_half_codimension_algebraic_Lefschetz_dual_single_fold_2026_11_10.md.

No target Chow preimage and no new Hodge surjectivity axiom is inserted.
The source-generation antecedent is named and remains the open
original-X geometric GST goal for the whole lower half.
-/

set_option maxHeartbeats 1500000
noncomputable section

namespace GSTCardinalLowHalfLefschetzTransfer

variable {AL AH WL WH : Type*}
variable [AddCommGroup AL] [Module ℚ AL]
variable [AddCommGroup AH] [Module ℚ AH]
variable [AddCommGroup WL] [Module ℚ WL]
variable [AddCommGroup WH] [Module ℚ WH]

/-- Once actual Chow sources represent EVERY lower-half rational Hodge
class, forward multiplication by a genuine ample Chow cycle supplies
EVERY complementary higher-weight class. No algebraic inverse
Lefschetz or analytic Hodge-star correspondence is assumed. -/
theorem upper_hodge_of_lower_native_sources
    (cycleClassLow : AL →ₗ[ℚ] WL)
    (cycleClassHigh : AH →ₗ[ℚ] WH)
    (nativeAmple : AL →ₗ[ℚ] AH)
    (bettiHardLefschetz : WL ≃ₗ[ℚ] WH)
    (hcanonical :
      ∀ z : AL,
        cycleClassHigh (nativeAmple z) =
          bettiHardLefschetz (cycleClassLow z))
    (hlow : Function.Surjective cycleClassLow) :
    Function.Surjective cycleClassHigh := by
  intro beta
  obtain ⟨alpha, halpha⟩ :=
    bettiHardLefschetz.surjective beta
  obtain ⟨z, hz⟩ := hlow alpha
  refine ⟨nativeAmple z, ?_⟩
  rw [hcanonical, hz, halpha]

/-- The precise contrapositive: a genuinely missing upper-weight
rational Hodge cycle forces a missing LOWER-HALF rational Hodge cycle.
This lowers the quantified GST source-birth target. -/
theorem missing_upper_implies_missing_lower
    (cycleClassLow : AL →ₗ[ℚ] WL)
    (cycleClassHigh : AH →ₗ[ℚ] WH)
    (nativeAmple : AL →ₗ[ℚ] AH)
    (bettiHardLefschetz : WL ≃ₗ[ℚ] WH)
    (hcanonical :
      ∀ z : AL,
        cycleClassHigh (nativeAmple z) =
          bettiHardLefschetz (cycleClassLow z))
    (hupper : ¬ Function.Surjective cycleClassHigh) :
    ¬ Function.Surjective cycleClassLow := by
  intro hlow
  exact hupper
    (upper_hodge_of_lower_native_sources
      cycleClassLow cycleClassHigh nativeAmple
      bettiHardLefschetz hcanonical hlow)

#check upper_hodge_of_lower_native_sources
#check missing_upper_implies_missing_lower
#print axioms upper_hodge_of_lower_native_sources
#print axioms missing_upper_implies_missing_lower

end GSTCardinalLowHalfLefschetzTransfer
