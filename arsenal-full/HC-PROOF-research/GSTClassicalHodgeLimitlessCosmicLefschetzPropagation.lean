import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTUniversalLefschetzPathFormula
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — LIMITLESS COSMIC LEFSCHETZ PROPAGATION

The cross-weight Hodge scalar is not inserted by hand.  It is the exact
coefficient produced by the global unbounded GST Lefschetz operator.

Starting at the genuine compact cosmic Hodge generator `delta_(p,p)`, the
only path reaching `(q,q)` after `2(q-p)` steps uses exactly `q-p` digit moves
and `q-p` carry moves.  Its multiplicity is therefore the central binomial
coefficient.  Projecting the resulting completed cosmic state back to the
`(q,q)` diagonal weight gives precisely that scalar times the target Hodge
generator.

Thus the within-weight matrix-unit artery and the cross-weight Lefschetz artery
both live in the same completed/compact limitless cosmos.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeLimitlessCosmicLefschetzPropagation

open GSTWorldCosmology
open GSTUniversalLefschetzCosmology
open GSTUniversalLefschetzPathFormula
open GSTDimensionFreeHodgeDiagonal
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeCrossWeightNativePropagation
open scoped BigOperators

/-- Completed-cosmos diagonal projector.  Unlike a finite world projector, it
has no terminal weight. -/
def completedDiagonalProjector (p : ℕ) : Module.End ℤ CompletedCosmos where
  toFun f := fun c => if c = (p,p) then f c else 0
  map_add' := by
    intro f g
    funext c
    by_cases h : c = (p, p)
    · simp [h]
    · simp [h]
  map_smul' := by
    intro z f
    funext c
    by_cases h : c = (p, p)
    · simp [h]
    · simp [h]

@[simp]
theorem completedDiagonalProjector_apply_self
    (p : ℕ) (f : CompletedCosmos) :
    completedDiagonalProjector p f (p,p) = f (p,p) := by
  simp [completedDiagonalProjector]

/-- The completed projector fixes the genuine compact cosmic Hodge generator. -/
@[simp]
theorem completedDiagonalProjector_generator
    (p : ℕ) :
    completedDiagonalProjector p (cosmicDiagonalClass p) =
      fun c => cosmicDiagonalClass p c := by
  funext c
  by_cases h : c = (p,p)
  · subst c
    simp [completedDiagonalProjector]
  · simp [completedDiagonalProjector, cosmicDiagonalClass, h, Ne.symm h]

/-- A mixed cosmic path from `(p,p)` can hit `(p+d,p+d)` after `2d` total
steps only when it uses exactly `d` digit moves and `d` carry moves. -/
theorem cosmic_mixed_path_to_diagonal
    (p d m : ℕ) :
    cosmicDigitShift m
        (cosmicCarryShift (2*d-m) (cosmicDiagonalClass p))
        (p+d,p+d) =
      if m = d then 1 else 0 := by
  by_cases hmd : m = d
  · subst m
    have h1 : d ≤ p + d := by omega
    have h2 : 2 * d - d ≤ p + d := by omega
    have h3 : p + d - (2 * d - d) = p := by omega
    have h4 : p + d - d = p := by omega
    simp [cosmicDigitShift, cosmicCarryShift, cosmicDiagonalClass,
      h1, h2, h3, h4]
  · by_cases hm : m ≤ p+d
    · by_cases hc : 2*d-m ≤ p+d
      · simp only [cosmicDigitShift, if_pos hm,
          cosmicCarryShift, if_pos hc]
        have hpoint :
            (p+d-(2*d-m), p+d-m) ≠ (p,p) := by
          intro h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          apply hmd
          omega
        simp [cosmicDiagonalClass, hpoint, hmd]
      · simp [cosmicDigitShift, cosmicCarryShift, hm, hc, hmd]
    · simp [cosmicDigitShift, hm, hmd]

/-- **GLOBAL CENTRAL-BINOMIAL LEFSCHETZ LAW.**
The exact `(p+d,p+d)` coefficient after `2d` unbounded Lefschetz steps from
weight `p` is `choose(2d,d)`. -/
theorem cosmicLefschetz_diagonal_coefficient
    (p d : ℕ) :
    ((cosmicLefschetz^(2*d)) (cosmicDiagonalClass p)) (p+d,p+d) =
      ((2*d).choose d : ℤ) := by
  rw [cosmicLefschetz_paths]
  rw [Finset.sum_apply]
  classical
  rw [Finset.sum_eq_single d]
  · simp [cosmic_mixed_path_to_diagonal]
  · intro m hm hmd
    simp [cosmic_mixed_path_to_diagonal, hmd]
  · intro hd
    exact (hd (Finset.mem_range.mpr (by omega))).elim

/-- Version indexed by source and target weights. -/
theorem cosmicLefschetz_target_coefficient
    (p q : ℕ) (hpq : p ≤ q) :
    ((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) =
      ((2*(q-p)).choose (q-p) : ℤ) := by
  have hq : p + (q-p) = q := Nat.add_sub_of_le hpq
  simpa [hq] using cosmicLefschetz_diagonal_coefficient p (q-p)

/-- The existing rational `limitlessLefschetzScalar` is exactly the rational
cast of the coefficient produced by the actual global cosmic operator. -/
theorem limitlessLefschetzScalar_eq_cosmic_coefficient
    (p q : ℕ) (hpq : p ≤ q) :
    limitlessLefschetzScalar p q =
      (((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) : ℚ) := by
  rw [cosmicLefschetz_target_coefficient p q hpq]
  rfl

/-- Projecting the global evolved state onto the target diagonal produces
exactly the central-binomial multiple of the target cosmic Hodge generator. -/
theorem completedProjector_cosmicLefschetz_generator
    (p q : ℕ) (hpq : p ≤ q) :
    completedDiagonalProjector q
        ((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) =
      ((2*(q-p)).choose (q-p) : ℤ) •
        (fun c => cosmicDiagonalClass q c) := by
  funext c
  by_cases hc : c = (q,q)
  · subst c
    simp [completedDiagonalProjector,
      cosmicLefschetz_target_coefficient p q hpq]
  · simp [completedDiagonalProjector, cosmicDiagonalClass, hc, Ne.symm hc]

/-- Every source-to-target pure-Hodge jump therefore has a nonzero coefficient
in the actual completed cosmos. -/
theorem cosmicLefschetz_target_coefficient_ne_zero
    (p q : ℕ) (hpq : p ≤ q) :
    ((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) ≠ 0 := by
  rw [cosmicLefschetz_target_coefficient p q hpq]
  exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))

/-- Finite windows recover the same global coefficient whenever the source and
target are visible. -/
theorem finite_observation_recovers_cosmic_transport
    (p q A B : ℕ) (hpq : p ≤ q)
    (hqA : q < A) (hqB : q < B) :
    observe A B ((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p))
        (⟨q,hqA⟩,⟨q,hqB⟩) =
      ((2*(q-p)).choose (q-p) : ℤ) := by
  change ((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) = _
  exact cosmicLefschetz_target_coefficient p q hpq

/-- Limitless cross-weight crown: the scalar used by the classical propagation
layer is exactly the true cosmic Lefschetz coefficient and remains visible in
every sufficiently large finite chart. -/
theorem limitless_cosmic_lefschetz_crown :
    ∀ p q : ℕ, p ≤ q →
      (((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) =
        ((2*(q-p)).choose (q-p) : ℤ))
      ∧ (limitlessLefschetzScalar p q =
        (((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) : ℚ))
      ∧ (((cosmicLefschetz^(2*(q-p))) (cosmicDiagonalClass p)) (q,q) ≠ 0) := by
  intro p q hpq
  exact ⟨cosmicLefschetz_target_coefficient p q hpq,
    limitlessLefschetzScalar_eq_cosmic_coefficient p q hpq,
    cosmicLefschetz_target_coefficient_ne_zero p q hpq⟩

#check completedDiagonalProjector
#check cosmic_mixed_path_to_diagonal
#check cosmicLefschetz_diagonal_coefficient
#check cosmicLefschetz_target_coefficient
#check limitlessLefschetzScalar_eq_cosmic_coefficient
#check completedProjector_cosmicLefschetz_generator
#check finite_observation_recovers_cosmic_transport
#check limitless_cosmic_lefschetz_crown

#print axioms cosmic_mixed_path_to_diagonal
#print axioms cosmicLefschetz_diagonal_coefficient
#print axioms cosmicLefschetz_target_coefficient
#print axioms limitlessLefschetzScalar_eq_cosmic_coefficient
#print axioms completedProjector_cosmicLefschetz_generator
#print axioms limitless_cosmic_lefschetz_crown

end GSTClassicalHodgeLimitlessCosmicLefschetzPropagation
