import GSTClassicalHodgeSeparatorPrimeCover

/-!
# GST CLASSICAL HODGE — AMBIENT PRIME INTERVAL COLLAPSE

The separator quotient prime covers zero in the source-prime quotient.  Pulling
this statement back through the quotient map says that there is no ambient
prime strictly between the source projective prime and the separator successor
prime.

This is the exact prime-order statement needed to transport quotient height one
to relative coheight one in the reduced source closure.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
open GSTClassicalHodgeSeparatorPrimeCover

namespace GSTClassicalHodgeSeparatorAmbientPrimeInterval

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any prime between the source prime and the separator successor prime is one
of the two endpoints. -/
theorem prime_between_source_separator_eq_endpoint
    (n : Nat) (x : projectiveSpace n)
    (R : Ideal (ProjectiveCoordinateRing n))
    (hRPrime : R.IsPrime)
    (hsource : x.asHomogeneousIdeal.toIdeal ≤ R)
    (hsucc : R ≤ separatorAmbientPrime n x) :
    R = x.asHomogeneousIdeal.toIdeal ∨ R = separatorAmbientPrime n x := by
  let P := x.asHomogeneousIdeal.toIdeal
  let π := Ideal.Quotient.mk P
  let r : Ideal (pointQuotient n x) := R.map π
  have hrPrime : r.IsPrime := by
    dsimp [r, π, P]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hsource
  have hrle : r ≤ separatorMinimalPrime n x := by
    have hmap : (R.map (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal)) ≤
        ((separatorAmbientPrime n x).map
          (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal)) :=
      Ideal.map_mono (f := Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal) hsucc
    have hsuccMap : (separatorAmbientPrime n x).map
        (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal) =
          separatorMinimalPrime n x := by
      unfold separatorAmbientPrime
      exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    rw [hsuccMap] at hmap
    exact hmap
  rcases prime_le_separator_eq_bot_or_self n x r hrPrime hrle with hbot | hself
  · left
    have hcomap := congrArg (Ideal.comap π) hbot
    have hRP : (R.map π).comap π = P ⊔ R := by
      exact Ideal.comap_map_quotientMk P R
    have hbotComap : (⊥ : Ideal (pointQuotient n x)).comap π = P := by
      ext a
      simp [π, P, Ideal.Quotient.eq_zero_iff_mem]
    rw [hRP, hbotComap] at hcomap
    exact (sup_eq_right.mpr hsource).symm.trans hcomap
  · right
    have hcomap := congrArg (Ideal.comap π) hself
    have hRP : (R.map π).comap π = P ⊔ R := by
      exact Ideal.comap_map_quotientMk P R
    have hQP : (separatorMinimalPrime n x).comap π =
        separatorAmbientPrime n x := rfl
    rw [hRP, hQP] at hcomap
    rw [sup_eq_right.mpr hsource] at hcomap
    exact hcomap

/-- Strict form: no ambient prime lies strictly between source and successor. -/
theorem no_prime_strictly_between_source_separator
    (n : Nat) (x : projectiveSpace n) :
    ¬ ∃ R : Ideal (ProjectiveCoordinateRing n),
      R.IsPrime
        ∧ x.asHomogeneousIdeal.toIdeal < R
        ∧ R < separatorAmbientPrime n x := by
  rintro ⟨R, hRp, hPR, hRQ⟩
  rcases prime_between_source_separator_eq_endpoint n x R hRp hPR.le hRQ.le with hP | hQ
  · exact hPR.ne hP.symm
  · exact hRQ.ne hQ

#check prime_between_source_separator_eq_endpoint
#check no_prime_strictly_between_source_separator

#print axioms prime_between_source_separator_eq_endpoint
#print axioms no_prime_strictly_between_source_separator

end GSTClassicalHodgeSeparatorAmbientPrimeInterval
