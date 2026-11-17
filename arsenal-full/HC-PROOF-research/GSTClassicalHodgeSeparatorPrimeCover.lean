import GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
import Mathlib.RingTheory.Ideal.Height

/-!
# GST CLASSICAL HODGE — SEPARATOR PRIME COVERS THE SOURCE QUOTIENT ORIGIN

The chosen minimal prime over the source-specific separator has height exactly
one in the domain obtained by quotienting by the source projective prime.
Therefore there is no nontrivial prime strictly between the zero prime and the
separator prime.

This is the algebraic form of the relative codimension-one statement.  The
next topological adapter transports this cover relation through the projective
embedding and the reduced source-closure homeomorphism.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorSuccessorPoint

namespace GSTClassicalHodgeSeparatorPrimeCover

/-- The source-prime quotient is a domain, so its zero ideal is prime. -/
local instance quotientBotPrime
    (n : Nat) (x : projectiveSpace n) :
    (⊥ : Ideal (pointQuotient n x)).IsPrime := by
  letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
  infer_instance

/-- The chosen separator prime is nonzero: a height-one prime cannot equal the
height-zero prime of a domain. -/
theorem separatorMinimalPrime_ne_bot
    (n : Nat) (x : projectiveSpace n) :
    separatorMinimalPrime n x ≠ ⊥ := by
  intro h
  have hh := separatorMinimalPrime_height_one n x
  rw [h] at hh
  have hbot : (⊥ : Ideal (pointQuotient n x)).height = 0 := by
    letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
    exact (Ideal.height_eq_zero_iff).2
      (by simpa using (IsDomain.minimalPrimes_eq_singleton_bot
        (pointQuotient n x)).symm.le)
  rw [hbot] at hh
  norm_num at hh

/-- **HEIGHT-ONE COVER LAW.**
Every prime below the chosen separator prime is either the quotient origin or
the separator prime itself. -/
theorem prime_le_separator_eq_bot_or_self
    (n : Nat) (x : projectiveSpace n)
    (r : Ideal (pointQuotient n x))
    (hrPrime : r.IsPrime)
    (hr : r ≤ separatorMinimalPrime n x) :
    r = ⊥ ∨ r = separatorMinimalPrime n x := by
  letI : r.IsPrime := hrPrime
  letI : (separatorMinimalPrime n x).IsPrime :=
    (separatorMinimalPrime_mem n x).isPrime
  by_cases heq : r = separatorMinimalPrime n x
  · exact Or.inr heq
  · have hlt : r < separatorMinimalPrime n x := lt_of_le_of_ne hr heq
    have hheight : r.height < (separatorMinimalPrime n x).height := by
      haveI : (separatorMinimalPrime n x).FiniteHeight := by infer_instance
      exact Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [separatorMinimalPrime_height_one n x] at hheight
    have hr0 : r.height = 0 :=
      (Order.lt_one_iff).mp hheight
    have hmin : r ∈ minimalPrimes (pointQuotient n x) :=
      (Ideal.height_eq_zero_iff).1 hr0
    letI : IsDomain (pointQuotient n x) := pointQuotientIsDomain n x
    have hsingle := IsDomain.minimalPrimes_eq_singleton_bot (pointQuotient n x)
    rw [hsingle] at hmin
    exact Or.inl (Set.mem_singleton_iff.mp hmin)

/-- Strict form: there is no prime strictly between zero and the separator. -/
theorem no_prime_strictly_between_bot_separator
    (n : Nat) (x : projectiveSpace n) :
    ¬ ∃ r : Ideal (pointQuotient n x),
      r.IsPrime ∧ (⊥ : Ideal (pointQuotient n x)) < r ∧
        r < separatorMinimalPrime n x := by
  rintro ⟨r, hrp, h0r, hrq⟩
  rcases prime_le_separator_eq_bot_or_self n x r hrp hrq.le with hbot | hself
  · exact h0r.ne hbot.symm
  · exact hrq.ne hself

#check separatorMinimalPrime_ne_bot
#check prime_le_separator_eq_bot_or_self
#check no_prime_strictly_between_bot_separator

#print axioms prime_le_separator_eq_bot_or_self
#print axioms no_prime_strictly_between_bot_separator

end GSTClassicalHodgeSeparatorPrimeCover
