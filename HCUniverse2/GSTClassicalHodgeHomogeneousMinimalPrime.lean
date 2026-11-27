import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# GST CLASSICAL HODGE — HOMOGENEOUS MINIMAL-PRIME RIGIDITY

A projective principal cut is defined by homogeneous equations, but ordinary
Noetherian minimal-prime existence returns an `Ideal` rather than a bundled
homogeneous prime.  This file removes that mismatch abstractly.

If `I` is homogeneous and `Q` is minimal among prime ideals containing `I`,
then `Q` is homogeneous.  Indeed the homogeneous core of `Q` is itself prime;
because `I` is homogeneous it lies in that core; and minimality of `Q` forces
the core to equal `Q`.

This is pure graded commutative algebra.  No projective variety, Hodge datum,
cycle class, or GST coordinate assumption occurs.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GradedRing DirectSum SetLike

namespace GSTClassicalHodgeHomogeneousMinimalPrime

variable {ι σ A : Type*}
variable [CommRing A]
variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable {𝒜 : ι → σ} [GradedRing 𝒜]

/-- **HOMOGENEOUS MINIMAL-PRIME RIGIDITY.**
Every minimal prime over a homogeneous ideal is homogeneous. -/
theorem minimalPrime_isHomogeneous
    {I Q : Ideal A}
    (hI : I.IsHomogeneous 𝒜)
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous 𝒜 := by
  let Qh : Ideal A := (Q.homogeneousCore 𝒜).toIdeal
  have hQhPrime : Qh.IsPrime := by
    dsimp [Qh]
    exact hQ.isPrime.homogeneousCore
  have hIleQh : I ≤ Qh := by
    dsimp [Qh]
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hQ.le
  have hQhleQ : Qh ≤ Q := by
    dsimp [Qh]
    exact Ideal.toIdeal_homogeneousCore_le 𝒜 Q
  have hQleQh : Q ≤ Qh :=
    hQ.2 ⟨hQhPrime, hIleQh⟩ hQhleQ
  have hEq : Qh = Q := le_antisymm hQhleQ hQleQh
  exact (Ideal.IsHomogeneous.iff_eq 𝒜 Q).2 hEq

/-- The minimal prime may therefore be bundled canonically as a homogeneous
ideal without changing its underlying ordinary ideal. -/
noncomputable def minimalPrimeHomogeneousIdeal
    {I Q : Ideal A}
    (hI : I.IsHomogeneous 𝒜)
    (hQ : Q ∈ I.minimalPrimes) :
    HomogeneousIdeal 𝒜 :=
  ⟨Q, minimalPrime_isHomogeneous hI hQ⟩

@[simp]
theorem minimalPrimeHomogeneousIdeal_toIdeal
    {I Q : Ideal A}
    (hI : I.IsHomogeneous 𝒜)
    (hQ : Q ∈ I.minimalPrimes) :
    (minimalPrimeHomogeneousIdeal hI hQ).toIdeal = Q :=
  rfl

/-- Primehood is retained after bundling. -/
theorem minimalPrimeHomogeneousIdeal_isPrime
    {I Q : Ideal A}
    (hI : I.IsHomogeneous 𝒜)
    (hQ : Q ∈ I.minimalPrimes) :
    (minimalPrimeHomogeneousIdeal hI hQ).toIdeal.IsPrime := by
  simpa using hQ.isPrime

#check minimalPrime_isHomogeneous
#check minimalPrimeHomogeneousIdeal
#check minimalPrimeHomogeneousIdeal_isPrime

#print axioms minimalPrime_isHomogeneous
#print axioms minimalPrimeHomogeneousIdeal_isPrime

end GSTClassicalHodgeHomogeneousMinimalPrime
