import GSTClassicalHodgeCMCoefficientDescentCore

/-!
# CM Galois-conjugate tensor spans and nonzero periods

The surface-switch proof of the 2026 CM paper takes a class on the
conjugated line (c,c,1,1), then uses scalar conjugation and an
identification of copied abelian factors to recover (1,1,c,c).

The algebraic content is that any field automorphism sigma of K fixing
the rational scalars preserves the K-linear span of rational cycle
classes. It sends period k to sigma(k), which remains nonzero.
This module formalizes that assertion for finite tensor coordinates,
without asserting the geometric factor identifications themselves.

Unlike an ordinary rational-descent theorem, this handles a target
whose coefficients are not rational: its whole coordinate vector is
conjugated, and the rational geometric generators stay fixed.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 13000000

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeCMGaloisConjugateSpan

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {I J : Type*}

/-- Applying a rational-scalar-fixing automorphism to one algebraic
tensor expansion yields the exact conjugate expansion using the SAME
rational geometric generators. -/
theorem conjugate_finite_algebraic_span
    (sigma : K ≃+* K)
    (hRat : ∀ r : ℚ,
      sigma (algebraMap ℚ K r) = algebraMap ℚ K r)
    (s : Finset J)
    (coefficient : J → K)
    (vectors : J → I → ℚ)
    (target : I → K)
    (h : ∀ i : I,
      target i = ∑ j ∈ s,
        coefficient j * algebraMap ℚ K (vectors j i)) :
    ∀ i : I,
      sigma (target i) = ∑ j ∈ s,
        sigma (coefficient j) * algebraMap ℚ K (vectors j i) := by
  intro i
  calc
    sigma (target i) =
        sigma (∑ j ∈ s,
          coefficient j * algebraMap ℚ K (vectors j i)) := by
            rw [h i]
    _ = ∑ j ∈ s,
        sigma (coefficient j) * algebraMap ℚ K (vectors j i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [map_mul, hRat]

/-- Nonzero CM surface periods remain nonzero after conjugation.
An automorphism cannot kill a nonzero tensor-period scalar. -/
theorem conjugate_period_nonzero
    (sigma : K ≃+* K) (k : K) (hk : k ≠ 0) :
    sigma k ≠ 0 := by
  intro hzero
  apply hk
  apply sigma.injective
  simpa using hzero

/-- A rational-coefficient target is fixed by any scalar automorphism
fixing Q. The same target then admits the conjugated coefficients. -/
theorem rational_target_has_conjugated_coefficients
    (sigma : K ≃+* K)
    (hRat : ∀ r : ℚ,
      sigma (algebraMap ℚ K r) = algebraMap ℚ K r)
    (s : Finset J)
    (coefficient : J → K)
    (vectors : J → I → ℚ)
    (target : I → ℚ)
    (h : ∀ i : I,
      algebraMap ℚ K (target i) =
        ∑ j ∈ s,
          coefficient j * algebraMap ℚ K (vectors j i)) :
    ∀ i : I,
      algebraMap ℚ K (target i) =
        ∑ j ∈ s,
          sigma (coefficient j) * algebraMap ℚ K (vectors j i) := by
  intro i
  have hc := conjugate_finite_algebraic_span
    sigma hRat s coefficient vectors (fun i => algebraMap ℚ K (target i)) h i
  simpa only [hRat] using hc

#check conjugate_finite_algebraic_span
#check conjugate_period_nonzero
#print axioms conjugate_finite_algebraic_span

end GSTClassicalHodgeCMGaloisConjugateSpan
