import GSTClassicalHodgeAtomicAnnihilator

/-!
# Rational coefficient descent from an arbitrary extension K/Q

The surface construction for CM abelian varieties can supply finite algebraic
coefficient combinations. Rational descent uses a Q-linear functional on K
taking 1 to 1. Every finite extension-linear combination of rational vectors
representing a rational target then descends to rational coefficients.

This is an honest linear algebra theorem, valid even for infinite extensions;
it does not assert existence of the geometric input cycles.
NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open GSTClassicalHodgeAtomicAnnihilator

namespace GSTClassicalHodgeCMCoefficientDescentCore

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A Q-linear retraction of the rational unit exists in every extension. -/
theorem exists_projection :
    ∃ epsilon : K →ₗ[ℚ] ℚ, epsilon 1 = 1 := by
  have hone : (1 : K) ∉ (⊥ : Submodule ℚ K) := by simp
  obtain ⟨ell, _, hne⟩ :=
    exists_linearFunctional_separating_submodule
      (⊥ : Submodule ℚ K) (1 : K) hone
  refine ⟨(ell 1)⁻¹ • ell, ?_⟩
  change (ell 1)⁻¹ • ell (1 : K) = (1 : ℚ)
  simpa [smul_eq_mul] using (inv_mul_cancel₀ hne)

theorem projection_fixes_rat
    (epsilon : K →ₗ[ℚ] ℚ)
    (hunit : epsilon 1 = 1) (r : ℚ) :
    epsilon (algebraMap ℚ K r) = r := by
  calc
    epsilon (algebraMap ℚ K r) =
        epsilon (r • (1 : K)) := by simp [Algebra.smul_def]
    _ = r • epsilon (1 : K) := epsilon.map_smul r 1
    _ = r := by simp [hunit, smul_eq_mul]

theorem projection_mul_rat
    (epsilon : K →ₗ[ℚ] ℚ) (c : K) (r : ℚ) :
    epsilon (c * algebraMap ℚ K r) = epsilon c * r := by
  calc
    epsilon (c * algebraMap ℚ K r) =
        epsilon (r • c) := by rw [Algebra.smul_def, mul_comm]
    _ = r • epsilon c := epsilon.map_smul r c
    _ = epsilon c * r := by simp [smul_eq_mul, mul_comm]

variable {I J : Type*}

/-- Descent of an explicit finite K-linear representation of rational vectors. -/
theorem finite_span_descends
    (s : Finset J) (coefficient : J → K)
    (vectors : J → I → ℚ) (target : I → ℚ)
    (h : ∀ i : I, algebraMap ℚ K (target i) =
       ∑ j ∈ s, coefficient j * algebraMap ℚ K (vectors j i)) :
    ∃ d : J → ℚ,
      ∀ i : I, target i = ∑ j ∈ s, d j * vectors j i := by
  obtain ⟨eps, heps⟩ := exists_projection (K := K)
  refine ⟨fun j => eps (coefficient j), ?_⟩
  intro i
  calc
    target i = eps (algebraMap ℚ K (target i)) := by
      symm
      exact projection_fixes_rat eps heps (target i)
    _ = eps (∑ j ∈ s,
        coefficient j * algebraMap ℚ K (vectors j i)) := by rw [h i]
    _ = ∑ j ∈ s, eps (coefficient j) * vectors j i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact projection_mul_rat eps (coefficient j) (vectors j i)

#check finite_span_descends
#print axioms finite_span_descends

end GSTClassicalHodgeCMCoefficientDescentCore
