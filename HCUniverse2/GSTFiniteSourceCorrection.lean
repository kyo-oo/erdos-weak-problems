import Mathlib

/-!
# Target-dependent finite and polynomial source correction

Proof draft; not compiled in this session. This is linear algebra over Q.
The scheme adapter derives the one-step class identity from independently
solved SOURCE fibers and actual native/Betti naturality. The identity is
an explicit hypothesis here, never a newly assumed target selector.

No commutation is required between individual source-return operators.
No finite-dimensional or global nilpotence assumption is used.
-/

open scoped BigOperators
noncomputable section

namespace GSTFiniteSourceCorrection

variable {V C W : Type*}
  [AddCommGroup V] [Module ℚ V]
  [AddCommGroup C] [Module ℚ C]
  [AddCommGroup W] [Module ℚ W]

/-- The partial cycle is constructed from alpha, including its residuals. -/
def partialCycle (N : Module.End ℚ V) (step : V → C) : ℕ → V → C
  | 0, _ => 0
  | n+1, x => partialCycle N step n x + step ((N^n) x)

/-- Exact error after every finite correction stage. -/
theorem partialCycle_class
    (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (N : Module.End ℚ V) (step : V → C)
    (step_class : ∀ x, cl (step x) = inc (x - N x))
    (n : ℕ) (x : V) :
    cl (partialCycle N step n x) = inc x - inc ((N^n) x) := by
  induction n with
  | zero => simp [partialCycle]
  | succ n ih =>
      rw [partialCycle, map_add, ih, step_class, map_sub, pow_succ']
      change inc x - inc ((N^n) x) +
        (inc ((N^n) x) - inc (N ((N^n) x))) =
        inc x - inc (N ((N^n) x))
      abel

/-- Local nilpotence at the prescribed target suffices for an exact cycle. -/
theorem exact_of_target_nilpotent
    (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (N : Module.End ℚ V) (step : V → C)
    (step_class : ∀ x, cl (step x) = inc (x - N x))
    (n : ℕ) (x : V) (hx : (N^n) x = 0) :
    cl (partialCycle N step n x) = inc x := by
  rw [partialCycle_class cl inc N step step_class, hx, map_zero, sub_zero]

/-- Unnormalized finite polynomial combination of the actual partial cycles. -/
def weightedCycle (N : Module.End ℚ V) (step : V → C)
    (r : ℕ) (c : ℕ → ℚ) (x : V) : C :=
  ∑ k ∈ Finset.range r, c k • partialCycle N step k x

theorem weightedCycle_class
    (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (N : Module.End ℚ V) (step : V → C)
    (step_class : ∀ x, cl (step x) = inc (x - N x))
    (r : ℕ) (c : ℕ → ℚ) (x : V) :
    cl (weightedCycle N step r c x) =
      (∑ k ∈ Finset.range r, c k) • inc x -
        inc (∑ k ∈ Finset.range r, c k • (N^k) x) := by
  simp only [weightedCycle, map_sum, map_smul,
    partialCycle_class cl inc N step step_class, smul_sub,
    Finset.sum_sub_distrib, Finset.sum_smul]

/-- Exact reconstruction from any finite annihilator with nonzero value at 1.
The error operator itself need not be nilpotent. -/
theorem exact_of_polynomial_annihilator
    (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (N : Module.End ℚ V) (step : V → C)
    (step_class : ∀ x, cl (step x) = inc (x - N x))
    (r : ℕ) (c : ℕ → ℚ) (x : V)
    (hpoly : (∑ k ∈ Finset.range r, c k • (N^k) x) = 0)
    (hvalue : (∑ k ∈ Finset.range r, c k) ≠ 0) :
    cl ((∑ k ∈ Finset.range r, c k)⁻¹ •
      weightedCycle N step r c x) = inc x := by
  rw [map_smul, weightedCycle_class cl inc N step step_class,
    hpoly, map_zero, sub_zero, smul_smul]
  simp [hvalue]

/-- Powers cannot improve a direction fixed by the total residual operator. -/
theorem powers_fix_of_fixed (N : Module.End ℚ V) (x : V)
    (hx : N x = x) (n : ℕ) : (N^n) x = x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change N ((N^n) x) = x
      rw [ih, hx]

/-- A surviving nonzero fixed mode forbids every proposed polynomial certificate. -/
theorem polynomial_certificate_forbids_fixed_mode
    (N : Module.End ℚ V) (x : V) (hx : N x = x)
    (r : ℕ) (c : ℕ → ℚ)
    (hpoly : (∑ k ∈ Finset.range r, c k • (N^k) x) = 0)
    (hvalue : (∑ k ∈ Finset.range r, c k) ≠ 0) : x = 0 := by
  have hsmul : (∑ k ∈ Finset.range r, c k) • x = 0 := by
    simpa only [powers_fix_of_fixed N x hx, Finset.sum_smul] using hpoly
  exact (smul_eq_zero.mp hsmul).resolve_left hvalue

/-- A concrete pair of noncommuting source-return operators whose TOTAL
error is square zero. Pairwise commutation would wrongly exclude this case. -/
def frameA : Matrix (Fin 2) (Fin 2) ℚ := !![1,1; 0,0]
def frameB : Matrix (Fin 2) (Fin 2) ℚ := !![0,0; 0,1]

theorem noncommuting_sources_admit_finite_correction :
    frameA * frameB ≠ frameB * frameA ∧
      (1 - (frameA + frameB)) * (1 - (frameA + frameB)) = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h
    norm_num [frameA, frameB, Matrix.mul_apply, Fin.sum_univ_succ] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [frameA, frameB, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ]

#print axioms partialCycle_class
#print axioms exact_of_polynomial_annihilator
#print axioms polynomial_certificate_forbids_fixed_mode

/-! ## The whole generalized fixed component, not just its eigenvectors

2026-10-28 continuation, uncompiled proof drafts. These statements isolate
the zero-Jordan component of the total source frame F=1-N. A class may be
in the source image and still be inaccessible to fixed-N polynomials.
-/

theorem powers_preserve_frame_difference (N : Module.End ℚ V) (n : ℕ) (x : V) :
    (N^n) (x-N x) = (N^n) x-N ((N^n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change N ((N^n) (x-N x))=N ((N^n) x)-N (N ((N^n) x))
      rw [ih,map_sub]

theorem polynomial_kills_frame_difference (N : Module.End ℚ V)
    (r : ℕ) (c : ℕ → ℚ) (x : V)
    (hpoly : (∑ k ∈ Finset.range r, c k • (N^k) x)=0) :
    (∑ k ∈ Finset.range r, c k • (N^k) (x-N x))=0 := by
  calc
    (∑ k ∈ Finset.range r, c k • (N^k) (x-N x)) =
        (∑ k ∈ Finset.range r, c k • (N^k) x)-
          N (∑ k ∈ Finset.range r, c k • (N^k) x) := by
            simp only [powers_preserve_frame_difference,smul_sub,
              Finset.sum_sub_distrib,map_sum,map_smul]
    _ = 0 := by rw [hpoly,map_zero,sub_self]

/-- Stronger than the earlier fixed-vector obstruction: ANY finite generalized
1-eigenvector of N is excluded from a certificate with nonzero value at 1. -/
theorem generalized_fixed_mode_forbids_certificate
    (N : Module.End ℚ V) (r : ℕ) (c : ℕ → ℚ)
    (hvalue : (∑ k ∈ Finset.range r,c k)≠0)
    (n : ℕ) (x : V) (hgeneralized : ((1-N)^n) x=0)
    (hpoly : (∑ k ∈ Finset.range r,c k • (N^k) x)=0) : x=0 := by
  induction n generalizing x with
  | zero => simpa using hgeneralized
  | succ n ih =>
      have hnext : ((1-N)^n) (x-N x)=0 := by
        simpa only [pow_succ,Module.End.mul_apply,LinearMap.sub_apply,
          Module.End.one_apply] using hgeneralized
      have hframe : x-N x=0 := ih (x-N x) hnext
        (polynomial_kills_frame_difference N r c x hpoly)
      exact polynomial_certificate_forbids_fixed_mode N x
        (sub_eq_zero.mp hframe).symm r c hpoly hvalue

#print axioms generalized_fixed_mode_forbids_certificate

end GSTFiniteSourceCorrection
