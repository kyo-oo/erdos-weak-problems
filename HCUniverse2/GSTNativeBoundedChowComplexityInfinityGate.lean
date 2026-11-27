import Mathlib

/-!
# Owner's physical GST infinity control and bounded Chow complexity gate

Full ORIGINAL-X geometric theorem:
research/derivations/GST_20261112_native_bounded_complexity_infinite_fiber_control_and_physical_Jordan_barrier.tex

New geometric source sufficient condition, proved externally at real
scheme-theoretic Chow level:
On smooth projective X_b -> B with flat prescribed alpha_b, ACTUAL
target-matching rational Chow cycles on a sequence b_n -> b_original
with uniform actual degree+denominator profile bound specialize to a
REAL Chow class of alpha on the ORIGINAL X, by proper relative
Chow parameter spaces. This uses only a convergent countable sequence.

This file verifies the exact finite-profile counting lemma and the
owner's actual U/J/M/[J,M] two-cell Jordan/idempotent barrier on physical
Navigation 0/1. Pure linear algebra is not incorrectly identified
with scheme-theoretic Chow source creation.
-/
set_option maxHeartbeats 3500000
noncomputable section

namespace GSTNativeBoundedChowComplexityInfinityGate

/-- If the genuine GST input worlds form an infinite set but the
Chow degree/denominator profiles lie in a FINITE set, then a SINGLE
profile occurs infinitely often. The geometric theorem adds the
independent data of algebraic cycles over converging distinct fibers. -/
theorem infinite_native_worlds_finite_chow_profile
    {I : Type*} {J : Type*} [Finite J]
    (worlds : Set I) (profile : I → J)
    (hInfinite : ¬ worlds.Finite) :
    ∃ j : J, ¬ (worlds ∩ profile ⁻¹' {j}).Finite := by
  classical
  by_contra h
  push_neg at h
  have hFinite : (⋃ j : J, worlds ∩ profile ⁻¹' {j}).Finite :=
    Set.finite_iUnion h
  have hCover : (⋃ j : J, worlds ∩ profile ⁻¹' {j}) = worlds := by
    ext w
    constructor
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨j, hj⟩
      exact hj.1
    · intro hw
      apply Set.mem_iUnion.mpr
      exact ⟨profile w, ⟨hw, rfl⟩⟩
  rw [hCover] at hFinite
  exact hInfinite hFinite

/-- Exact owner's original physical null/maximum CM factor at
DIRECT SURVIVE strength one, Navigation OFF. -/
def offFold (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 + z.2, -z.1 + 3 * z.2)

/-- Actual physical Navigation ON original fixed GST fold. -/
def onFold (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 + 3 * z.2, z.1 + 3 * z.2)

/-- The original OFF fold is 2 I plus a nonzero nilpotent. -/
def offJordanNil (z : ℚ × ℚ) : ℚ × ℚ :=
  (-z.1 + z.2, -z.1 + z.2)

/-- Exact source Jordan decomposition, not an invented wave. -/
theorem offFold_jordan (z : ℚ × ℚ) :
    offFold z =
      (2 * z.1 + (offJordanNil z).1,
       2 * z.2 + (offJordanNil z).2) := by
  rcases z with ⟨a, b⟩
  apply Prod.ext <;> dsimp [offFold, offJordanNil] <;> ring

/-- Square-zero GST OFF Jordan defect. -/
theorem offJordanNil_square_zero (z : ℚ × ℚ) :
    offJordanNil (offJordanNil z) = (0, 0) := by
  rcases z with ⟨a,b⟩
  apply Prod.ext <;> dsimp [offJordanNil] <;> ring

/-- ON scaled wave is an exact rank-one projector. -/
def onProjector (z : ℚ × ℚ) : ℚ × ℚ :=
  ((z.1 + 3 * z.2) / 4, (z.1 + 3 * z.2) / 4)

theorem onProjector_idempotent (z : ℚ × ℚ) :
    onProjector (onProjector z) = onProjector z := by
  rcases z with ⟨a,b⟩
  apply Prod.ext <;> dsimp [onProjector] <;> ring

theorem onFold_is_four_projector (z : ℚ × ℚ) :
    onFold z = (4*(onProjector z).1,4*(onProjector z).2) := by
  rcases z with ⟨a,b⟩
  apply Prod.ext <;> dsimp [onFold, onProjector] <;> ring

/-- Native rank-collapse is exact: the normalized ON orbit always
lies in the diagonal rational subspace (a,a). -/
theorem onProjector_diagonal (z : ℚ × ℚ) :
    (onProjector z).1 = (onProjector z).2 := rfl

/-- Navigation OFF is genuinely NOT already diagonal/nilpotent-free:
the owner's original null seed has nonzero nilpotent source. -/
theorem offJordanNil_null_seed_nonzero :
    offJordanNil ((1:ℚ),0) ≠ (0,0) := by
  norm_num [offJordanNil]

#check infinite_native_worlds_finite_chow_profile
#check offFold_jordan
#check offJordanNil_square_zero
#check onProjector_idempotent
#check onFold_is_four_projector
#print axioms infinite_native_worlds_finite_chow_profile
#print axioms offJordanNil_square_zero
#print axioms onProjector_idempotent

end GSTNativeBoundedChowComplexityInfinityGate
