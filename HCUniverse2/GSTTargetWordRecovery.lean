import Mathlib

/-!
# Target-first source recovery by ordered words

Uncompiled proof draft. Unlike the existing algebraic-spine word frames,
the tail is read on the prescribed target and no native tail endomorphism
is requested. Empty words are excluded. Source existence and any geometric
operator identity still require independent proof.
-/

open scoped BigOperators
noncomputable section
namespace GSTTargetWordRecovery

variable {V C W ι J : Type*}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup C] [Module ℚ C]
  [AddCommGroup W] [Module ℚ W]

def wordOperator (F : ι → Module.End ℚ V) : List ι → Module.End ℚ V
  | [] => 1
  | i::tail => F i * wordOperator F tail

/-- Every admissible word has a head; no cycle is requested for the empty word. -/
abbrev NonemptyWord (ι : Type*) := ι × List ι

def wordCycle (F : ι → Module.End ℚ V) (step : ι → V → C)
    (word : NonemptyWord ι) (alpha : V) : C :=
  step word.1 (wordOperator F word.2 alpha)

theorem wordCycle_class (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (F : ι → Module.End ℚ V) (step : ι → V → C)
    (hstep : ∀ i x, cl (step i x)=inc (F i x))
    (word : NonemptyWord ι) (alpha : V) :
    cl (wordCycle F step word alpha)=inc (wordOperator F (word.1::word.2) alpha) := by
  exact hstep word.1 (wordOperator F word.2 alpha)

def finiteWordCycle (F : ι → Module.End ℚ V) (step : ι → V → C)
    (s : Finset J) (word : J → NonemptyWord ι) (coeff : J → ℚ) (alpha : V) : C :=
  ∑ j ∈ s, coeff j • wordCycle F step (word j) alpha

theorem finiteWordCycle_class (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (F : ι → Module.End ℚ V) (step : ι → V → C)
    (hstep : ∀ i x, cl (step i x)=inc (F i x))
    (s : Finset J) (word : J → NonemptyWord ι) (coeff : J → ℚ) (alpha : V) :
    cl (finiteWordCycle F step s word coeff alpha)=
      inc (∑ j ∈ s, coeff j • wordOperator F ((word j).1::(word j).2) alpha) := by
  simp only [finiteWordCycle, map_sum, map_smul, wordCycle_class cl inc F step hstep]

theorem exact_target_of_word_relation (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (F : ι → Module.End ℚ V) (step : ι → V → C)
    (hstep : ∀ i x, cl (step i x)=inc (F i x))
    (s : Finset J) (word : J → NonemptyWord ι) (coeff : J → ℚ) (alpha : V)
    (hword : (∑ j ∈ s, coeff j • wordOperator F ((word j).1::(word j).2) alpha)=alpha) :
    cl (finiteWordCycle F step s word coeff alpha)=inc alpha := by
  rw [finiteWordCycle_class cl inc F step hstep, hword]

/-- A denominator-free explicit constructor from three length-four words. -/
def fourthOrderCycle (A B D : Module.End ℚ V) (stepA stepB : V → C) (alpha : V) : C :=
  stepA (A (B (B alpha))) + stepA (A (D (D alpha))) + stepB (B (D (D alpha)))

theorem fourthOrderCycle_class (cl : C →ₗ[ℚ] W) (inc : V →ₗ[ℚ] W)
    (A B D : Module.End ℚ V) (stepA stepB : V → C)
    (hA : ∀ x, cl (stepA x)=inc (A x)) (hB : ∀ x, cl (stepB x)=inc (B x))
    (hidentity : A*A*B*B + A*A*D*D + B*B*D*D=1) (alpha : V) :
    cl (fourthOrderCycle A B D stepA stepB alpha)=inc alpha := by
  have hvector := congrArg (fun T : Module.End ℚ V => T alpha) hidentity
  change A (A (B (B alpha))) + A (A (D (D alpha))) + B (B (D (D alpha)))=alpha at hvector
  simp only [fourthOrderCycle, map_add, hA, hB]
  rw [← map_add, ← map_add, hvector]

def rotationA : Matrix (Fin 3) (Fin 3) ℚ := !![0,0,0;0,0,-1;0,1,0]
def rotationB : Matrix (Fin 3) (Fin 3) ℚ := !![0,0,1;0,0,0;-1,0,0]
def rotationC : Matrix (Fin 3) (Fin 3) ℚ := !![0,-1,0;1,0,0;0,0,0]

theorem every_weighted_frame_singular (x y z : ℚ) :
    Matrix.det (x • rotationA+y • rotationB+z • rotationC)=0 := by
  simp [rotationA, rotationB, rotationC, Matrix.det_fin_three, Matrix.add_apply,
    Matrix.smul_apply, Matrix.of_apply]
  ring

theorem quadratic_word_identity :
    rotationA*rotationA+rotationB*rotationB+rotationC*rotationC = -2 •
      (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationA, rotationB, rotationC, Matrix.mul_apply, Matrix.one_apply,
      Matrix.of_apply]

/-- Coefficients are integers even though the displayed carrier is rational. -/
theorem integral_fourth_order_identity :
    rotationA*rotationA*rotationB*rotationB +
      rotationA*rotationA*rotationC*rotationC +
      rotationB*rotationB*rotationC*rotationC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationA, rotationB, rotationC, Matrix.mul_apply, Matrix.one_apply,
      Matrix.of_apply]

theorem family_is_noncommuting : rotationA*rotationB ≠ rotationB*rotationA := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 0 1) h
  norm_num [rotationA, rotationB, Matrix.mul_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Fin.sum_univ_three] at h01

#print axioms exact_target_of_word_relation
#print axioms fourthOrderCycle_class
#print axioms every_weighted_frame_singular
#print axioms integral_fourth_order_identity
end GSTTargetWordRecovery
