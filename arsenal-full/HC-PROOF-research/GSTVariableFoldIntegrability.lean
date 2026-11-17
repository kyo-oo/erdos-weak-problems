import Mathlib

/-!
# GST variable fold: square equation versus differential integrability

Pointwise coordinate identities behind equations (8)--(10) of the derivation.
The Nijenhuis bracket calculation is proved there and independently tested by
Wolfram; it is not represented here as a completed Lean vector-field proof.
-/

namespace GSTVariableFoldIntegrability

def symplecticPair (v w : Fin 4 → ℝ) : ℝ :=
  v 0*w 1-v 1*w 0+v 2*w 3-v 3*w 2

noncomputable def variableFold (f : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-v 1, v 0, -(v 3)/f, f*v 2]

theorem variableFold_square (f : ℝ) (hf : f ≠ 0) (v : Fin 4 → ℝ) :
    variableFold f (variableFold f v) = -v := by
  ext i
  fin_cases i <;> simp [variableFold] <;> field_simp

theorem positive_energy_formula (f : ℝ) (v : Fin 4 → ℝ) :
    symplecticPair v (variableFold f v) =
      (v 0)^2+(v 1)^2+f*(v 2)^2+(v 3)^2/f := by
  simp [symplecticPair, variableFold]
  ring

theorem positive_energy_nonnegative (f : ℝ) (hf : 0 < f) (v : Fin 4 → ℝ) :
    0 ≤ symplecticPair v (variableFold f v) := by
  rw [positive_energy_formula]
  positivity

/-- The derived coefficient of N_J(partial_1,partial_3); df is f's derivative. -/
noncomputable def nijenhuisCoefficient (f df : ℝ) : ℝ := df/f

theorem nijenhuisCoefficient_zero_iff (f df : ℝ) (hf : f ≠ 0) :
    nijenhuisCoefficient f df = 0 ↔ df = 0 := by
  simp [nijenhuisCoefficient, hf]

theorem positive_square_fold_with_nonzero_bracket_coefficient :
    (∀ v : Fin 4 → ℝ, variableFold 2 (variableFold 2 v) = -v) ∧
    (∀ v : Fin 4 → ℝ, 0 ≤ symplecticPair v (variableFold 2 v)) ∧
    nijenhuisCoefficient 2 2 ≠ 0 := by
  refine ⟨fun v => variableFold_square 2 (by norm_num) v,
    fun v => positive_energy_nonnegative 2 (by norm_num) v, ?_⟩
  norm_num [nijenhuisCoefficient]

#print axioms variableFold_square
#print axioms nijenhuisCoefficient_zero_iff
end GSTVariableFoldIntegrability
