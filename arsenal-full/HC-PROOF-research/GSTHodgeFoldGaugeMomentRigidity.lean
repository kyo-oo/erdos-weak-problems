import GSTHodgeSingleHypothesisConditional

/-!
# GST Hodge fold-gauge rigidity: exact orbit and detector laws

This is a mathematical obstruction audit for the ONE geometric hypothesis in
GSTHodgeSingleHypothesisConditional, not an extra Hodge hypothesis.

A rational GST fold recoordination U, when transported consistently on the
operator, source and detector, leaves *every* Hankel moment unchanged.
Thus invertible fold-gauge transformations cannot convert a singular
source-orbit certificate into a nonsingular one.

A second verified no-go identifies a degree trace acting as a left
eigenfunctional of a fold: every such Hankel moment has rank at most one,
already witnessed by its zero 2-by-2 minor.

Both statements are proved over arbitrary rational GST modules without
finiteness, eigenbasis selection, arbitrary target cycles, or any sorry.
They do not claim to generate the original-X algebraic source.
-/

noncomputable section

namespace GSTHodgeFoldGaugeMomentRigidity

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- A GST fold orbit, with the exact orientation T^(n+1) v = T (T^n v). -/
def foldIter (T : W →ₗ[ℚ] W) (v : W) : ℕ → W
  | 0 => v
  | n + 1 => T (foldIter T v n)

/-- Rational similarity of a GST fold under an invertible coordinate change. -/
def gaugeConjugate
    (U : W ≃ₗ[ℚ] W) (T : W →ₗ[ℚ] W) : W →ₗ[ℚ] W :=
  U.symm.toLinearMap.comp (T.comp U.toLinearMap)

/-- Gauge transformation carries every orbit iterate exactly. -/
theorem foldIter_gauge
    (U : W ≃ₗ[ℚ] W)
    (T : W →ₗ[ℚ] W)
    (v : W) (n : ℕ) :
    foldIter (gaugeConjugate U T) (U.symm v) n =
      U.symm (foldIter T v n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (gaugeConjugate U T)
            (foldIter (gaugeConjugate U T) (U.symm v) n) =
          U.symm (T (foldIter T v n))
      rw [ih]
      simp [gaugeConjugate, LinearMap.comp_apply]

/-- The GST Hankel moment at source v with detector ell. -/
def foldMoment
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ)
    (i j : ℕ) : ℚ :=
  ell (foldIter T v (i + j))

/-- Every moment is unchanged when the source, fold and detector
are ALL transported. Moving only one of them is not a gauge transformation. -/
theorem foldMoment_gauge
    (U : W ≃ₗ[ℚ] W)
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ)
    (i j : ℕ) :
    foldMoment (gaugeConjugate U T) (U.symm v)
        (ell.comp U.toLinearMap) i j =
      foldMoment T v ell i j := by
  change
    ell (U (foldIter (gaugeConjugate U T) (U.symm v) (i + j))) =
      ell (foldIter T v (i + j))
  rw [foldIter_gauge]
  simp

/-- Exact finite GST Hankel matrix. -/
def foldHankel
    (n : ℕ)
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => foldMoment T v ell i.val j.val

/-- Invertible GST fold recoordination preserves the ENTIRE matrix. -/
theorem foldHankel_gauge
    (n : ℕ)
    (U : W ≃ₗ[ℚ] W)
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ) :
    foldHankel n (gaugeConjugate U T) (U.symm v)
        (ell.comp U.toLinearMap) =
      foldHankel n T v ell := by
  ext i j
  exact foldMoment_gauge U T v ell i.val j.val

/-- The determinant certificate cannot be created by similarity alone. -/
theorem foldHankel_det_gauge
    (n : ℕ)
    (U : W ≃ₗ[ℚ] W)
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ) :
    (foldHankel n (gaugeConjugate U T) (U.symm v)
      (ell.comp U.toLinearMap)).det =
        (foldHankel n T v ell).det := by
  rw [foldHankel_gauge]

/-- A detector which is a left eigenfunctional reads a geometric
progression and therefore cannot distinguish multiple orbit directions. -/
theorem eigenDetector_foldIter
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ)
    (lam : ℚ)
    (heigen : ∀ x : W, ell (T x) = lam * ell x)
    (n : ℕ) :
    ell (foldIter T v n) = lam ^ n * ell v := by
  induction n with
  | zero =>
      simp [foldIter]
  | succ n ih =>
      change ell (T (foldIter T v n)) =
        lam ^ (n + 1) * ell v
      rw [heigen, ih, pow_succ]
      ring

theorem eigenDetector_foldMoment
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ)
    (lam : ℚ)
    (heigen : ∀ x : W, ell (T x) = lam * ell x)
    (i j : ℕ) :
    foldMoment T v ell i j = lam ^ (i + j) * ell v :=
  eigenDetector_foldIter T v ell lam heigen (i + j)

/-- The first nontrivial Hankel determinant vanishes under the
left-eigenfunctional restriction, regardless of whether the seed is nonzero. -/
theorem eigenDetector_firstMinor_zero
    (T : W →ₗ[ℚ] W)
    (v : W)
    (ell : W →ₗ[ℚ] ℚ)
    (lam : ℚ)
    (heigen : ∀ x : W, ell (T x) = lam * ell x) :
    foldMoment T v ell 0 0 * foldMoment T v ell 1 1 -
      foldMoment T v ell 0 1 * foldMoment T v ell 1 0 = 0 := by
  rw [eigenDetector_foldMoment T v ell lam heigen 0 0,
      eigenDetector_foldMoment T v ell lam heigen 1 1,
      eigenDetector_foldMoment T v ell lam heigen 0 1,
      eigenDetector_foldMoment T v ell lam heigen 1 0]
  norm_num
  ring

#check foldIter_gauge
#check foldMoment_gauge
#check foldHankel_gauge
#check foldHankel_det_gauge
#check eigenDetector_foldIter
#check eigenDetector_firstMinor_zero
#print axioms foldHankel_det_gauge
#print axioms eigenDetector_firstMinor_zero

end GSTHodgeFoldGaugeMomentRigidity
