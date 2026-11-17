import Mathlib

/-!
# GST CM–NM Gaussian Rational Period Trace

Arithmetic mechanism motivated by the contributor's exact Equation (3):
  1/(x^n - y^(n+1))
and the request to combine Number Manipulation (NM) with complex
multiplication (CM) on abelian geometry rather than stay over ℝ.

Model the arithmetic coefficient field ℚ(i) by rational pairs and
explicit multiplication, conjugation, norm and field reciprocal.
Prove that conjugation of the indexed corrected denominator commutes
with every finite CM power, and that the field trace of the reciprocal
has an EXACT RATIONAL CLOSED FORM.

For u = a + i b != 0:
   Tr_{ℚ(i)/ℚ}(u⁻¹) = 2*a/(a²+b²).
The same formula applies at EACH index of the contributor's corrected
CM kernel, with u = x^n - y^(n+1).

This is a genuine CM NUMBER-THEORETIC RATIONAL DESCENT step, not just
real series algebra. It manufactures a canonical rational scalar from
paired conjugate complex coefficients. It does NOT assume or prove that
the coefficient is the period of a geometric Hodge cycle: an actual
period/cup/Gysin comparison and nonzero realization remain to prove.
-/

set_option maxHeartbeats 20000000

noncomputable section

namespace GSTCMNumberManipulationTrace

/-- ℚ(i) as rational real/imaginary coordinate pairs. -/
abbrev CMQ := ℚ × ℚ

def cmMul (z w : CMQ) : CMQ :=
  (z.1*w.1-z.2*w.2, z.1*w.2+z.2*w.1)

def cmSub (z w : CMQ) : CMQ := (z.1-w.1,z.2-w.2)
def cmConj (z : CMQ) : CMQ := (z.1,-z.2)
def cmNormSq (z : CMQ) : ℚ := z.1^2+z.2^2

/-- The Gaussian field reciprocal, totalized as usual at zero. -/
def cmInv (z : CMQ) : CMQ :=
  (z.1 / cmNormSq z, -z.2 / cmNormSq z)

def cmTrace (z : CMQ) : ℚ := 2*z.1

/-- Number-theoretic CM conjugation is multiplicative. -/
theorem cmConj_mul (z w : CMQ) :
    cmConj (cmMul z w) = cmMul (cmConj z) (cmConj w) := by
  rcases z with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp [cmConj, cmMul]
  ring

theorem cmConj_sub (z w : CMQ) :
    cmConj (cmSub z w) = cmSub (cmConj z) (cmConj w) := by
  rcases z with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp [cmConj, cmSub]
  ring

/-- Positivity is an arithmetic fact, not an assumed "period ≠ 0". -/
theorem cmNormSq_pos (z : CMQ) (hz : z ≠ 0) :
    0 < cmNormSq z := by
  by_contra h
  have hnonneg : 0 ≤ cmNormSq z := by
    unfold cmNormSq
    positivity
  have hz0 : z.1 = 0 ∧ z.2 = 0 := by
    have hzero : z.1^2 + z.2^2 ≤ 0 := by
      simpa [cmNormSq] using le_of_not_gt h
    constructor <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  apply hz
  exact Prod.ext hz0.1 hz0.2

theorem cmNormSq_conj (z : CMQ) :
    cmNormSq (cmConj z) = cmNormSq z := by
  rcases z with ⟨a,b⟩
  simp [cmConj,cmNormSq]

/-- Exact norm-normalized rational reciprocal is the multiplicative inverse. -/
theorem cmMul_inv (z : CMQ) (hz : z ≠ 0) :
    cmMul z (cmInv z) = (1,0) := by
  have hnorm : cmNormSq z ≠ 0 :=
    ne_of_gt (cmNormSq_pos z hz)
  rcases z with ⟨a,b⟩
  dsimp [cmNormSq,cmInv,cmMul] at *
  apply Prod.ext
  · dsimp
    field_simp
    <;> ring
  · dsimp
    field_simp
    <;> ring

/-- Exact rational trace of a genuine CM reciprocal. -/
theorem cmTrace_inv_formula (z : CMQ) :
    cmTrace (cmInv z) = (2*z.1)/(cmNormSq z) := by
  simp [cmTrace,cmInv]
  ring

/-- An imaginary CM component changes sign under conjugation, while
the trace is fixed: this is the algebraic source of rational descent. -/
theorem cmTrace_conj (z : CMQ) :
    cmTrace (cmConj z) = cmTrace z := by
  simp [cmTrace,cmConj]

theorem cmInv_conj (z : CMQ) :
    cmInv (cmConj z) = cmConj (cmInv z) := by
  rcases z with ⟨a,b⟩
  simp [cmInv,cmConj,cmNormSq,eq_comm]
  ring

/-- CM Gaussian powers, with no implicit real-coordinate truncation. -/
def cmPow (z : CMQ) : ℕ → CMQ
  | 0 => (1,0)
  | n+1 => cmMul z (cmPow z n)

theorem cmConj_pow (z : CMQ) (n : ℕ) :
    cmConj (cmPow z n) = cmPow (cmConj z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cmPow,cmConj_mul,ih]

/-- The original corrected index-dependent denominator over genuine
non-real CM arithmetic, instead of the earlier ℝ-only restriction. -/
def cmIndexedDenominator (x y : CMQ) (m : ℕ) : CMQ :=
  cmSub (cmPow x (m+1)) (cmPow y (m+2))

/-- Conjugation commutes with the corrected NM/CM denominator. -/
theorem cmIndexedDenominator_conj
    (x y : CMQ) (m : ℕ) :
    cmConj (cmIndexedDenominator x y m) =
      cmIndexedDenominator (cmConj x) (cmConj y) m := by
  simp [cmIndexedDenominator,cmConj_sub,cmConj_pow]

/-- Exact rational trace of the original corrected complex reciprocal:
this is a canonical rational scalar with no arbitrary zeta coefficient. -/
def cmIndexedNMTrace (x y : CMQ) (m : ℕ) : ℚ :=
  cmTrace (cmInv (cmIndexedDenominator x y m))

theorem cmIndexedNMTrace_exact (x y : CMQ) (m : ℕ) :
    cmIndexedNMTrace x y m =
      (2*(cmIndexedDenominator x y m).1) /
        cmNormSq (cmIndexedDenominator x y m) := by
  exact cmTrace_inv_formula _

/-- The number-manipulated CM scalar agrees across the conjugate
embedding. The result is rational for EVERY index with no transcendental
period assumption or free choice of coefficient. -/
theorem cmIndexedNMTrace_conj
    (x y : CMQ) (m : ℕ) :
    cmIndexedNMTrace (cmConj x) (cmConj y) m =
      cmIndexedNMTrace x y m := by
  unfold cmIndexedNMTrace
  rw [← cmIndexedDenominator_conj]
  rw [cmInv_conj]
  exact cmTrace_conj _

/-- A nonzero real part of the CM denominator certifies a nonzero trace.
A purely imaginary denominator can have ZERO trace: one cannot
automatically equate nonzero complex periods with nonzero trace. -/
theorem cmIndexedNMTrace_ne_zero_of_real_ne_zero
    (x y : CMQ) (m : ℕ)
    (hreal : (cmIndexedDenominator x y m).1 ≠ 0) :
    cmIndexedNMTrace x y m ≠ 0 := by
  have hden : cmIndexedDenominator x y m ≠ 0 := by
    intro h
    exact hreal (congrArg Prod.fst h)
  rw [cmIndexedNMTrace_exact]
  exact div_ne_zero (mul_ne_zero (by norm_num) hreal)
    (ne_of_gt (cmNormSq_pos _ hden))

#check cmMul_inv
#check cmTrace_inv_formula
#check cmConj_pow
#check cmIndexedDenominator_conj
#check cmIndexedNMTrace_exact
#check cmIndexedNMTrace_conj
#check cmIndexedNMTrace_ne_zero_of_real_ne_zero

#print axioms cmMul_inv
#print axioms cmIndexedNMTrace_exact
#print axioms cmIndexedNMTrace_conj
#print axioms cmIndexedNMTrace_ne_zero_of_real_ne_zero

end GSTCMNumberManipulationTrace
