import Mathlib

/-!
# Three-twist extraction of an actual singular-stratum source

Uncompiled proof draft. In geometry a,d are divisor classes on the resolved
spectral variety; push is proper Chow return to the original X. The A_n
intersection equations and actual source geometry are proved/checked before
using this algebra. A scalar finite difference does not supply that geometry.
-/

namespace GSTSingularBranchExtraction
variable {R C : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup C] [Module ℚ C]

def twistSquare (a d : R) (k : ℚ) : R := (a+(2*k) • d)^2

theorem three_twist_identity (a d : R) :
    twistSquare a d 1+twistSquare a d (-1)-(2 : ℚ) • twistSquare a d 0=(8 : ℚ) • d^2 := by
  have h2 : (algebraMap ℚ R) (2 : ℚ) = (2 : R) := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by rw [Nat.cast_ofNat], map_natCast, Nat.cast_ofNat]
  have h8 : (algebraMap ℚ R) (8 : ℚ) = (8 : R) := by
    rw [show (8 : ℚ) = ((8 : ℕ) : ℚ) from by rw [Nat.cast_ofNat], map_natCast, Nat.cast_ofNat]
  simp only [twistSquare, Algebra.smul_def]
  norm_num [h2, h8]
  ring

theorem centered_twist_identity (a d : R) (t h : ℚ) :
    twistSquare a d (t+h)+twistSquare a d (t-h)-(2 : ℚ) • twistSquare a d t=
      (8*h^2) • d^2 := by
  have h2 : (algebraMap ℚ R) (2 : ℚ) = (2 : R) := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from by rw [Nat.cast_ofNat], map_natCast, Nat.cast_ofNat]
  have h8 : (algebraMap ℚ R) (8 : ℚ) = (8 : R) := by
    rw [show (8 : ℚ) = ((8 : ℕ) : ℚ) from by rw [Nat.cast_ofNat], map_natCast, Nat.cast_ofNat]
  simp only [twistSquare,Algebra.smul_def,map_add,map_sub,map_mul,map_pow,h2,h8]
  norm_num
  ring

theorem three_returned_cycles (push : R →ₗ[ℚ] C) (a d : R) :
    push (twistSquare a d 1)+push (twistSquare a d (-1))-
      (2 : ℚ) • push (twistSquare a d 0)=(8 : ℚ) • push (d^2) := by
  rw [← map_smul,← map_add,← map_sub,three_twist_identity,map_smul]

/-- Exact normalization; no pairing or numerical equality substitutes for Chow. -/
theorem extracted_stratum (push : R →ₗ[ℚ] C) (a d : R)
    (stratum : C) (c : ℚ) (hc : c≠0) (hintersection : push (d^2)=c • stratum) :
    (8*c)⁻¹ • (push (twistSquare a d 1)+push (twistSquare a d (-1))-
      (2 : ℚ) • push (twistSquare a d 0))=stratum := by
  rw [three_returned_cycles,hintersection,smul_smul,smul_smul]
  have h : (8*c)⁻¹*(8*c)=1 := inv_mul_cancel₀ (mul_ne_zero (by norm_num) hc)
  rw [mul_assoc,h,one_smul]

def chainPair (i j : ℕ) : ℤ :=
  if i=j then -2 else if i+1=j ∨ j+1=i then 1 else 0

theorem chainPair_symmetric (i j : ℕ) : chainPair i j=chainPair j i := by
  simp only [chainPair,eq_comm,or_comm]

theorem distinct_exceptional_difference_square (i j : ℕ) (hij : i≠j) :
    chainPair i i+chainPair j j-chainPair i j-chainPair j i=
      if i+1=j ∨ j+1=i then -6 else -4 := by
  rw [← chainPair_symmetric i j]
  simp only [chainPair,if_pos rfl,if_neg hij]
  split_ifs <;> norm_num

theorem fixed_exceptional_difference_square (i : ℕ) :
    chainPair i i+chainPair i i-chainPair i i-chainPair i i=0 := by ring

theorem adjacent_normalization : (8*(-6 : ℚ))⁻¹= -1/48 := by norm_num
theorem nonadjacent_normalization : (8*(-4 : ℚ))⁻¹= -1/32 := by norm_num

#print axioms extracted_stratum
#print axioms distinct_exceptional_difference_square
end GSTSingularBranchExtraction
