import GSTCMNumberManipulationTrace

/-!
# GST CM indexed Number Manipulation isogeny source: every index legal

For the corrected Equation (3) with x=1+i and y=i, the Gaussian
denominator u_n=(1+i)^n-i^(n+1) is NONZERO for every positive index n.
This kernel proof uses multiplicativity of the exact rational
Gaussian norm, with N(1+i)=2 and N(i)=1. Therefore the two
Gaussian powers have different norms and cannot coincide.

Geometrically every u_n is a nonzero Gaussian integer and hence
its multiplication on E=C/(Z+iZ) is an actual algebraic CM
isogeny, with inverse rational correspondence 1/N(u_n)
times the graph of the conjugate isogeny. The scheme/cohomology
realization of this fact is not claimed as a kernel theorem here.

A stronger fact, that the IMAGINARY PART of u_n is nonzero
at every index, is mathematically derived by four residue
classes in the associated research manuscript but is NOT
asserted to be Lean-verified by this module. The first
attempt at that stronger kernel proof failed elaboration;
the present certified theorem isolates the verified
nonzero denominator needed for legitimate CM inversion.
-/

set_option maxHeartbeats 20000000
noncomputable section

namespace GSTCMNumberManipulationTrace

theorem cmNormSq_mul (z w : CMQ) :
    cmNormSq (cmMul z w) = cmNormSq z * cmNormSq w := by
  rcases z with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  dsimp [cmMul,cmNormSq]
  ring

theorem cmNormSq_pow (z : CMQ) (n : ℕ) :
    cmNormSq (cmPow z n) = (cmNormSq z)^n := by
  induction n with
  | zero =>
      norm_num [cmPow,cmNormSq]
  | succ n ih =>
      rw [cmPow,cmNormSq_mul, ih,pow_succ]
      ring

theorem cmIndexedDenominator_nonzero_every_index (m : ℕ) :
    cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) m ≠ 0 := by
  intro hz
  have heq : cmPow ((1,1):CMQ) (m+1) =
      cmPow ((0,1):CMQ) (m+2) := by
    apply Prod.ext
    · have hfst := congrArg Prod.fst hz
      dsimp [cmIndexedDenominator,cmSub] at hfst
      exact sub_eq_zero.mp hfst
    · have hsnd := congrArg Prod.snd hz
      dsimp [cmIndexedDenominator,cmSub] at hsnd
      exact sub_eq_zero.mp hsnd
  have hnorm := congrArg cmNormSq heq
  rw [cmNormSq_pow,cmNormSq_pow] at hnorm
  have hpow : (2:ℚ)^(m+1)=1 := by
    norm_num [cmNormSq] at hnorm
    exact hnorm
  have hbase : ∀ n:ℕ, (1:ℚ) ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        nlinarith
  have hgt : (1:ℚ) < 2^(m+1) := by
    rw [pow_succ]
    nlinarith [hbase m]
  exact (ne_of_gt hgt) hpow

#check cmNormSq_mul
#check cmNormSq_pow
#check cmIndexedDenominator_nonzero_every_index
#print axioms cmIndexedDenominator_nonzero_every_index

end GSTCMNumberManipulationTrace
