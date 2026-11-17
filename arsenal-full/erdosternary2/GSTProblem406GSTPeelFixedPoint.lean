import GSTFourPowerAffineExponentPeel
import GSTFourPowerAffineOrbit
import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST non-archimedean fixed point and delayed physical survivors

Let s_m=(3^m-1)/2=111...1_3 (m digits). The one-trit
exponent peel has the exact nonlinear identity

  peel1 x = x + 3*x*(2*x+1)^2.

Thus its 3-adic fixed point is x=-1/2. The physical exponent
K_m=s_m approaches this non-natural 3-adic point, and the
original physical affine orbit satisfies A_(K_m)=K_m (mod 3^m).

Consequently the first m affine trits of 4^(K_m) are all 1,
hence the first m physical nontrivial trits of the genuine
consecutive powers cannot be a simultaneous pair of 2s.

These are arbitrarily long genuine finite survivors, NOT a fixed
integer exponent surviving infinitely many rows.
-/

namespace GSTProblem406GSTPeelFixedPoint

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel

/-- Natural m-digit ternary all-one exponent, defined without subtraction. -/
def ternaryOnes : Nat → Nat
  | 0 => 0
  | m+1 => 3*ternaryOnes m+1

/-- 2*ternaryOnes(m)+1=3^m, i.e. ternaryOnes=(3^m-1)/2. -/
theorem ternaryOnes_identity (m : Nat) :
    2*ternaryOnes m+1=3^m := by
  induction m with
  | zero => decide
  | succ m ih =>
      simp only [ternaryOnes, pow_succ]
      omega

theorem ternaryOnes_lt_pow (m : Nat) :
    ternaryOnes m < 3^m := by
  have h := ternaryOnes_identity m
  omega

/-- The next all-one exponent appends a single new HIGH ternary trit. -/
theorem ternaryOnes_high_succ (m : Nat) :
    ternaryOnes (m+1) = ternaryOnes m+3^m := by
  rw [ternaryOnes]
  have h := ternaryOnes_identity m
  omega

/-- Exact concatenation of two all-one ternary exponent blocks. -/
theorem ternaryOnes_add (j t : Nat) :
    ternaryOnes (j+t) = ternaryOnes j + 3^j*ternaryOnes t := by
  have hj := ternaryOnes_identity j
  have ht := ternaryOnes_identity t
  have hjt := ternaryOnes_identity (j+t)
  have heq : 2*(ternaryOnes j+3^j*ternaryOnes t)+1=3^(j+t) := by
    calc
      2*(ternaryOnes j+3^j*ternaryOnes t)+1 =
          (2*ternaryOnes j+1)+3^j*(2*ternaryOnes t) := by ring
      _ = 3^j+3^j*(2*ternaryOnes t) := by rw [hj]
      _ = 3^j*(2*ternaryOnes t+1) := by ring
      _ = 3^j*3^t := by rw [ht]
      _ = 3^(j+t) := (pow_add 3 j t).symm
  omega

/-- Every literal original finite ternaryOnes word has source digit 1
in every position below its length. -/
theorem ternaryOnes_digit_one
    (m j : Nat) (hj : j < m) :
    digit3 (ternaryOnes m) j = 1 := by
  have hN : 0<3^j := by positivity
  have hshape : ternaryOnes m =
      ternaryOnes j + 3^j*ternaryOnes (m-j) := by
    calc
      ternaryOnes m = ternaryOnes (j+(m-j)) := by congr 1; omega
      _ = ternaryOnes j+3^j*ternaryOnes (m-j) :=
        ternaryOnes_add j (m-j)
  have hquot : ternaryOnes m /3^j = ternaryOnes (m-j) := by
    rw [hshape,Nat.add_mul_div_left _ _ hN,
      Nat.div_eq_of_lt (ternaryOnes_lt_pow j)]
    simp
  unfold digit3
  rw [hquot]
  have ht : 0 < m-j := by omega
  cases h : (m-j) with
  | zero => omega
  | succ t =>
      simp [ternaryOnes]

/-- Nonlinear GST polynomial identity. -/
theorem peel1_exact_nonarchimedean_fixedpoint (x : Nat) :
    peel1 x = x + 3*x*(2*x+1)^2 := by
  unfold peel1
  ring

/-- The finite all-one coordinates approximate the fixed point:
the GST peel1 polynomial fixes each modulo 3^m. -/
theorem peel1_ternaryOnes_residue (m : Nat) :
    peel1 (ternaryOnes m) % 3^m =
      ternaryOnes m % 3^m := by
  rw [peel1_exact_nonarchimedean_fixedpoint,
    ternaryOnes_identity m]
  have hdiv : 3^m ∣ 3*ternaryOnes m*(3^m)^2 := by
    refine ⟨3*ternaryOnes m*3^m, ?_⟩
    ring
  have hzero : (3*ternaryOnes m*(3^m)^2) % 3^m = 0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.add_mod,hzero]
  simp

/-- The precise physical orbit at exponent (3^m-1)/2 agrees with
the m-digit all-one coordinate modulo 3^m.
This is the exact GST fixed-point congruence, not numerical fitting. -/
theorem physical_ternaryOnes_affine_fixedpoint (m : Nat) :
    affineOrbit (ternaryOnes m) % 3^m =
      ternaryOnes m % 3^m := by
  induction m with
  | zero => simp [ternaryOnes, affineOrbit]
  | succ m ih =>
      have hpoly :
          peel1 (affineOrbit (ternaryOnes m)) ≡
            peel1 (ternaryOnes m) [MOD 3^m] := by
        change (peel1 (affineOrbit (ternaryOnes m)))%3^m =
          (peel1 (ternaryOnes m))%3^m
        simp [peel1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ih]
      have hfixed :
          peel1 (ternaryOnes m) ≡ ternaryOnes m [MOD 3^m] :=
        peel1_ternaryOnes_residue m
      have htotal := hpoly.trans hfixed
      have hmul := htotal.mul_left' 3
      have hadd := hmul.add_left 1
      change (1+3*peel1 (affineOrbit (ternaryOnes m)))%(3*3^m) =
        (1+3*ternaryOnes m)%(3*3^m) at hadd
      have haddEq :
          (1+3*peel1 (affineOrbit (ternaryOnes m)))%(3*3^m) =
            (1+3*ternaryOnes m)%(3*3^m) := by
        exact hadd
      calc
        affineOrbit (ternaryOnes (m+1)) % 3^(m+1) =
            (1+3*peel1 (affineOrbit (ternaryOnes m)))%(3*3^m) := by
          rw [ternaryOnes, affineOrbit_three_mul_add_one, Nat.pow_succ]
          ring
        _ = (1+3*ternaryOnes m)%(3*3^m) := haddEq
        _ = ternaryOnes (m+1)%3^(m+1) := by
          rw [ternaryOnes, Nat.pow_succ]
          ring

/-- Strong physical source-word rigidity: for each m and every j<m,
the j+1-th ternary digit of the REAL 4^((3^m-1)/2) is exactly 1. -/
theorem physical_ternaryOnes_first_m_digits_are_one
    (m j : Nat) (hj : j < m) :
    digit3 (4^(ternaryOnes m)) (j+1)=1 := by
  have hdiv : 3^(j+1) ∣ 3^m := Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      affineOrbit (ternaryOnes m)%3^(j+1) =
        ternaryOnes m%3^(j+1) := by
    calc
      affineOrbit (ternaryOnes m)%3^(j+1) =
        (affineOrbit (ternaryOnes m)%3^m)%3^(j+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (ternaryOnes m%3^m)%3^(j+1) := by
        rw [physical_ternaryOnes_affine_fixedpoint m]
      _ = ternaryOnes m%3^(j+1) :=
        Nat.mod_mod_of_dvd _ hdiv
  calc
    digit3 (4^(ternaryOnes m)) (j+1) =
      digit3 (affineOrbit (ternaryOnes m)) j :=
        four_pow_digit_affine_shift (ternaryOnes m) j
    _ = digit3 (ternaryOnes m) j :=
      digit3_eq_of_mod_next _ _ j hmod
    _ = 1 := ternaryOnes_digit_one m j hj

/-- These increasingly long ORIGINAL perfect-power pairs have no
common-two row among the first m nontrivial physical trits. -/
theorem physical_ternaryOnes_survives_m_rows (m : Nat) :
    ∀ j : Nat, 1 ≤ j → j ≤ m →
      ¬ (digit3 (4^(ternaryOnes m)) j = 2 ∧
         digit3 (4^((ternaryOnes m)+1)) j = 2) := by
  intro j hj1 hjm hhit
  have hj : j-1 < m := by omega
  have heq := physical_ternaryOnes_first_m_digits_are_one m (j-1) hj
  have hshape : j-1+1=j := by omega
  rw [hshape] at heq
  omega

#print axioms ternaryOnes_identity
#print axioms ternaryOnes_add
#print axioms ternaryOnes_digit_one
#print axioms peel1_exact_nonarchimedean_fixedpoint
#print axioms peel1_ternaryOnes_residue
#print axioms physical_ternaryOnes_affine_fixedpoint
#print axioms physical_ternaryOnes_first_m_digits_are_one
#print axioms physical_ternaryOnes_survives_m_rows

end GSTProblem406GSTPeelFixedPoint
