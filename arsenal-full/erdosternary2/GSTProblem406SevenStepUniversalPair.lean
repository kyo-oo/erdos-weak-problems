import GSTFourPowerNo22Magnitude
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Uniform seven-step physical common-two for EVERY positive integer

For every A>0, some j <= 7 and p >=1 have the literal same-row ternary
digit 2 in A*4^j and 4*(A*4^j).

No perfect-power hypothesis on A. No density assumption or global hGate.
The proof is a complete 18-unit-class Fin 27 arithmetic certificate,
plus exact physical three-adic valuation descent for sources divisible by 3.

For A=4^K this yields the power-of-four bounded-gap theorem (a separate
consequence, NOT the every-individual-exponent hGate).
-/

namespace GSTProblem406SevenStepUniversalPair

open GSTFourPowerDirectResidue

/-- Finite kernel arithmetic over all ternary units modulo 27: every
unit multiplier orbit reaches a physical same-row 2 pair at ternary
position 2 in at most seven steps. -/
private theorem finite_mod27_seven_step :
    ∀ r : Fin 27, r.val%3≠0 →
      ∃ j : Fin 8,
        digit3 (r.val*4^j.val) 2=2 ∧
        digit3 (4*(r.val*4^j.val)) 2=2 := by
  decide

/-- The physical digit at row 2 is exactly mod27-periodic
under multiplication by any fixed nonnegative natural multiplier. -/
private theorem digit3_mul_mod27 (A M : Nat) :
    digit3 (A*M) 2 = digit3 ((A%27)*M) 2 := by
  apply digit3_eq_of_mod_next
  change (A*M)%27 = ((A%27)*M)%27
  simp [Nat.mul_mod]

/-- Every positive ternary unit has a true common-two orbit witness,
with explicit row p=2 and j<=7. -/
theorem unit_source_seven_step (A : Nat) (hunit : A%3≠0) :
    ∃ j : Nat, j ≤ 7 ∧
      digit3 (A*4^j) 2=2 ∧
      digit3 (4*(A*4^j)) 2=2 := by
  let r : Fin 27 := ⟨A%27, Nat.mod_lt _ (by decide)⟩
  have hr : r.val%3 ≠ 0 := by
    dsimp [r]
    rw [Nat.mod_mod_of_dvd A (by decide : 3∣27)]
    exact hunit
  obtain ⟨j,hs,hn⟩ := finite_mod27_seven_step r hr
  refine ⟨j.val,by have hh:=j.isLt; omega,?_,?_⟩
  · rw [digit3_mul_mod27 A (4^j.val)]
    exact hs
  · calc
      digit3 (4*(A*4^j.val)) 2 =
        digit3 (A*(4*4^j.val)) 2 := by congr 1; ring
      _ = digit3 ((A%27)*(4*4^j.val)) 2 :=
        digit3_mul_mod27 A (4*4^j.val)
      _ = digit3 (4*((A%27)*4^j.val)) 2 := by congr 1; ring
      _ = 2 := hn

/-- Every ternary digit shifts one place upward under multiplication
by 3. This is an exact identity on integer digits, not a surrogate. -/
private theorem digit3_three_mul_shift (X p : Nat) :
    digit3 (3*X) (p+1) = digit3 X p := by
  have h := GSTFourPowerNo22Magnitude.digit3_div_three_pow_shift (3*X) 1 p
  have hcancel : (3*X)/3 = X := by omega
  simpa [hcancel, Nat.add_comm] using h.symm

/-- The full uniform theorem: for ALL A>0, at some j<=7, the
two literal consecutive quadruple orbit entries share a positive-row
digit 2. For v_3(A)=t, the finite certificate fires at row t+2. -/
theorem any_positive_source_pair_within_seven :
    ∀ A : Nat, 0 < A →
      ∃ j : Nat, j ≤ 7 ∧
        ∃ p : Nat, 1 ≤ p ∧
          digit3 (A*4^j) p=2 ∧
          digit3 (4*(A*4^j)) p=2 := by
  intro A
  induction A using Nat.strongRecOn with
  | ind A ih =>
    intro hA
    by_cases hz : A%3=0
    · let B := A/3
      have hdecomp : A%3 + 3*(A/3) = A := Nat.mod_add_div A 3
      have hAeq : A = 3*B := by dsimp [B]; omega
      have hBpos : 0 < B := by omega
      have hBlt : B < A := by
        dsimp [B]
        exact Nat.div_lt_self hA (by decide)
      obtain ⟨j,hj,p,hp,hs,hn⟩ := ih B hBlt hBpos
      refine ⟨j,hj,p+1,by omega,?_,?_⟩
      · calc
          digit3 (A*4^j) (p+1) =
            digit3 (3*(B*4^j)) (p+1) := by
              congr 1
              rw [hAeq]
              ring
          _ = digit3 (B*4^j) p := digit3_three_mul_shift _ _
          _ = 2 := hs
      · calc
          digit3 (4*(A*4^j)) (p+1) =
            digit3 (3*(4*(B*4^j))) (p+1) := by
              congr 1
              rw [hAeq]
              ring
          _ = digit3 (4*(B*4^j)) p := digit3_three_mul_shift _ _
          _ = 2 := hn
    · obtain ⟨j,hj,hs,hn⟩ := unit_source_seven_step A hz
      exact ⟨j,hj,2,by decide,hs,hn⟩

/-- Original production gate, guaranteed in every run of eight
consecutive powers-of-four exponents, derived using the general
multiplicative theorem rather than exponent-congruence case work. -/
theorem original_thirdWave_within_seven (K : Nat) :
    ∃ j : Nat, j ≤ 7 ∧
      GSTFourPowerThirdWave.thirdWave (K+j) := by
  obtain ⟨j,hj,p,hp,hs,hn⟩ :=
    any_positive_source_pair_within_seven (4^K) (by positivity)
  have hs' : digit3 (4^(K+j)) p=2 := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hs
  have hn' : digit3 (4^((K+j)+1)) p=2 := by
    have he : 4^(K+j+1)=4*(4^K*4^j) := by
      rw [pow_succ, pow_add]
      ring
    rw [he]
    exact hn
  refine ⟨j,hj,?_⟩
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact ⟨p,hp,hs',hn'⟩

#print axioms finite_mod27_seven_step
#print axioms unit_source_seven_step
#print axioms digit3_three_mul_shift
#print axioms any_positive_source_pair_within_seven
#print axioms original_thirdWave_within_seven

end GSTProblem406SevenStepUniversalPair
