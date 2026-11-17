import GSTProblem406ArchimedeanPhysicalEscape
import GSTFourPowerThirdWave
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Global bounded gaps in the exact original physical third-wave gate

A 19-shift rational interval cover of [1,9) proves:
for any K, at least one of K, K+1, ..., K+18 admits a genuine
same-position ternary 2 in both original powers of four.

This is unconditional, no universal hGate, no finite bound on K,
and no computational scan of exponents.

It does NOT prove a common two for every individual K. The original
hGate remains strictly stronger.
-/

namespace GSTProblem406SyndeticArchimedeanGate

open GSTFourPowerDirectExistence

/-- Multiplicative phase window: A 4^j falls strictly between
7/8 of, and exactly, the upper nine-power boundary 9^e B. -/
def PhaseHit (A B j e : Nat) : Prop :=
  4^j * A < 9^e * B ∧ 7*(9^e*B) < 8*(4^j*A)

/-- Exact 19-piece rational certificate. Only inequalities involving
A and B appear; the 18 cutting fractions have been chosen strictly
inside the overlaps of neighboring power-of-four phase intervals.

The shifts, in interval order, are:
11,3,14,6,17,9,1,12,4,15,7,18,10,2,13,5,16,8,0.
-/
theorem phase_cover_nineteen
    (A B : Nat) (hB : 0 < B)
    (hlo : B ≤ A) (hhi : A < 9*B) :
    ∃ j e : Nat, j ≤ 18 ∧ PhaseHit A B j e := by
  by_cases h0 : 8*A < 9*B
  ·
    refine ⟨11, 7, by decide, ?_⟩
    change 4194304*A < 4782969*B ∧ 7*(4782969*B) < 8*(4194304*A)
    omega
  ·
    by_cases h1 : 19*A < 24*B
    ·
      refine ⟨3, 2, by decide, ?_⟩
      change 64*A < 81*B ∧ 7*(81*B) < 8*(64*A)
      omega
    ·
      by_cases h2 : 7*A < 10*B
      ·
        refine ⟨14, 9, by decide, ?_⟩
        change 268435456*A < 387420489*B ∧ 7*(387420489*B) < 8*(268435456*A)
        omega
      ·
        by_cases h3 : 5*A < 8*B
        ·
          refine ⟨6, 4, by decide, ?_⟩
          change 4096*A < 6561*B ∧ 7*(6561*B) < 8*(4096*A)
          omega
        ·
          by_cases h4 : 5*A < 9*B
          ·
            refine ⟨17, 11, by decide, ?_⟩
            change 17179869184*A < 31381059609*B ∧ 7*(31381059609*B) < 8*(17179869184*A)
            omega
          ·
            by_cases h5 : 1*A < 2*B
            ·
              refine ⟨9, 6, by decide, ?_⟩
              change 262144*A < 531441*B ∧ 7*(531441*B) < 8*(262144*A)
              omega
            ·
              by_cases h6 : 53*A < 119*B
              ·
                refine ⟨1, 1, by decide, ?_⟩
                change 4*A < 9*B ∧ 7*(9*B) < 8*(4*A)
                omega
              ·
                by_cases h7 : 2*A < 5*B
                ·
                  refine ⟨12, 8, by decide, ?_⟩
                  change 16777216*A < 43046721*B ∧ 7*(43046721*B) < 8*(16777216*A)
                  omega
                ·
                  by_cases h8 : 13*A < 37*B
                  ·
                    refine ⟨4, 3, by decide, ?_⟩
                    change 256*A < 729*B ∧ 7*(729*B) < 8*(256*A)
                    omega
                  ·
                    by_cases h9 : 5*A < 16*B
                    ·
                      refine ⟨15, 10, by decide, ?_⟩
                      change 1073741824*A < 3486784401*B ∧ 7*(3486784401*B) < 8*(1073741824*A)
                      omega
                    ·
                      by_cases h10 : 5*A < 18*B
                      ·
                        refine ⟨7, 5, by decide, ?_⟩
                        change 16384*A < 59049*B ∧ 7*(59049*B) < 8*(16384*A)
                        omega
                      ·
                        by_cases h11 : 1*A < 4*B
                        ·
                          refine ⟨18, 12, by decide, ?_⟩
                          change 68719476736*A < 282429536481*B ∧ 7*(282429536481*B) < 8*(68719476736*A)
                          omega
                        ·
                          by_cases h12 : 2*A < 9*B
                          ·
                            refine ⟨10, 7, by decide, ?_⟩
                            change 1048576*A < 4782969*B ∧ 7*(4782969*B) < 8*(1048576*A)
                            omega
                          ·
                            by_cases h13 : 17*A < 86*B
                            ·
                              refine ⟨2, 2, by decide, ?_⟩
                              change 16*A < 81*B ∧ 7*(81*B) < 8*(16*A)
                              omega
                            ·
                              by_cases h14 : 3*A < 17*B
                              ·
                                refine ⟨13, 9, by decide, ?_⟩
                                change 67108864*A < 387420489*B ∧ 7*(387420489*B) < 8*(67108864*A)
                                omega
                              ·
                                by_cases h15 : 5*A < 32*B
                                ·
                                  refine ⟨5, 4, by decide, ?_⟩
                                  change 1024*A < 6561*B ∧ 7*(6561*B) < 8*(1024*A)
                                  omega
                                ·
                                  by_cases h16 : 4*A < 29*B
                                  ·
                                    refine ⟨16, 11, by decide, ?_⟩
                                    change 4294967296*A < 31381059609*B ∧ 7*(31381059609*B) < 8*(4294967296*A)
                                    omega
                                  ·
                                    by_cases h17 : 1*A < 8*B
                                    ·
                                      refine ⟨8, 6, by decide, ?_⟩
                                      change 65536*A < 531441*B ∧ 7*(531441*B) < 8*(65536*A)
                                      omega
                                    ·
                                      refine ⟨0, 1, by decide, ?_⟩
                                      change 1*A < 9*B ∧ 7*(9*B) < 8*(1*A)
                                      omega

/-- Every positive integer lies in a unique nine-power envelope.
The proof uses strong induction and integer quotient/remainder, without
any real logarithms, density assumptions, or infinitary approximation. -/
theorem exists_nine_envelope :
    ∀ A : Nat, 0 < A →
      ∃ n : Nat, 9^n ≤ A ∧ A < 9^(n+1) := by
  intro A
  induction A using Nat.strongRecOn with
  | ind A ih =>
      intro hA
      by_cases hsmall : A < 9
      · refine ⟨0, ?_, ?_⟩
        · norm_num
          omega
        · norm_num
          omega
      · have hmod : A%9 < 9 := Nat.mod_lt A (by decide)
        have hdecomp : A%9 + 9*(A/9) = A := Nat.mod_add_div A 9
        have hdivpos : 0 < A/9 := by omega
        have hdivlt : A/9 < A :=
          Nat.div_lt_self (by omega) (by decide)
        obtain ⟨n, hnlo, hnhi⟩ := ih (A/9) hdivlt hdivpos
        have hpow : 9^(n+1) = 9*(9^n) := by rw [pow_succ]; ring
        have hpow2 : 9^((n+1)+1) = 9*(9^(n+1)) := by rw [pow_succ]; ring
        refine ⟨n+1, ?_, ?_⟩
        · omega
        · omega

/-- Scale-free Archimedean escape: multiplying ANY positive integer
by one of the first 19 powers of four produces a sharp no-22 escape.
This is the ingredient producing bounded gaps of actual hGate events. -/
theorem archimedean_escape_within_eighteen
    (A : Nat) (hA : 0 < A) :
    ∃ j m : Nat, j ≤ 18 ∧
      A*4^j < 9^m ∧ 7*(9^m-1) < 8*(A*4^j) := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_nine_envelope A hA
  have hnhi' : A < 9*(9^n) := by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hnhi
  obtain ⟨j,e,hj,hwin⟩ :=
    phase_cover_nineteen A (9^n) (by positivity) hnlo hnhi'
  unfold PhaseHit at hwin
  rcases hwin with ⟨hbelow, habove⟩
  refine ⟨j,n+e,hj,?_,?_⟩
  · simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hbelow
  · have hstrong : 7*(9^(n+e)) < 8*(A*4^j) := by
      simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using habove
    omega

/-- Unconditional global bounded gaps: EVERY interval of 19
consecutive exponents contains an original same-position CommonTwo.
This strictly strengthens the existence of infinitely many good
exponents, but does not assert the all-exponents hGate. -/
theorem commonTwo_within_eighteen (K : Nat) :
    ∃ j : Nat, j ≤ 18 ∧ CommonTwo (K+j) := by
  obtain ⟨j,m,hj,hl,hh⟩ :=
    archimedean_escape_within_eighteen (4^K) (by positivity)
  have hl' : 4^(K+j) < 9^m := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hl
  have hh' : 7*(9^m-1) < 8*4^(K+j) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hh
  exact ⟨j,hj,
    GSTProblem406ArchimedeanPhysicalEscape.CommonTwo_of_archimedean_escape
      (K+j) m hl' hh'⟩

/-- Stronger global digit-pattern theorem: within every run of
19 consecutive powers of four, at least one has a literal adjacent
ternary block 22. This is independent of the neighbor-power carry
machine; it follows by the sharp no-22 magnitude obstruction. -/
theorem adjacent22_within_eighteen (K : Nat) :
    ∃ j : Nat, j ≤ 18 ∧
      ∃ p : Nat,
        GSTFourPowerDirectResidue.digit3 (4^(K+j)) p = 2 ∧
        GSTFourPowerDirectResidue.digit3 (4^(K+j)) (p+1) = 2 := by
  obtain ⟨j,m,hj,hl,hh⟩ :=
    archimedean_escape_within_eighteen (4^K) (by positivity)
  refine ⟨j,hj,?_⟩
  by_contra hNo
  have hword :
      GSTFourPowerNo22Magnitude.No22Ternary (4^(K+j)) := by
    intro p hp
    apply hNo
    exact ⟨p,hp⟩
  have hl' : 4^(K+j) < 9^m := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hl
  have hh' : 7*(9^m-1) < 8*4^(K+j) := by
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hh
  have hbound :=
    GSTFourPowerNo22Magnitude.no22_nine_power_bound
      (4^(K+j)) m hl' hword
  omega

/-- Entirely base-independent multiplicative pattern birth:
for EVERY positive natural integer A, at least one of
A, 4A, 4^2 A, ..., 4^18 A has a literal ternary 22 block.
No perfect-power assumption is needed for this theorem. -/
theorem any_positive_orbit_adjacent22 (A : Nat) (hA : 0 < A) :
    ∃ j : Nat, j ≤ 18 ∧
      ∃ p : Nat,
        GSTFourPowerDirectResidue.digit3 (A*4^j) p = 2 ∧
        GSTFourPowerDirectResidue.digit3 (A*4^j) (p+1) = 2 := by
  obtain ⟨j,m,hj,hl,hh⟩ :=
    archimedean_escape_within_eighteen A hA
  refine ⟨j,hj,?_⟩
  by_contra hNo
  have hword :
      GSTFourPowerNo22Magnitude.No22Ternary (A*4^j) := by
    intro p hp
    exact hNo ⟨p,hp⟩
  have hbound :=
    GSTFourPowerNo22Magnitude.no22_nine_power_bound
      (A*4^j) m hl hword
  omega

/-- Stronger global physical source-neighbor statement:
for EVERY positive integer A congruent 1 modulo 3, some j <= 18
makes A*4^j and 4*A*4^j share a digit 2 at a POSITIVE ternary
row. This generalizes the powers-of-four bounded-gap gate. -/
theorem any_unit_orbit_commonTwo_within_eighteen
    (A : Nat) (hAmod : A%3=1) :
    ∃ j : Nat, j ≤ 18 ∧
      ∃ p : Nat, 1 ≤ p ∧
        GSTFourPowerDirectResidue.digit3 (A*4^j) p = 2 ∧
        GSTFourPowerDirectResidue.digit3 (4*(A*4^j)) p = 2 := by
  have hApos : 0 < A := by omega
  obtain ⟨j,hj,p,h2,h22⟩ :=
    any_positive_orbit_adjacent22 A hApos
  refine ⟨j,hj,?_⟩
  by_contra hNo
  have hmodpow : 4^j%3 = 1 := by
    simp [Nat.pow_mod]
  have hsource0 :
      GSTFourPowerDirectResidue.digit3 (A*4^j) 0 = 1 := by
    unfold GSTFourPowerDirectResidue.digit3
    simp only [pow_zero, Nat.div_one]
    calc
      (A*4^j)%3 = ((A%3)*(4^j%3))%3 := Nat.mul_mod _ _ _
      _ = 1 := by rw [hAmod,hmodpow]
  have hp : 1 ≤ p := by
    by_contra hpnot
    have hp0 : p=0 := by omega
    subst p
    omega
  have hforbidden :=
    GSTFourPowerDirectNo22.no_common_forbids_source_22
      (A*4^j) p hp hNo h2
  exact hforbidden h22

/-- The exact original production third-wave predicate also fires
within 18 exponent increments from every starting K. -/
theorem thirdWave_within_eighteen (K : Nat) :
    ∃ j : Nat, j ≤ 18 ∧
      GSTFourPowerThirdWave.thirdWave (K+j) := by
  obtain ⟨j,hj,h⟩ := commonTwo_within_eighteen K
  exact ⟨j,hj, (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2 h⟩

#print axioms phase_cover_nineteen
#print axioms exists_nine_envelope
#print axioms archimedean_escape_within_eighteen
#print axioms any_positive_orbit_adjacent22
#print axioms any_unit_orbit_commonTwo_within_eighteen
#print axioms adjacent22_within_eighteen
#print axioms commonTwo_within_eighteen
#print axioms thirdWave_within_eighteen

end GSTProblem406SyndeticArchimedeanGate
