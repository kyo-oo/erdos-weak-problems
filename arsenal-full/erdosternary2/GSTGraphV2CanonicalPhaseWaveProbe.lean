import GSTGraphV2CanonicalPhaseSteering

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalPhaseWaveProbe

open GSTCanonicalTailLTE
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTGraphV2CanonicalRenormalization
open GSTGraphV2CanonicalPhaseSteering
open GSTGraphV2SeededPrefix
open GSTV2

/-- Zero origin has zero canonical tail. -/
theorem canonicalTail_zero_exact (r : Nat) :
    canonicalTail r 0 = 0 := by
  have hden : 1 < 3^(r+1) := by
    rw [Nat.pow_succ]
    have hp : 0 < 3^r := by positivity
    nlinarith
  simp [canonicalTail, Nat.div_eq_of_lt hden]

/-- Adding one origin unit appends exactly one width-`3^r` horizontal block. -/
theorem canonicalTail_succ_exact (r n : Nat) :
    canonicalTail r (n+1) =
      canonicalTail r n +
        4^(n * 3^r) * canonicalTail r 1 := by
  have h := canonicalTail_power_block_recurrence r n 1 0
  simpa [Nat.pow_zero, Nat.add_comm, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

/-- From scale one onward every canonical horizontal block multiplier is one
modulo nine. -/
theorem pow4_canonical_multiple_mod9_one
    (r n : Nat) (hr : 1 ≤ r) :
    4^(n * 3^r) % 9 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show n * 3^(1+k) = 3 * (n * 3^k) by
    rw [pow_add]
    norm_num
    ring]
  rw [Nat.pow_mul]
  norm_num [Nat.pow_mod]

/-- At every scale `r≥1`, the canonical tail is exactly multiplication by
seven modulo nine.  This is the second ternary layer of the Graph-V2 phase
wave. -/
theorem canonicalTail_mod9_linear
    (r n : Nat) (hr : 1 ≤ r) :
    canonicalTail r n % 9 = (7*n) % 9 := by
  induction n with
  | zero =>
      simp [canonicalTail_zero_exact]
  | succ n ih =>
      rw [canonicalTail_succ_exact]
      have hpow := pow4_canonical_multiple_mod9_one r n hr
      have hc : canonicalTail r 1 % 9 = 7 := by
        rw [show canonicalTail r 1 = unitTail r by rfl,
          unitTail_eq_lteCoeff]
        exact lteCoeff_mod9_seven_of_one_le r hr
      rw [Nat.add_mod, Nat.mul_mod, hpow, hc, ih]
      rw [Nat.mul_succ, Nat.add_mod]
      omega

/-- From scale two onward the LTE coefficient is rigid modulo twenty-seven. -/
theorem lteCoeff_mod27_sixteen_of_two_le : ∀ r : Nat, 2 ≤ r →
    lteCoeff r % 27 = 16 := by
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero =>
      norm_num [lteCoeff]
  | succ k ih =>
      rw [show 2 + (k+1) = (2+k)+1 by omega, lteCoeff]
      have hterm1 :
          (3^((2+k)+1) * lteCoeff (2+k)^2) % 27 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        have h27 : 27 ∣ 3^((2+k)+1) := by
          use 3^k
          rw [show (2+k)+1 = k+3 by omega, pow_add]
          norm_num
          ring
        exact dvd_mul_of_dvd_left h27 _
      have hterm2 :
          (3^(2*(2+k)+1) * lteCoeff (2+k)^3) % 27 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        have h27 : 27 ∣ 3^(2*(2+k)+1) := by
          use 3^(2*k+2)
          rw [show 2*(2+k)+1 = (2*k+2)+3 by omega, pow_add]
          norm_num
          ring
        exact dvd_mul_of_dvd_left h27 _
      rw [Nat.add_mod]
      rw [hterm2, Nat.add_zero]
      rw [Nat.add_mod]
      rw [hterm1, ih]
      norm_num

/-- Hence the affine prefix offset itself is rigidly five modulo nine. -/
theorem prefixOffset_mod9_five
    (s : Nat) (hs : 2 ≤ s) :
    prefixOffset s % 9 = 5 := by
  have hc27 : unitTail s % 27 = 16 := by
    rw [unitTail_eq_lteCoeff]
    exact lteCoeff_mod27_sixteen_of_two_le s hs
  have hsplit := Nat.mod_add_div (unitTail s) 27
  rw [hc27] at hsplit
  have hunit : unitTail s = 16 + 27 * (unitTail s / 27) := by
    simpa [Nat.add_comm, Nat.mul_comm] using hsplit.symm
  rw [prefixOffset, hunit]
  have hdiv :
      (16 + 27 * (unitTail s / 27)) / 3 =
        5 + 9 * (unitTail s / 27) := by omega
  rw [hdiv]
  omega

/-- The complete seed-one canonical parent tail has an explicit mod-nine
phase. -/
theorem canonical_parent_tail_mod9
    (s n : Nat) (hs : 2 ≤ s) :
    (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) % 9 =
      (5 + 7*n) % 9 := by
  have hz := prefixOffset_mod9_five s hs
  have hA : 4^(3^s) % 9 = 1 := by
    simpa [Nat.mul_comm] using
      (pow4_canonical_multiple_mod9_one s 1 (by omega))
  have hT := canonicalTail_mod9_linear (s+1) n (by omega)
  rw [Nat.add_mod, Nat.mul_mod, hz, hA, hT]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The observed GST+ phase: origin residue three modulo nine forces a Happy
parent gate one row above the canonical cut. -/
theorem canonical_parent_mod9_three_happy
    (s n : Nat) (hs : 2 ≤ s) (hn : n % 9 = 3) :
    SeedHappy 1 1
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) 1 := by
  let X := prefixOffset s + 4^(3^s) * canonicalTail (s+1) n
  have hX : X % 9 = 8 := by
    dsimp [X]
    rw [canonical_parent_tail_mod9 s n hs]
    omega
  have hx3 : X % 3 = 2 := by omega
  have hxd : (X / 3) % 3 = 2 := by omega
  unfold SeedHappy seededCarry seededResidue seededDigit
  change GSTU2DEventTransport.HappyCell (4 * (1 + 3 * (X % 3)) / 9) ((X / 3) % 3)
  rw [hx3, hxd]
  norm_num [GSTU2DEventTransport.HappyCell]

/-- The observed NULL phase: origin residue four modulo nine forces the other
Happy chord one row above the canonical cut. -/
theorem canonical_parent_mod9_four_happy
    (s n : Nat) (hs : 2 ≤ s) (hn : n % 9 = 4) :
    SeedHappy 1 1
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) 1 := by
  let X := prefixOffset s + 4^(3^s) * canonicalTail (s+1) n
  have hX : X % 9 = 6 := by
    dsimp [X]
    rw [canonical_parent_tail_mod9 s n hs]
    omega
  have hx3 : X % 3 = 0 := by omega
  have hxd : (X / 3) % 3 = 2 := by omega
  unfold SeedHappy seededCarry seededResidue seededDigit
  change GSTU2DEventTransport.HappyCell (4 * (1 + 3 * (X % 3)) / 9) ((X / 3) % 3)
  rw [hx3, hxd]
  norm_num [GSTU2DEventTransport.HappyCell]

/-- All-depth parent badness therefore excludes both second-layer Happy wave
phases. -/
theorem canonical_parent_bad_forbids_mod9_three_four
    (s n : Nat) (hs : 2 ≤ s)
    (hBad : ∀ j : Nat, ¬ SeedHappy 1 1
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) j) :
    n % 9 ≠ 3 ∧ n % 9 ≠ 4 := by
  constructor
  · intro h3
    exact hBad 1 (canonical_parent_mod9_three_happy s n hs h3)
  · intro h4
    exact hBad 1 (canonical_parent_mod9_four_happy s n hs h4)

#check canonicalTail_mod9_linear
#check prefixOffset_mod9_five
#check canonical_parent_tail_mod9
#check canonical_parent_mod9_three_happy
#check canonical_parent_mod9_four_happy
#check canonical_parent_bad_forbids_mod9_three_four
#print axioms canonical_parent_bad_forbids_mod9_three_four

end GSTGraphV2CanonicalPhaseWaveProbe
