import GSTCanonicalTailStateIso

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTSeedOneShift

open GSTCanonicalTailStateIso

/-- Seed-one affine x4 carry on a stripped ternary tail. -/
def seedOneCarry (X j : Nat) : Nat :=
  (1 + 4 * (X % 3^j)) / 3^j

/-- Seed-one Happy witness on the stripped tail. -/
def SeedOneWitness (X : Nat) : Prop :=
  ∃ j : Nat, digit3 X j = 2 ∧
    (seedOneCarry X j = 0 ∨ seedOneCarry X j = 3)

/-- Exact digit stripping through the forced leading ternary digit one. -/
theorem prefixed_one_digit_shift (X j : Nat) :
    digit3 (1 + 3*X) (j+1) = digit3 X j := by
  simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (prefix_slice_digit_exact 1 1 X j (by decide : 1 < 3^1))

/-- Exact residue identity behind the seed-one carry shift. -/
theorem prefixed_one_deep_mod (X j : Nat) :
    (1 + 3*X) % 3^(j+1) = 1 + 3 * (X % 3^j) := by
  have hpow : 3^(j+1) = 3 * 3^j := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow, Nat.mod_mul]
  have hmod3 : (1 + 3*X) % 3 = 1 := by simp
  have hdiv3 : (1 + 3*X) / 3 = X := by
    have h3 : 0 < (3:Nat) := by decide
    rw [Nat.add_mul_div_left _ _ h3, Nat.div_eq_of_lt (by decide : 1 < 3), Nat.zero_add]
  rw [hmod3, hdiv3]

/-- Exact carry stripping.  The ordinary carry of `1+3X` becomes seed-one carry on `X`. -/
theorem prefixed_one_carry_shift (X j : Nat) :
    carry4 (1 + 3*X) (j+1) = seedOneCarry X j := by
  unfold carry4 seedOneCarry
  rw [prefixed_one_deep_mod]
  have hpow : 3^(j+1) = 3 * 3^j := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow, ← Nat.div_div_eq_div_mul]
  have hshape :
      4 * (1 + 3 * (X % 3^j)) =
        1 + 3 * (1 + 4 * (X % 3^j)) := by ring
  rw [hshape]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3, Nat.div_eq_of_lt (by decide : 1 < 3), Nat.zero_add]

/-- Position zero of `1+3X` is forced digit one and is never Happy. -/
theorem prefixed_one_not_happy_zero (X : Nat) :
    ¬ HappyCell (carry4 (1 + 3*X) 0) (digit3 (1 + 3*X) 0) := by
  intro h
  have hd := h.1
  simp [digit3, Nat.add_mod, Nat.mul_mod] at hd

/-- SEED: ordinary Navigation of `1+3X` is exactly seed-one Navigation of `X`. -/
theorem navigation_prefixed_one_iff_seed_one (X : Nat) :
    Navigation (1 + 3*X) ↔ SeedOneWitness X := by
  constructor
  · intro hNav
    obtain ⟨p, hHappy⟩ := hNav
    have hp : 1 ≤ p := by
      by_contra hnot
      have hp0 : p = 0 := by omega
      subst p
      exact prefixed_one_not_happy_zero X hHappy
    let j := p - 1
    have hpEq : p = j+1 := by
      dsimp [j]
      omega
    refine ⟨j, ?_⟩
    rw [hpEq] at hHappy
    constructor
    · simpa [prefixed_one_digit_shift] using hHappy.1
    · simpa [prefixed_one_carry_shift] using hHappy.2
  · intro hSeed
    obtain ⟨j, hd, hC⟩ := hSeed
    refine ⟨j+1, ?_⟩
    constructor
    · rw [prefixed_one_digit_shift]
      exact hd
    · rw [prefixed_one_carry_shift]
      exact hC

end GSTSeedOneShift
