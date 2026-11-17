import GSTFourPowerDirectExistence
import GSTFourPowerDirectAdditionCarry
import GSTCanonicalTailStateIso
import GSTFourPowerAffineTwoTritClassifier

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectHappyBridge

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry

/-- A direct common-two witness is already a physical Happy row on the source
power.  No navigation or witness transport is involved: the same row is used.
If the source and its x4 target both have ternary digit two, the exact target
formula forces the source carry to be congruent to zero mod three; since that
carry is below four, it is literally zero or three. -/
theorem commonTwo_to_physical_happy_row
    (K : Nat) (h : CommonTwo K) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) q)
        (GSTCanonicalTailStateIso.digit3 (4^K) q) := by
  rcases h with ⟨q, hq, hs, ht⟩
  refine ⟨q, hq, ?_⟩
  unfold GSTCanonicalTailStateIso.HappyCell
  constructor
  · simpa [GSTCanonicalTailStateIso.digit3,
      GSTFourPowerDirectResidue.digit3] using hs
  · have ht4 : digit3 (4 * (4^K)) q = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
    have hformula := digit3_four_mul (4^K) q
    have hs' : digit3 (4^K) q = 2 := hs
    rw [hs', ht4] at hformula
    have hcarry : directCarry4 (4^K) q = 0 ∨ directCarry4 (4^K) q = 3 := by
      have hlt := directCarry4_lt_four (4^K) q
      omega
    simpa [GSTCanonicalTailStateIso.carry4, directCarry4] using hcarry

/-- Fresh affine branch `0,2`: the finite-state kill theorem constructs a
`CommonTwo (3*u)` witness, and the same physical row is therefore Happy on
`4^(3*u)`.  This is an actual row `q ≥ 1`, not a residue-only surrogate. -/
theorem affine_zero_two_to_physical_happy
    (u : Nat) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u)) q) := by
  exact commonTwo_to_physical_happy_row (3*u)
    (GSTFourPowerAffineTwoTritClassifier.commonTwo_three_mul_of_q_mod_three_two u hu)

/-- Fresh affine branch `2,1`: the twisted finite-state kill theorem constructs
`CommonTwo (3*u+2)`, hence a real physical Happy row on `4^(3*u+2)`. -/
theorem affine_two_one_to_physical_happy
    (u : Nat) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u+2)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u+2)) q) := by
  exact commonTwo_to_physical_happy_row (3*u+2)
    (GSTFourPowerAffineTwoTritClassifier.commonTwo_three_mul_add_two_of_q_mod_three_one u hu)

/-- Relocation-shaped version of the affine `0,2` kill branch.  When the next
exponent is exactly `3*u` with `u mod 3 = 2`, a genuine Happy row is constructed
on the `4^(K+1)` sheet. -/
theorem affine_zero_two_forces_relocated_physical_happy
    (K u : Nat) (hExp : K+1 = 3*u) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hExp]
  exact affine_zero_two_to_physical_happy u hu

/-- Relocation-shaped version of the affine `2,1` kill branch.  When the next
exponent is exactly `3*u+2` with `u mod 3 = 1`, a genuine Happy row is
constructed on the `4^(K+1)` sheet. -/
theorem affine_two_one_forces_relocated_physical_happy
    (K u : Nat) (hExp : K+1 = 3*u+2) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hExp]
  exact affine_two_one_to_physical_happy u hu

/-- Once the direct arithmetic existence theorem is proved, the actual Task-3
physical target follows immediately at a row `q ≥ 1`.  This theorem contains
no navigation, propagation edge, relocation surrogate, or quarantined route. -/
theorem directExistence_to_physical_happy_forcing
    (hDirect : FourPowerDirectExistence) :
    ∀ K : Nat, 5 ≤ K → K ≠ 7 →
      ∃ q : Nat, 1 ≤ q ∧
        GSTCanonicalTailStateIso.HappyCell
          (GSTCanonicalTailStateIso.carry4 (4^K) q)
          (GSTCanonicalTailStateIso.digit3 (4^K) q) := by
  intro K hK h7
  exact commonTwo_to_physical_happy_row K (hDirect K hK h7)

/-- Fresh-production relocation reduction.  In the actual Task-3 induction
range `K ≥ 8`, a relocated physical Happy row on the `4^(K+1)` sheet follows
straight from direct arithmetic existence at exponent `K+1`.  The source row
and even the source Happy hypothesis are therefore logically unnecessary once
`FourPowerDirectExistence` is available.  This removes the need to propagate a
latent packet or transport a witness through any navigation machinery. -/
theorem directExistence_forces_relocated_physical_happy
    (hDirect : FourPowerDirectExistence) :
    ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) →
      ∃ q : Nat, 1 ≤ q ∧
        GSTCanonicalTailStateIso.HappyCell
          (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
          (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  intro K p hK hp hSource
  exact directExistence_to_physical_happy_forcing hDirect (K+1) (by omega) (by omega)

/-- Exact Task 3.3 fresh-production relocation theorem.  The source physical
Happy row has the production signature, and the conclusion constructs a real
physical Happy row `q ≥ 1` on the next four-power sheet.  Its proof is purely
through direct consecutive-four-power arithmetic: no graph navigation,
relocation surrogate, packet transport, or quarantined route is imported. -/
theorem four_power_happy_propagates
    (hDirect : FourPowerDirectExistence)
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact directExistence_forces_relocated_physical_happy hDirect K p hK hp hHappy

#check commonTwo_to_physical_happy_row
#check affine_zero_two_to_physical_happy
#check affine_two_one_to_physical_happy
#check affine_zero_two_forces_relocated_physical_happy
#check affine_two_one_forces_relocated_physical_happy
#check directExistence_to_physical_happy_forcing
#check directExistence_forces_relocated_physical_happy
#check four_power_happy_propagates
#print axioms commonTwo_to_physical_happy_row
#print axioms affine_zero_two_to_physical_happy
#print axioms affine_two_one_to_physical_happy
#print axioms affine_zero_two_forces_relocated_physical_happy
#print axioms affine_two_one_forces_relocated_physical_happy
#print axioms directExistence_to_physical_happy_forcing
#print axioms directExistence_forces_relocated_physical_happy
#print axioms four_power_happy_propagates

end GSTFourPowerDirectHappyBridge
