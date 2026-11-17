import GSTFinalPurePowerResidueTransplant
import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTCanonicalBoundaryRigidity

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2HandwrittenExponentialLTE
open GSTFinalPurePowerResidueTransplant

/-- Reducing the right factor before a multiplication does not change the
resulting residue. -/
theorem mul_mod_reduce_right (a b M : Nat) :
    (a * b) % M = (a * (b % M)) % M := by
  calc
    (a * b) % M = ((a % M) * (b % M)) % M := Nat.mul_mod a b M
    _ = (a * (b % M)) % M := by
      simpa using (Nat.mul_mod a (b % M) M).symm

/-- The reverse-base-four graph carry word is not an abstract state: it is
exactly the quotient obtained by multiplying the initial row residue by `4^N`.
This identity is valid at every start column and every ternary cut. -/
theorem carryWord_eq_stripQuotient
    (E p start N : Nat) :
    carryWord E p start N =
      stripQuotient ((4^start * E) % 3^p) (3^p) N := by
  induction N with
  | zero =>
      simp [carryWord, stripQuotient]
  | succ N ih =>
      rw [carryWord, ih]
      rw [stripQuotient_succ _ _ N (Nat.pow_pos (by decide))]
      congr 1
      change
        (4 * ((4^(start+N) * E) % 3^p)) / 3^p =
          (4 * ((4^N * ((4^start * E) % 3^p)) % 3^p)) / 3^p
      have hres :
          (4^(start+N) * E) % 3^p =
            (4^N * ((4^start * E) % 3^p)) % 3^p := by
        calc
          (4^(start+N) * E) % 3^p =
              (4^N * (4^start * E)) % 3^p := by
                congr 1
                rw [Nat.pow_add]
                ring
          _ = (4^N * ((4^start * E) % 3^p)) % 3^p :=
            mul_mod_reduce_right (4^N) (4^start * E) (3^p)
      rw [hres]

/-- The V2/LTE coefficient has the canonical prefix-one decomposition. -/
def canonicalPrefixOffsetV2 (s : Nat) : Nat := lteCoeff s / 3

theorem lteCoeff_prefix_one_exact (s : Nat) :
    lteCoeff s = 1 + 3 * canonicalPrefixOffsetV2 s := by
  have hmod := lteCoeff_mod3_one s
  have hdiv := Nat.mod_add_div (lteCoeff s) 3
  unfold canonicalPrefixOffsetV2
  omega

/-- Exact canonical block decomposition at the next ternary cut. -/
theorem canonical_block_prefix_exact (s : Nat) :
    4^(3^s) =
      1 + 3^(s+1) + 3^(s+2) * canonicalPrefixOffsetV2 s := by
  have hLTE := pow4_three_power_lte_exact s
  have hc := lteCoeff_prefix_one_exact s
  have hpow : 3^(s+2) = 3^(s+1) * 3 := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  rw [hLTE, hc, hpow]
  ring

/-- The forced low part of one canonical block is strictly below the next
ternary cut. -/
theorem canonical_low_block_lt_cut (s : Nat) :
    1 + 3^(s+1) < 3^(s+2) := by
  have hpow : 3^(s+2) = 3^(s+1) * 3 := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  have h1 : 1 ≤ 3^(s+1) := Nat.one_le_pow _ _ (by decide)
  rw [hpow]
  omega

/-- For `s>=1`, multiplying the forced low block by four crosses the next
ternary cut exactly once. -/
theorem canonical_four_low_block_div_cut
    (s : Nat) (hs : 1 ≤ s) :
    (4 * (1 + 3^(s+1))) / 3^(s+2) = 1 := by
  let B := 3^(s+1)
  have hpow : 3^(s+2) = B * 3 := by
    dsimp [B]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  have hB9 : 9 ≤ B := by
    dsimp [B]
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hM : 0 < B * 3 := by positivity
  have hrem : B + 4 < B * 3 := by omega
  rw [hpow]
  change (4 * (1 + B)) / (B * 3) = 1
  rw [show 4 * (1 + B) = (B + 4) + (B * 3) * 1 by ring]
  rw [Nat.add_mul_div_left _ _ hM]
  rw [Nat.div_eq_of_lt hrem]

/-- Every canonical full energy is literally one modulo the production cut
`3^(s+2)`. -/
theorem canonicalEnergy_mod_production_cut (s n : Nat) :
    canonicalEnergy s n % 3^(s+2) = 1 := by
  simpa [canonicalEnergy, show (s+1)+1 = s+2 by omega] using
    pow4_scaled_mod_next (s+1) n

/-- One canonical horizontal block therefore has the fixed residue
`1 + 3^(s+1)` at the same production cut, independently of `n`. -/
theorem canonical_right_residue_exact
    (s n : Nat) :
    (4^(canonicalWidth s) * canonicalEnergy s n) % 3^(s+2) =
      1 + 3^(s+1) := by
  have hE := canonicalEnergy_mod_production_cut s n
  have hA := canonical_block_prefix_exact s
  have hsmall := canonical_low_block_lt_cut s
  calc
    (4^(canonicalWidth s) * canonicalEnergy s n) % 3^(s+2) =
        (4^(canonicalWidth s) *
          (canonicalEnergy s n % 3^(s+2))) % 3^(s+2) :=
      mul_mod_reduce_right (4^(canonicalWidth s))
        (canonicalEnergy s n) (3^(s+2))
    _ = 4^(3^s) % 3^(s+2) := by
      rw [hE]
      simp [canonicalWidth]
    _ = (1 + 3^(s+1) +
          3^(s+2) * canonicalPrefixOffsetV2 s) % 3^(s+2) := by
      rw [hA]
    _ = (1 + 3^(s+1)) % 3^(s+2) := by
      rw [Nat.add_mod]
      have hz :
          (3^(s+2) * canonicalPrefixOffsetV2 s) % 3^(s+2) = 0 :=
        Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
      rw [hz, Nat.add_zero, Nat.mod_mod]
    _ = 1 + 3^(s+1) := Nat.mod_eq_of_lt hsmall

/-- Left endpoint carry at the canonical production cut is forced to NULL. -/
theorem canonical_left_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) 0 (s+2)).seven.carry = 0 := by
  have hc : carry4 (canonicalEnergy s n) (s+2) = 0 := by
    unfold carry4
    rw [canonicalEnergy_mod_production_cut]
    apply Nat.div_eq_of_lt
    have h27 : 27 ≤ 3^(s+2) := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  simpa [GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
    GSTCanonicalSevenAxisBridge.vertex] using hc

/-- Right endpoint carry one canonical block later is forced to seed one. -/
theorem canonical_right_carry_one
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+2)).seven.carry = 1 := by
  have hc : carry4
      (4^(canonicalWidth s) * canonicalEnergy s n) (s+2) = 1 := by
    unfold carry4
    rw [canonical_right_residue_exact]
    exact canonical_four_low_block_div_cut s hs
  simpa [GSTGraphV2InfiniteControl.graph, GSTGraphV2InfiniteControl.cell,
    GSTCanonicalSevenAxisBridge.vertex] using hc

/-- The parent offset at the canonical cut is exactly the LTE prefix offset. -/
theorem canonical_parent_offset_exact
    (s n : Nat) :
    carryWord (canonicalEnergy s n) (s+2) 0 (canonicalWidth s) =
      canonicalPrefixOffsetV2 s := by
  rw [carryWord_eq_stripQuotient]
  unfold stripQuotient
  simp only [Nat.pow_zero, Nat.one_mul]
  rw [canonicalEnergy_mod_production_cut]
  simp only [Nat.mul_one, canonicalWidth]
  rw [canonical_block_prefix_exact]
  have hM : 0 < 3^(s+2) := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hM]
  rw [Nat.div_eq_of_lt (canonical_low_block_lt_cut s)]
  simp

/-- The retained high/child residue is also fixed: `1 + 4*z`. -/
theorem canonical_child_residue_exact
    (s n : Nat) (hs : 1 ≤ s) :
    carryWord (canonicalEnergy s n) (s+2) 1 (canonicalWidth s) =
      1 + 4 * canonicalPrefixOffsetV2 s := by
  rw [carryWord_eq_stripQuotient]
  unfold stripQuotient
  have h4lt : 4 < 3^(s+2) := by
    have h27 : 27 ≤ 3^(s+2) := by
      rw [show (27 : Nat) = 3^3 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hstart :
      (4^1 * canonicalEnergy s n) % 3^(s+2) = 4 := by
    norm_num only [Nat.pow_one]
    calc
      (4 * canonicalEnergy s n) % 3^(s+2) =
          (4 * (canonicalEnergy s n % 3^(s+2))) % 3^(s+2) :=
        mul_mod_reduce_right 4 (canonicalEnergy s n) (3^(s+2))
      _ = 4 % 3^(s+2) := by
        rw [canonicalEnergy_mod_production_cut]
      _ = 4 := Nat.mod_eq_of_lt h4lt
  rw [hstart]
  simp only [canonicalWidth]
  rw [canonical_block_prefix_exact]
  have hM : 0 < 3^(s+2) := Nat.pow_pos (by decide)
  have hshape :
      (1 + 3^(s+1) + 3^(s+2) * canonicalPrefixOffsetV2 s) * 4 =
        4 * (1 + 3^(s+1)) +
          3^(s+2) * (4 * canonicalPrefixOffsetV2 s) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ hM]
  rw [canonical_four_low_block_div_cut s hs]

/-- **Canonical boundary rigidity.**  At the production cut the entire finite
horizontal boundary packet is forced by `s`; `n` survives only in the child
tail above the cut. -/
theorem canonical_boundary_packet_exact
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+2)).seven.carry = 1 ∧
    carryWord (canonicalEnergy s n) (s+2) 0 (canonicalWidth s) =
      canonicalPrefixOffsetV2 s ∧
    carryWord (canonicalEnergy s n) (s+2) 1 (canonicalWidth s) =
      1 + 4 * canonicalPrefixOffsetV2 s ∧
    (graph (canonicalEnergy s n) 0 (s+2)).seven.carry = 0 := by
  exact ⟨canonical_right_carry_one s n hs,
    canonical_parent_offset_exact s n,
    canonical_child_residue_exact s n hs,
    canonical_left_carry_zero s n hs⟩

#check carryWord_eq_stripQuotient
#check canonical_block_prefix_exact
#check canonical_boundary_packet_exact
#print axioms carryWord_eq_stripQuotient
#print axioms canonical_boundary_packet_exact

end GSTCanonicalBoundaryRigidity
