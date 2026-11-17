import GSTGraphV2HandwrittenExponentialCascade

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2HandwrittenExponentialLTE

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialCascade

/-!
# Exact LTE boundary of the handwritten exponential cascade

The repeated U split separates a consumed ternary origin prefix from a
higher-level perfect-power tail.  This file proves the missing local boundary
fact about that tail itself: at its defining ternary cut it is the neutral
NULL/zero-information vertex.  The consumed prefix is therefore the *only*
source of the physical state seen after the horizontal U phase translation.
-/

/-- Exact LTE quotient in
`4^(3^r) = 1 + 3^(r+1) * lteCoeff r`. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- Exact power-of-four LTE identity at every ternary scale. -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
  | 0 => by norm_num [lteCoeff]
  | r+1 => by
      have ih := pow4_three_power_lte_exact r
      calc
        4^(3^(r+1)) = (4^(3^r))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        _ = (1 + 3^(r+1) * lteCoeff r)^3 := by rw [ih]
        _ = 1 + 3^((r+1)+1) * lteCoeff (r+1) := by
          simp only [lteCoeff]
          rw [show (r+1)+1 = r+2 by omega]
          have h1 : 3^(r+1) = 3^r * 3 := by
            rw [Nat.pow_succ]
          have h2 : 3^(2*r+1) = (3^r)^2 * 3 := by
            calc
              3^(2*r+1) = 3^((r+r)+1) := by congr 1 <;> omega
              _ = 3^(r+r) * 3 := by rw [Nat.pow_succ]
              _ = (3^r * 3^r) * 3 := by rw [Nat.pow_add]
              _ = (3^r)^2 * 3 := by ring
          have h3 : 3^(r+2) = 3^r * 9 := by
            calc
              3^(r+2) = 3^((r+1)+1) := by congr 1 <;> omega
              _ = 3^(r+1) * 3 := by rw [Nat.pow_succ]
              _ = 3^r * 9 := by rw [h1]; ring
          rw [h3, h1, h2]
          ring

/-- The exact LTE quotient is always one modulo three. -/
theorem lteCoeff_mod3_one : ∀ r : Nat, lteCoeff r % 3 = 1
  | 0 => by decide
  | r+1 => by
      have ih := lteCoeff_mod3_one r
      simp only [lteCoeff]
      have hpow1 : 3^(r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      have hpow2 : 3^(2*r+1) % 3 = 0 := by
        rw [Nat.pow_succ]
        simp
      simp [Nat.add_mod, Nat.mul_mod, hpow1, hpow2, ih]

/-- Any multiple of the scale exponent is one modulo the next ternary cut. -/
theorem pow4_scaled_mod_next (r u : Nat) :
    4^(3^r * u) % 3^(r+1) = 1 := by
  have hA := pow4_three_power_lte_exact r
  rw [Nat.pow_mul, hA, Nat.pow_mod]
  have hMgt1 : 1 < 3^(r+1) := by
    have h3 : 3^1 ≤ 3^(r+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h3 ⊢
  have hbase : (1 + 3^(r+1) * lteCoeff r) % 3^(r+1) = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hMgt1]
  simpa [hbase, Nat.mod_eq_of_lt hMgt1]

/-- The same scaled power is one modulo the current cut once the cut is
positive. -/
theorem pow4_scaled_mod_current (r u : Nat) (hr : 1 ≤ r) :
    4^(3^r * u) % 3^r = 1 := by
  let R := 4^(3^r * u)
  have hnext : R % 3^(r+1) = 1 := by
    dsimp [R]
    exact pow4_scaled_mod_next r u
  have hdvd : 3^r ∣ 3^(r+1) := Nat.pow_dvd_pow 3 (by omega)
  have hmod := Nat.mod_mod_of_dvd R hdvd
  have hpow : 1 < 3^r := by
    have h3 : 3^1 ≤ 3^r :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hr
    norm_num at h3 ⊢
    omega
  rw [hnext, Nat.mod_eq_of_lt hpow] at hmod
  exact hmod.symm

/-- At scale at least two, the remaining higher-level perfect-power tail has
zero incoming x4 carry at its own cut. -/
theorem pow4_scaled_cut_carry_zero
    (r u : Nat) (hr : 2 ≤ r) :
    carry4 (4^(3^r * u)) r = 0 := by
  have hmod := pow4_scaled_mod_current r u (by omega)
  unfold carry4
  rw [hmod]
  have h9 : 9 ≤ 3^r := by
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) hr
  exact Nat.div_eq_of_lt (by omega)

/-- At the same cut the remaining higher-level tail exposes information digit
zero. -/
theorem pow4_scaled_cut_digit_zero
    (r u : Nat) (hr : 2 ≤ r) :
    digit3 (4^(3^r * u)) r = 0 := by
  let R := 4^(3^r * u)
  have hnext : R % 3^(r+1) = 1 := by
    dsimp [R]
    exact pow4_scaled_mod_next r u
  have hcur : R % 3^r = 1 := by
    dsimp [R]
    exact pow4_scaled_mod_current r u (by omega)
  have hsplit :
      R % (3^r * 3) = R % 3^r + 3^r * (R / 3^r % 3) := by
    rw [Nat.mod_mul]
  rw [← Nat.pow_succ, hnext, hcur] at hsplit
  have hp : 0 < 3^r := Nat.pow_pos (by decide)
  have hprod : 3^r * (R / 3^r % 3) = 0 := by
    omega
  have hd : R / 3^r % 3 = 0 := by
    rcases Nat.mul_eq_zero.mp hprod with hp0 | hd0
    · exact False.elim ((Nat.ne_of_gt hp) hp0)
    · exact hd0
  unfold digit3
  exact hd

/-- **Full Graph-V2 U-cut boundary.**  Before the accumulated origin prefix is
reapplied as a horizontal phase, the unconsumed U tail occupies NULL with
zero ternary information at the exact cut `t+K`. -/
theorem uTailEnergy_cut_neutral
    (t n K : Nat) (hcut : 2 ≤ t+K) :
    (graph (uTailEnergy t n K) 0 (t+K)).seven.carry = 0 ∧
    (graph (uTailEnergy t n K) 0 (t+K)).seven.digit = 0 ∧
    (graph (uTailEnergy t n K) 0 (t+K)).seven.space = .null := by
  have hc := pow4_scaled_cut_carry_zero
    (t+K) (originSuffix n K) hcut
  have hd := pow4_scaled_cut_digit_zero
    (t+K) (originSuffix n K) hcut
  have hE : uTailEnergy t n K = 4^(3^(t+K) * originSuffix n K) := rfl
  constructor
  · simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hE] using hc
  constructor
  · simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hE] using hd
  · simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
      GSTCanonicalSevenAxisBridge.spaceOfCarry, hE, hc]

/-- At the production child row `s+2+q`, choosing U depth `q+1` is exact: the
unconsumed child origin is neutral there before the consumed-prefix phase is
applied. -/
theorem canonical_child_u_cut_neutral
    (s n q : Nat) (hs : 1 ≤ s) :
    (graph (uTailEnergy (s+1) n (q+1)) 0 (s+2+q)).seven.carry = 0 ∧
    (graph (uTailEnergy (s+1) n (q+1)) 0 (s+2+q)).seven.digit = 0 ∧
    (graph (uTailEnergy (s+1) n (q+1)) 0 (s+2+q)).seven.space = .null := by
  have hcut : 2 ≤ (s+1) + (q+1) := by omega
  have h := uTailEnergy_cut_neutral (s+1) n (q+1) hcut
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

#check pow4_three_power_lte_exact
#check lteCoeff_mod3_one
#check pow4_scaled_mod_next
#check pow4_scaled_cut_carry_zero
#check pow4_scaled_cut_digit_zero
#check uTailEnergy_cut_neutral
#check canonical_child_u_cut_neutral
#print axioms pow4_three_power_lte_exact
#print axioms uTailEnergy_cut_neutral

end GSTGraphV2HandwrittenExponentialLTE
