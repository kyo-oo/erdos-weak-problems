import GSTPrefixOneOntologicalEscape
import GSTSeedOneShift
import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneSeedCore

open GSTCanonicalTailStateIso
open GSTPerfectPowerTailNavigation
open GSTFourPowerOntologicalAdapter
open GSTPrefixOneOntologicalEscape
open GSTSeedOneShift
open GSTCanonicalTailLTE

/-- The unit canonical tail `c_s = Q_s(1)`. -/
def unitTail (s : Nat) : Nat := canonicalTail s 1

/-- The forced residual prefix `z_s`, so eventually `c_s = 1 + 3 z_s`. -/
def prefixOffset (s : Nat) : Nat := unitTail s / 3

/-- The standalone canonical quotient agrees with the exact recursive LTE coefficient. -/
theorem unitTail_eq_lteCoeff (s : Nat) : unitTail s = lteCoeff s := by
  have hQ : 4^(3^s) = 1 + 3^(s+1) * unitTail s := by
    simpa [unitTail] using (canonical_tail_decomposition s 1)
  have hLTE : 4^(3^s) = 1 + 3^(s+1) * lteCoeff s :=
    pow4_three_power_lte_exact s
  have hEq : 1 + 3^(s+1) * unitTail s =
      1 + 3^(s+1) * lteCoeff s := hQ.symm.trans hLTE
  have hM : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  nlinarith

/-- The unit tail is exactly one modulo three. -/
theorem unitTail_mod3_one (s : Nat) : unitTail s % 3 = 1 := by
  rw [unitTail_eq_lteCoeff, lteCoeff_mod3_one]

/-- Exact forced unit prefix `c_s = 1 + 3 z_s`. -/
theorem unitTail_prefix_one (s : Nat) :
    unitTail s = 1 + 3 * prefixOffset s := by
  have h := Nat.mod_add_div (unitTail s) 3
  rw [unitTail_mod3_one s] at h
  simpa [prefixOffset, Nat.add_comm] using h.symm

/-- Exact canonical prefix recurrence `Q_s(1+3n) = c_s + 3 A_s Q_{s+1}(n)`. -/
theorem canonical_prefix_recurrence
    (s n : Nat) :
    canonicalTail s (1 + 3*n) =
      unitTail s + 3 * 4^(3^s) * canonicalTail (s+1) n := by
  let M : Nat := 3^(s+1)
  let A : Nat := 4^(3^s)
  let T : Nat := canonicalTail (s+1) n
  let P : Nat := canonicalTail s (1 + 3*n)
  let c : Nat := unitTail s

  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hMgt1 : 1 < M := by
    dsimp [M]
    have h3 : 3 ≤ 3^(s+1) := by
      simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (show 1 ≤ s+1 by omega))
    omega
  have hA : A = 1 + M*c := by
    dsimp [A, M, c, unitTail]
    simpa using (canonical_tail_decomposition s 1)
  have hMnext : 3^(s+2) = 3*M := by
    dsimp [M]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hE : 4^(3^(s+1) * n) = 1 + 3*M*T := by
    dsimp [T]
    have h := canonical_tail_decomposition (s+1) n
    rw [show (s+1)+1 = s+2 by omega, hMnext] at h
    simpa [Nat.mul_assoc] using h
  have hExp :
      3^s * (1 + 3*n) = 3^s + 3^(s+1) * n := by
    rw [Nat.pow_succ]
    ring
  have hProduct :
      4^(3^s * (1 + 3*n)) = A * 4^(3^(s+1) * n) := by
    rw [hExp, Nat.pow_add]
  have hShape :
      4^(3^s * (1 + 3*n)) =
        1 + M * (c + 3*A*T) := by
    rw [hProduct, hE, hA]
    ring
  have hParent :
      4^(3^s * (1 + 3*n)) = 1 + M*P := by
    dsimp [M, P]
    exact canonical_tail_decomposition s (1 + 3*n)
  have hEq : 1 + M*P = 1 + M*(c + 3*A*T) :=
    hParent.symm.trans hShape
  have hEqDiv := congrArg (fun x : Nat => x / M) hEq
  rw [Nat.add_mul_div_left _ _ hMpos,
      Nat.div_eq_of_lt hMgt1, Nat.zero_add,
      Nat.add_mul_div_left _ _ hMpos,
      Nat.div_eq_of_lt hMgt1, Nat.zero_add] at hEqDiv
  simpa [P, c, A, T] using hEqDiv

/-- Formula (9): the prefix-one canonical parent is literally `1 + 3 X`. -/
theorem prefix_one_tail_shape
    (s n : Nat) :
    canonicalTail s (1 + 3*n) =
      1 + 3 * (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) := by
  rw [canonical_prefix_recurrence s n, unitTail_prefix_one s]
  ring

/-- Strengthened seed core: no child witness is required once the independent
four-power creation master is supplied. -/
theorem gst_prefix_one_seed_one_parent_of_master
    (hMaster : FourPowerCreationMaster)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    SeedOneWitness
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) := by
  have hNav := gst_prefix_one_ontological_escape_of_master hMaster s n hs hn
  rw [prefix_one_tail_shape s n] at hNav
  exact (navigation_prefixed_one_iff_seed_one
    (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n)).1 hNav

end GSTPrefixOneSeedCore
