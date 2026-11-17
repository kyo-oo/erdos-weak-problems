import GSTWorldtraceBlockLift
import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST tower window from the new whole-block transport identity

This derives the exact arbitrary-multiplier tower read from the already
kernel-green quotient block lemma without using GSTTowerFire or the
original monolithic navigation proof. It holds at every natural scale.
-/

namespace GSTWorldtraceTowerWindow

open GSTWorldtraceBlockLift
open GSTFourPowerDirectResidue

/-- The entire first (s+1)-trit quotient block is the tower coefficient
multiplied by u, modulo 3^(s+1). -/
theorem tower_quotient_window (s u : Nat) :
    (4^(u*3^s) / 3^(s+1)) % 3^(s+1) =
      (u * GSTCanonicalTailLTE.lteCoeff s) % 3^(s+1) := by
  have hp := pow4_whole_block_lift 0 u s (s+1) (by omega) (by omega)
  have hlt : 1 < 3^(s+1) := by
    have hh : 0 < 3^s := by positivity
    rw [pow_succ]
    omega
  have hd : 1 / 3^(s+1) = 0 := Nat.div_eq_of_lt hlt
  simpa only [Nat.zero_add, pow_zero, one_div, hd, Nat.zero_add,
    Nat.mul_one] using hp

/-- The GST tower-digit read, recovered from whole-block transport
and the exact digit-slicing theorem: the first s+1 quotient trits of
4^(u*3^s) are those of u*c_s. -/
theorem tower_digit_read_from_block (s u k : Nat) (hk : k ≤ s) :
    digit3 (4^(u*3^s)) (s+1+k) =
      digit3 (u * GSTCanonicalTailLTE.lteCoeff s) k := by
  let R : Nat := 4^(u*3^s)
  let Q : Nat := u * GSTCanonicalTailLTE.lteCoeff s
  have hmod : (R / 3^(s+1)) % 3^(s+1) = Q % 3^(s+1) := by
    simpa only [R, Q] using tower_quotient_window s u
  have hdvd : 3^(k+1) ∣ 3^(s+1) := Nat.pow_dvd_pow 3 (by omega)
  have hmodk :
      (R / 3^(s+1)) % 3^(k+1) = Q % 3^(k+1) := by
    calc
      (R / 3^(s+1)) % 3^(k+1) =
        ((R / 3^(s+1)) % 3^(s+1)) % 3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdvd).symm
      _ = (Q % 3^(s+1)) % 3^(k+1) := by rw [hmod]
      _ = Q % 3^(k+1) := Nat.mod_mod_of_dvd _ hdvd
  have hread : digit3 (R / 3^(s+1)) k = digit3 Q k :=
    digit3_eq_of_mod_next _ _ _ hmodk
  calc
    digit3 (4^(u*3^s)) (s+1+k) =
      digit3 (R / 3^(s+1)) k := by
        unfold digit3
        dsimp [R]
        rw [pow_add, ← Nat.div_div_eq_div_mul]
    _ = digit3 Q k := hread
    _ = digit3 (u * GSTCanonicalTailLTE.lteCoeff s) k := rfl

#print axioms tower_quotient_window
#print axioms tower_digit_read_from_block

end GSTWorldtraceTowerWindow
