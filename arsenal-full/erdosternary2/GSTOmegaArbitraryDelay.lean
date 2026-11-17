import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# No uniform finite-horizon theorem for nonexceptional natural powers

For every finite ternary observation depth L, and every requested
minimum natural exponent M, there is a natural K >= max M 5
for which 4^K has no digit two at ANY position p <= L.

This is not a counterexample to Erdős: digits beyond L are unrestricted.
It is an unconditional global obstruction to using a finite horizon
or the mere eventual-zero property of exponent digits as an
automatic universal terminal exit from the binary shadow tree.
-/

namespace GSTOmegaArbitraryDelay

open GSTFourPowerDirectResidue

/-- The exceptional seed power 4^4=256 has no digit two at any depth. -/
theorem exceptional_four_is_clean (p : Nat) :
    digit3 (4^4) p ≠ 2 := by
  by_cases hp : p < 6
  · interval_cases p <;> norm_num [digit3]
  · have hle : 3^6 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    have hsmall : 4^4 < 3^p := by
      have h : 4^4 < 3^6 := by decide
      omega
    have hzero : 4^4 / 3^p = 0 := Nat.div_eq_of_lt hsmall
    change (4^4 / 3^p) % 3 ≠ 2
    rw [hzero]
    decide

/-- Any arbitrarily large natural exponent can reproduce the clean
seed through an arbitrarily prescribed ternary observation horizon.
No cutoff is searched; the construction is algebraic. -/
theorem arbitrarily_large_natural_clean_prefix
    (L M : Nat) :
    ∃ K : Nat, 5 ≤ K ∧ M ≤ K ∧
      ∀ p : Nat, p ≤ L → digit3 (4^K) p ≠ 2 := by
  let K : Nat := 4 + 3^L * (M+5)
  have hpge : 1 ≤ 3^L := by
    have hpos : 0 < 3^L := by positivity
    omega
  refine ⟨K, ?_, ?_, ?_⟩
  · dsimp [K]
    nlinarith
  · dsimp [K]
    nlinarith
  · intro p hp
    have hpow : 3^L = 3^p*3^(L-p) := by
      rw [← pow_add]
      congr 1
      omega
    have hshape :
        3^L * (M+5) = 3^p * (3^(L-p)*(M+5)) := by
      rw [hpow]
      ring
    have hrepr : K = 4 + 3^p * (3^(L-p)*(M+5)) := by
      dsimp [K]
      rw [hshape]
    rw [hrepr]
    rw [pow4_digit_period p 4 (3^(L-p)*(M+5))]
    exact exceptional_four_is_clean p

#print axioms exceptional_four_is_clean
#print axioms arbitrarily_large_natural_clean_prefix

end GSTOmegaArbitraryDelay
