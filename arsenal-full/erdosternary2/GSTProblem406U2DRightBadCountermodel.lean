import GSTU2DSharpCrossingBlock
import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact U2D right-BAD / positive-rectangle countermodel

This is an adversarial check of one proposed proof shortcut,
NOT a counterexample to the original CommonTwo theorem.

The positive source A=55 satisfies A mod 27 = 1.  Its own
source-neighbor pair has a genuine Happy digit 2 at row 3.
The right source after horizontal width N=3 is 55*4^3=3520,
which has NO shared digit 2 with 4*3520 at ANY ternary row,
including row zero.  However the exact x4-by-3 weighted
crossing sum through row 3 is POSITIVE, equal to 41661.

Therefore right-boundary all-depth BADness alone does NOT
force the left-to-right full U2D rectangle weighted sum <=0.
Any proposed universal proof using that sign transfer must
supply an additional canonical perfect-power-specific
interior constraint. All statements here are exact arithmetic.
-/

namespace GSTProblem406U2DRightBadCountermodel

open GSTU2DExactCrossingCharge
open GSTFourPowerDirectResidue

private def demoDigit (t p : Nat) : Nat :=
  digit3 (55*4^t) p

private def demoCarry (t p : Nat) : Nat :=
  (4*((55*4^t)%3^p))/3^p

/-- The arbitrary (non-perfect-power) initial source has
the same low ternary prefix 1 as a canonical residual source. -/
theorem demo_source_mod27 : 55%27=1 := by decide

/-- The left edge genuinely has common 2 at source row 3. -/
theorem demo_left_physical_happy :
    digit3 55 3=2 ∧ digit3 (4*55) 3=2 := by
  norm_num [digit3]

/-- The right edge has no common 2 at ANY row; this includes
the actual all-depth infinite BAD requirement (not a finite
sample), since the right source is less than 3^8. -/
theorem demo_right_all_depth_bad :
    ∀ p : Nat,
      ¬ (digit3 (55*4^3) p=2 ∧
         digit3 (55*4^4) p=2) := by
  intro p
  by_cases hp : p<8
  · have hp7 : p ≤ 7 := by omega
    interval_cases p <;> norm_num [digit3] <;> omega
  · have hpow : (3:Nat)^8 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) (by omega)
    have hlt : (55:Nat)*4^3 < 3^p := by
      have hsmall : (55:Nat)*4^3 < 3^8 := by decide
      omega
    have hzero : digit3 (55*4^3) p=0 := by
      unfold digit3
      rw [Nat.div_eq_of_lt hlt]
    omega

/-- Explicit exact failure of the sought generic sign
implication. This is the full weightedCrossPrefix, not just
the boundary crossDensity. -/
theorem demo_positive_full_rectangle :
    weightedCrossPrefix demoCarry demoDigit 3 4 = 41661 := by
  decide

theorem right_bad_does_not_force_nonpositive_rectangle :
    (∀ p : Nat,
      ¬ (digit3 (55*4^3) p=2 ∧ digit3 (55*4^4) p=2))
      ∧ 0 < weightedCrossPrefix demoCarry demoDigit 3 4 := by
  constructor
  · exact demo_right_all_depth_bad
  · rw [demo_positive_full_rectangle]
    decide

#print axioms demo_right_all_depth_bad
#print axioms demo_positive_full_rectangle
#print axioms right_bad_does_not_force_nonpositive_rectangle

end GSTProblem406U2DRightBadCountermodel
