import GSTProblem406BinaryOriginExponentScale
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Problem 406: source-exact finite physical hGate equivalence
#
# The previous finite-horizon theorem used a 2(K+1)+1 row cutoff.
# For EVERY K>=13, the true original CommonTwo(K) is equivalent
# to the same original physical pair having its witness below
# the substantially shorter cutoff (4K-1)/3.
#
# This result is not a new universal existence claim and assumes no
# custom axiom or global thirdWave gate. It tightens the exact
# Archimedean resolution at which the remaining theorem must fire.
-/

namespace GSTProblem406PhysicalCutGateEquivalence

open GSTProblem406BinaryOriginExponentScale
open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue

/-- The exact original gate is equivalent to a K-dependent finite
search only below the sharp physical source terminal bound.
This is a biconditional, not an existence assumption. -/
theorem commonTwo_iff_sharp_physical_cut
    (K : Nat) (hK : 13 ≤ K) :
    CommonTwo K ↔
      ∃ p : Nat, 1 ≤ p ∧ p < physicalShortCut K ∧
        digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2 := by
  constructor
  · rintro ⟨p,hp,hs,hn⟩
    have hcut : p < physicalShortCut K := by
      by_contra hnot
      have hz := physical_source_digit_zero_above_short_cut K p hK (by omega)
      omega
    exact ⟨p,hp,hcut,hs,hn⟩
  · rintro ⟨p,hp,_,hs,hn⟩
    exact ⟨p,hp,hs,hn⟩

/-- Nonexistence is not hidden in an unbounded ideal: every BAD
actual exponent K>=13 corresponds EXACTLY to BADness at
the already kernel-certified physical row cutoff. -/
theorem noCommonTwo_iff_all_sharp_rows_bad
    (K : Nat) (hK : 13 ≤ K) :
    ¬ CommonTwo K ↔
      ∀ p : Nat, 1 ≤ p → p < physicalShortCut K →
      ¬ (digit3 (4^K) p=2 ∧ digit3 (4^(K+1)) p=2) := by
  rw [commonTwo_iff_sharp_physical_cut K hK]
  push_neg
  rfl

#print axioms commonTwo_iff_sharp_physical_cut
#print axioms noCommonTwo_iff_all_sharp_rows_bad

end GSTProblem406PhysicalCutGateEquivalence
