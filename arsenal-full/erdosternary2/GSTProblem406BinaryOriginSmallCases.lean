import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact physical small K=5..12 gates, with the excluded exponent 7

This supplies all base exponents below the new binary-origin
physical short-cut K>=13. Every witness is a SAME physical row
in 4^K and 4^(K+1). No custom axiom, hGate or surrogate.
-/

namespace GSTProblem406BinaryOriginSmallCases

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue

theorem commonTwo_small_K_exact
    (K : Nat) (hLow : 5 ≤ K) (hHigh : K ≤ 12) (hK7 : K ≠ 7) :
    CommonTwo K := by
  have hCases : K=5 ∨ K=6 ∨ K=8 ∨ K=9 ∨ K=10 ∨ K=11 ∨ K=12 := by omega
  rcases hCases with h|h|h|h|h|h|h
  · subst K
    refine ⟨2,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨2,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨4,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨7,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨10,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨10,by decide,?_,?_⟩ <;> norm_num [digit3]
  · subst K
    refine ⟨10,by decide,?_,?_⟩ <;> norm_num [digit3]

#print axioms commonTwo_small_K_exact

end GSTProblem406BinaryOriginSmallCases
