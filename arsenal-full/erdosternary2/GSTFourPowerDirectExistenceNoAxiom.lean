import GSTFourPowerDirectExistence
import GSTFourPowerDirectAdditionCarry
import GSTCanonicalTailStateIso

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

-- Controlled CI trigger: clean bridge probe after Lake rollback.

/-!
# Separate no-axiom bridge for `FourPowerDirectExistence`

This file is intentionally *not* wired into the monolith.  It also deliberately
avoids `GSTInfiniteFourPowerNavigation`: that experimental provider currently
fails to build and its printed axiom audit contains `sorryAx`.

The clean certified content here is the arithmetic bridge:

* direct small cases `K = 5,6` give `CommonTwo` at row `p = 2`;
* any physical Happy row on `4^K` gives a same-row `CommonTwo K` witness;
* therefore a theorem-backed `K ≥ 8` Happy-row provider is exactly sufficient
  to close `FourPowerDirectExistence` without the old production-boundary axiom.
-/

namespace GSTFourPowerDirectExistenceNoAxiom

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry

/-- A physical Happy cell for `4^K` is exactly a same-row common-two witness for
`4^K` and `4^(K+1)`. -/
theorem happyCell_to_commonTwo
    (K p : Nat) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    CommonTwo K := by
  unfold GSTCanonicalTailStateIso.HappyCell at hHappy
  rcases hHappy with ⟨hd, hc⟩
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3] using hd
  · have hsrc : GSTFourPowerDirectResidue.digit3 (4^K) p = 2 := by
      simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3] using hd
    have hcarry : directCarry4 (4^K) p = 0 ∨ directCarry4 (4^K) p = 3 := by
      simpa [GSTCanonicalTailStateIso.carry4, directCarry4] using hc
    have hmulFormula := digit3_four_mul (4^K) p
    have hmul : GSTFourPowerDirectResidue.digit3 (4 * (4^K)) p = 2 := by
      rw [hmulFormula, hsrc]
      rcases hcarry with h0 | h3
      · simp [h0]
      · simp [h3]
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Direct base case `K = 5`, witnessed at row two. -/
theorem commonTwo_five : CommonTwo 5 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

/-- Direct base case `K = 6`, witnessed at row two. -/
theorem commonTwo_six : CommonTwo 6 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

/-- Clean reduction of the remaining seam.  The only mathematical input still
needed is a theorem-backed Happy-row provider for `K ≥ 8`; no custom axiom,
monolith transplant, or dirty navigation provider is used here. -/
theorem fourPowerDirectExistence_from_physical_happy_ge_three
    (happy_ge_three :
      ∀ K : Nat, 8 ≤ K →
        ∃ p : Nat, 3 ≤ p ∧
          GSTCanonicalTailStateIso.HappyCell
            (GSTCanonicalTailStateIso.carry4 (4^K) p)
            (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ := happy_ge_three K hK8
    exact happyCell_to_commonTwo K p (by omega) hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact commonTwo_five
    · exact commonTwo_six
    · exact (hK7 rfl).elim

#print axioms happyCell_to_commonTwo
#print axioms commonTwo_five
#print axioms commonTwo_six
#print axioms fourPowerDirectExistence_from_physical_happy_ge_three

end GSTFourPowerDirectExistenceNoAxiom
