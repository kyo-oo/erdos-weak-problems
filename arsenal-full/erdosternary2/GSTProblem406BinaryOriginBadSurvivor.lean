import GSTProblem406BinaryOriginExponentScale
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Problem 406 — physical BAD exponent forces a genuine high-valuation
# finite ternary survivor, without introducing a new axiom.

This is an unconditional reduction in the ORIGINAL direction:
if K>=13 were an actual counterexample to CommonTwo(K), then the
specific integer R=4^K must simultaneously be:
(1) a literal all-row GST BAD source for R -> 4R;
(2) less than 3^L at the strict physical terminal cut L;
(3) a ternary 1-unit and divisible by 2^(floor(3L/2)+1).

The existence of such BAD integers at arbitrary L is NOT ruled out by
this module. This theorem is a proved necessary obstruction, not a
replacement universal hypothesis, and does not assert Erdős 406.
-/

namespace GSTProblem406BinaryOriginBadSurvivor

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTProblem406BinaryOriginExponentScale

/-- In the true original exponent family, a counterexample after K=12
creates an exact simultaneous binary-terminal/ternary-BAD packet.
No local prefix or surrogate exponent is involved. -/
theorem bad_physical_exponent_produces_binary_origin_survivor
    (K : Nat) (hK : 13 ≤ K)
    (hBad : ¬ CommonTwo K) :
    ∃ L R : Nat,
      10 ≤ L ∧
      0 < R ∧
      R < 3^L ∧
      R%3=1 ∧
      (2:Nat)^((3*L)/2+1) ∣ R ∧
      (∀ p : Nat, 1 ≤ p →
        ¬ (digit3 R p=2 ∧ digit3 (4*R) p=2)) := by
  let L := physicalShortCut K
  let R := 4^K
  have hL10 : 10 ≤ L := by
    dsimp [L,physicalShortCut]
    omega
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < 3^L := by
    dsimp [R,L]
    exact physical_source_lt_short_cut K hK
  have hRmod : R%3=1 := by
    dsimp [R]
    simp [Nat.pow_mod]
  have hRval : (2:Nat)^((3*L)/2+1) ∣ R := by
    dsimp [R,L]
    exact physical_source_high_binary_order K hK
  refine ⟨L,R,hL10,hRpos,hRlt,hRmod,hRval,?_⟩
  intro p hp ⟨hd,hn⟩
  apply hBad
  refine ⟨p,hp,?_,?_⟩
  · simpa [R] using hd
  · have heq : (4:Nat)^(K+1) = 4*(4^K) := by
      rw [pow_succ]
      ring
    simpa [R,heq] using hn

#print axioms bad_physical_exponent_produces_binary_origin_survivor

end GSTProblem406BinaryOriginBadSurvivor
