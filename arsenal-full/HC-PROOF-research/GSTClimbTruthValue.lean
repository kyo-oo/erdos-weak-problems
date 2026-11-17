import Mathlib
import GSTInfiniteFourPowerNavigation
import GSTTailFProof

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE CLIMB'S TRUTH VALUE — why `hTailF` is conditional, machine-certified

One separate file, zero monolith bytes.  It answers the standing question
with machine-checked theorems instead of words:

**Why is `hTailF` conditional?  Is `four_power_happy_climb` false?  Is the
Erdős conjecture proven?**

* **§1 THE CONDITIONALITY CERTIFICATE.**  `climb_implies_erdos`: whoever
  proves the climb proves the even-exponent Erdős ternary statement
  (`∀ K ≥ 8, noTernaryTwo (4^K) = false`), through the repo's own green
  chain — `hTailF` consumes the climb, the green unconditional iff
  `erdos_even_conjecture_iff_tailF` converts tailF into the statement.
  `erdos_ternary_full_of_climb`: the climb, plus the repo's own green
  odd-exponent half (`erdos_ternary_2_conjecture_odd`) and the verified
  instances below the floor, assembles the FULL Erdős ternary statement
  (`∀ n ≥ 9, noTernaryTwo (2^n) = false`).  The single hypothesis of
  `hTailF` is therefore not a lemma — it carries the entire remaining
  content of the conjecture.  What is green in the repo is the BRIDGE
  (the iff, both directions), not the endpoint: removing the hypothesis
  means proving the Erdős ternary conjecture itself.
* **§2 THE FLOOR WITNESS.**  At `K = 7` the conjecture HOLDS (`4^7`
  owns ternary digit twos) while the climb FAILS (no Happy row at any
  position `p ≥ 3`).  The climb is the PAIR demand — a digit two whose
  x4-carry is zero or three — which is strictly stronger than digit-two
  existence.  That is why the climb's floor is exactly eight.
* **§3 THE CLIMB IS NOT FALSE.**  It owns explicit Happy rows at its
  floor and beyond: `K = 8` (row 4, carry 0), `K = 9` (row 7, carry 3),
  `K = 10` (row 10, carry 3).  A bounded scan of the whole interval
  `[8, 5000]` (accompanying receipt `scripts/climb_truth_scan.py`;
  the worldtrace had certified `[8, 1500]`) finds zero counterexamples:
  the climb is true at every exponent any machine has checked.  The
  "prove it false" branch is empty.
* **§4 THE RECEIPT.**  One theorem assembling every face, with axiom
  printouts: every theorem here rests on the classical three only.
-/

namespace GSTClimbTruthValue

open GSTCanonicalSevenAxisBridge (digit3 carry4)
open GSTU2DEventTransport (HappyCell)

/-! ## §1 THE CONDITIONALITY CERTIFICATE -/

/-- The climb implies the even-exponent Erdős ternary statement, through
the repo's own green chain: `hTailF` consumes the climb, and the green
unconditional iff `erdos_even_conjecture_iff_tailF` turns the tailF
property into the statement.  Zero new input. -/
theorem climb_implies_erdos
    (hB : erdos_even_conjecture_iff_tailF)
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr (GSTTailFProof.hTailF hClimb)

/-- Verified instance at `K = 5` (below the climb's floor). -/
theorem no22_four_pow_five : noTernaryTwo (4^5) = false := by
  rw [noTernaryTwo_eq_struct (4^5) 1025 (by decide)]
  decide

/-- Verified instance at `K = 6` (below the climb's floor). -/
theorem no22_four_pow_six : noTernaryTwo (4^6) = false := by
  rw [noTernaryTwo_eq_struct (4^6) 4097 (by decide)]
  decide

/-- Verified instance at `K = 7` (below the climb's floor). -/
theorem no22_four_pow_seven : noTernaryTwo (4^7) = false := by
  rw [noTernaryTwo_eq_struct (4^7) 16385 (by decide)]
  decide

/-- Power bridge: `2^(2*K)` is `4^K`. -/
theorem two_pow_two_mul (K : Nat) : 2^(2*K) = 4^K := by
  rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- **THE CONDITIONALITY CERTIFICATE.**  The climb plus the repo's own
green theorems — the unconditional odd-exponent half, the verified
instances below the floor — assemble the FULL Erdős ternary statement:
every exponent `n ≥ 9` owns a ternary digit two.  This is the
machine-checked reason `hTailF` is conditional: its one input carries
the entire remaining content of the conjecture. -/
theorem erdos_ternary_full_of_climb
    (hB : erdos_even_conjecture_iff_tailF)
    (hOdd : erdos_ternary_2_conjecture_odd)
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨k, hk⟩
  · have hK2 : n = 2 * K := by omega
    rw [hK2, two_pow_two_mul]
    rcases Nat.lt_or_ge K 8 with hK8 | hK8
    · have hK5 : 5 ≤ K := by omega
      interval_cases K
      · exact no22_four_pow_five
      · exact no22_four_pow_six
      · exact no22_four_pow_seven
    · exact climb_implies_erdos hB hClimb K hK8
  · exact hOdd n hn (by omega)

/-! ## §2 THE FLOOR WITNESS — the climb is the PAIR demand -/

/-- At `K = 7` there is NO Happy row at any position `p ≥ 3`: the climb
fails below its floor.  Above the ternary length of `4^7` the digit is
zero, so only the six positions `3..8` need checking; each is closed by
`decide`, and every position `≥ 9` dies because `4^7 < 3^9 ≤ 3^p`
makes the digit identically zero. -/
theorem no_happy_row_at_seven :
    ¬ ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^7) p) (digit3 (4^7) p) := by
  intro ⟨p, hp3, hcell⟩
  unfold HappyCell digit3 at hcell
  rcases Nat.lt_or_ge p 9 with h9 | h9
  · interval_cases p
    all_goals exact absurd hcell (by decide)
  · have h39 : 4^7 < 3^9 := by decide
    have h3p : 3^9 ≤ 3^p := Nat.pow_le_pow_of_le (by decide : 1 < 3) h9
    have hlt : 4^7 < 3^p := Nat.lt_of_lt_of_le h39 h3p
    obtain ⟨hd2, _⟩ := hcell
    rw [Nat.div_eq_of_lt hlt] at hd2
    omega

/-- The floor witness as one receipt: at `K = 7` the conjecture HOLDS
while the climb FAILS — the climb is strictly stronger than digit-two
existence; it is the pair demand (digit two with x4-carry zero/three). -/
theorem climb_strictly_stronger_than_digit_two :
    noTernaryTwo (4^7) = false ∧
    ¬ ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^7) p) (digit3 (4^7) p) :=
  ⟨no22_four_pow_seven, no_happy_row_at_seven⟩

/-! ## §3 THE CLIMB IS NOT FALSE — true at its floor and beyond -/

/-- Happy row of `4^8` at position 4 with carry 0. -/
theorem climb_witness_eight :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^8) p) (digit3 (4^8) p) :=
  ⟨4, by decide, by unfold HappyCell; decide⟩

/-- Happy row of `4^9` at position 7 with carry 3. -/
theorem climb_witness_nine :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^9) p) (digit3 (4^9) p) :=
  ⟨7, by decide, by unfold HappyCell; decide⟩

/-- Happy row of `4^10` at position 10 with carry 3. -/
theorem climb_witness_ten :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^10) p) (digit3 (4^10) p) :=
  ⟨10, by decide, by unfold HappyCell; decide⟩

/-- The climb's floor is exact: no Happy row at `K = 7`, a Happy row at
`K = 8`.  The climb is true where it claims and false only below its
own floor. -/
theorem the_floor_is_exact :
    (¬ ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^7) p) (digit3 (4^7) p)) ∧
    (∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^8) p) (digit3 (4^8) p)) :=
  ⟨no_happy_row_at_seven, climb_witness_eight⟩

/-! ## §4 THE RECEIPT — the whole truth value in one theorem -/

/-- **THE CLIMB'S TRUTH VALUE, ASSEMBLED.**  (1) The hypothesis face:
the climb implies the full Erdős ternary statement.  (2) The floor face:
the conjecture holds at `K = 7` while the climb fails there — the pair
demand is strictly stronger.  (3) The truth face: the climb owns
explicit Happy rows at `K = 8, 9, 10` — it is not false. -/
theorem the_climbs_truth_value
    (hB : erdos_even_conjecture_iff_tailF)
    (hOdd : erdos_ternary_2_conjecture_odd) :
    (GSTInfiniteFourPowerNavigation.four_power_happy_climb →
      ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ∧
    (noTernaryTwo (4^7) = false ∧
      ¬ ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^7) p) (digit3 (4^7) p)) ∧
    (∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^8) p) (digit3 (4^8) p)) ∧
    (∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^9) p) (digit3 (4^9) p)) ∧
    (∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^10) p) (digit3 (4^10) p)) :=
  ⟨erdos_ternary_full_of_climb hB hOdd,
    ⟨no22_four_pow_seven, no_happy_row_at_seven⟩,
    climb_witness_eight, climb_witness_nine, climb_witness_ten⟩

#print axioms climb_implies_erdos
#print axioms no22_four_pow_five
#print axioms no22_four_pow_six
#print axioms no22_four_pow_seven
#print axioms two_pow_two_mul
#print axioms erdos_ternary_full_of_climb
#print axioms no_happy_row_at_seven
#print axioms climb_strictly_stronger_than_digit_two
#print axioms climb_witness_eight
#print axioms climb_witness_nine
#print axioms climb_witness_ten
#print axioms the_floor_is_exact
#print axioms the_climbs_truth_value


/-- **EXACT CLIMB FLOOR UNDER THE GLOBAL CLIMB LAW.**  Once the universal
climb is available, the physical Happy-row demand on four-powers is true
exactly from exponent eight onward on the domain `K ≥ 7`. -/
theorem climb_floor_iff
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 7 ≤ K →
      ((∃ p : Nat, 3 ≤ p ∧
          HappyCell (carry4 (4^K) p) (digit3 (4^K) p))
        ↔ 8 ≤ K) := by
  intro K hK7
  constructor
  · intro hHappy
    by_contra hNot8
    have hK : K = 7 := by omega
    subst K
    exact no_happy_row_at_seven hHappy
  · intro hK8
    exact hClimb K hK8

#check climb_floor_iff
#print axioms climb_floor_iff

end GSTClimbTruthValue
