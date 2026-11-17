import GSTFourPowerDirectResidue
import GSTFourPowerDirectResidue27
import GSTFourPowerDirectResidue81
import GSTFourPowerExponentTritObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectExistence

open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue27
open GSTFourPowerDirectResidue81
open GSTFourPowerExponentTritObstruction

/-- Pure arithmetic common-digit predicate for two consecutive powers of four.
This is the primary object of the corrected proof architecture: it contains no
source Happy witness, relocation hypothesis, or propagation edge. -/
def CommonTwo (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧
    digit3 (4^(K+1)) p = 2

/-- The actual universal arithmetic target, isolated from all propagation
machinery. The only exceptional exponent in the statement is `7`. -/
def FourPowerDirectExistence : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K

/-- A common-two witness in particular proves that the source power itself has
a ternary digit two. -/
theorem commonTwo_has_source_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 := by
  rcases h with ⟨p, hp, h0, h1⟩
  exact ⟨p, hp, h0⟩

/-- Symmetrically, a common-two witness gives a ternary digit two in the next
power as well. -/
theorem commonTwo_has_target_two
    (K : Nat) (h : CommonTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^(K+1)) p = 2 := by
  rcases h with ⟨p, hp, h0, h1⟩
  exact ⟨p, hp, h1⟩

/-- The exact row-two classifier gives a direct common witness in exponent
classes five and six modulo nine. -/
theorem commonTwo_of_mod9_five_or_six
    (K : Nat) (hres : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K := by
  refine ⟨2, by norm_num, ?_⟩
  exact row_two_overlap_of_mod9_five_or_six K hres

/-- Therefore a hypothetical counterexample to the direct theorem cannot lie
in either exact row-two overlap class. -/
theorem noCommonTwo_excludes_mod9_five_six
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 9 ≠ 5 ∧ K % 9 ≠ 6 := by
  exact no_common_two_forbids_mod9_five_six K hNo

/-- The exact row-three classifier supplies a direct common-two witness in four
additional exponent classes modulo 27. -/
theorem commonTwo_of_mod27_row_three
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    CommonTwo K := by
  refine ⟨3, by norm_num, ?_⟩
  exact row_three_overlap_of_mod27_classes K hres

/-- Consequently, a hypothetical direct counterexample avoids every exact
row-three overlap class modulo 27. -/
theorem noCommonTwo_excludes_mod27_row_three
    (K : Nat) (hNo : ¬ CommonTwo K) :
    K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25 := by
  exact no_common_two_forbids_mod27_classes K hNo

/-- Row four contributes fourteen exact common-two classes modulo 81. -/
theorem commonTwo_of_mod81_row_four
    (K : Nat) (hres : RowFourClass (K % 81)) :
    CommonTwo K := by
  refine ⟨4, by norm_num, ?_⟩
  exact row_four_overlap_of_mod81_classes K hres

/-- Hence a hypothetical counterexample avoids every exact row-four class. -/
theorem noCommonTwo_excludes_mod81_row_four
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ¬ RowFourClass (K % 81) := by
  exact no_common_two_forbids_mod81_classes K hNo

/-- Every hypothetical direct counterexample obeys the parametric exponent-trit
obstruction at every scale.  If the two low-prefix values agree at row `p+1`,
the actual `p`-th ternary trit of `K` cannot equal the canonical killing trit.

This is the recursive direct proof law: it constrains the ternary expansion of
`K` itself and contains no source-witness transport. -/
theorem noCommonTwo_exponent_trit_law
    (K p : Nat) (hNo : ¬ CommonTwo K)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - digit3 (4^(exponentPrefix K p)) (p+1) := by
  exact no_common_two_exponent_trit_obstruction K p hNo heq

/-- Bundled form: a hypothetical counterexample carries the trit obstruction
uniformly at every ternary scale. -/
theorem noCommonTwo_all_exponent_trit_laws
    (K : Nat) (hNo : ¬ CommonTwo K) :
    ∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1) := by
  intro p heq
  exact noCommonTwo_exponent_trit_law K p hNo heq

/-- The direct universal target implies the corresponding source-digit-two
existence statement immediately. This records the genuine arithmetic strength
of the remaining boundary. -/
theorem directExistence_implies_source_two
    (h : FourPowerDirectExistence)
    (K : Nat) (hK : 5 ≤ K) (h7 : K ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 := by
  exact commonTwo_has_source_two K (h K hK h7)

#check CommonTwo
#check FourPowerDirectExistence
#check commonTwo_has_source_two
#check commonTwo_has_target_two
#check commonTwo_of_mod9_five_or_six
#check noCommonTwo_excludes_mod9_five_six
#check commonTwo_of_mod27_row_three
#check noCommonTwo_excludes_mod27_row_three
#check commonTwo_of_mod81_row_four
#check noCommonTwo_excludes_mod81_row_four
#check noCommonTwo_exponent_trit_law
#check noCommonTwo_all_exponent_trit_laws
#check directExistence_implies_source_two
#print axioms commonTwo_has_source_two
#print axioms commonTwo_has_target_two
#print axioms commonTwo_of_mod9_five_or_six
#print axioms noCommonTwo_excludes_mod9_five_six
#print axioms commonTwo_of_mod27_row_three
#print axioms noCommonTwo_excludes_mod27_row_three
#print axioms commonTwo_of_mod81_row_four
#print axioms noCommonTwo_excludes_mod81_row_four
#print axioms noCommonTwo_exponent_trit_law
#print axioms noCommonTwo_all_exponent_trit_laws
#print axioms directExistence_implies_source_two

end GSTFourPowerDirectExistence
