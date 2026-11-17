import GSTFourPowerDirectExistence
import GSTFourPowerDirectHappyBridge
import GSTFourPowerDirectResidue
import GSTFourPowerDirectResidue27
import GSTFourPowerDirectResidue81
import GSTFourPowerExponentTritObstruction
import GSTFourPowerAffineTwoTritClassifier
import GSTFourPowerAffinePeelClassifier
import GSTFourPowerDirectFailedRelocationState
import GSTFourPowerDirectChat2Application

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerHappyProvider

open GSTFourPowerDirectExistence

/-- Direct row-three-or-higher common-two witness, separated from the older
`CommonTwo` API whose witness only starts at row one. -/
def CommonTwoGeThree (K : Nat) : Prop :=
  ∃ p : Nat, 3 ≤ p ∧
    GSTFourPowerDirectResidue.digit3 (4^K) p = 2 ∧
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) p = 2

/-- A prefix/trit hit at ternary exponent scale `p ≥ 2`.  By the exact
`row_common_two_iff_prefix_killing_trit` theorem, this is precisely the
parametric condition that creates a row `p+1 ≥ 3` common-two witness. -/
def PrefixHitGeThree (K : Nat) : Prop :=
  ∃ p : Nat, 2 ≤ p ∧
    GSTFourPowerDirectResidue.digit3
        (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
      GSTFourPowerDirectResidue.digit3
        (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1) ∧
    GSTFourPowerExponentTritObstruction.exponentTrit K p =
      2 - GSTFourPowerDirectResidue.digit3
        (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1)

/-- Transport a direct common-two witness at row `p ≥ 3` into the physical
Graph-V2 Happy predicate.  This is the sharpened bridge needed by the roadmap:
not merely `CommonTwo → HappyCell`, but row-controlled transport. -/
theorem commonTwoAt_ge_three_to_physical_happy
    (K p : Nat) (hp : 3 ≤ p)
    (hs : GSTFourPowerDirectResidue.digit3 (4^K) p = 2)
    (ht : GSTFourPowerDirectResidue.digit3 (4^(K+1)) p = 2) :
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) p)
      (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  unfold GSTCanonicalTailStateIso.HappyCell
  constructor
  · simpa [GSTCanonicalTailStateIso.digit3,
      GSTFourPowerDirectResidue.digit3] using hs
  · have ht4 :
        GSTFourPowerDirectResidue.digit3 (4 * (4^K)) p = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
    have hformula := GSTFourPowerDirectAdditionCarry.digit3_four_mul (4^K) p
    rw [hs, ht4] at hformula
    have hcarry :
        GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 0 ∨
        GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 3 := by
      have hlt := GSTFourPowerDirectAdditionCarry.directCarry4_lt_four (4^K) p
      have hcases :
          GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 0 ∨
          GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 1 ∨
          GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 2 ∨
          GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) p = 3 := by
        omega
      rcases hcases with h0 | h1 | h2 | h3
      · exact Or.inl h0
      · rw [h1] at hformula
        norm_num at hformula
      · rw [h2] at hformula
        norm_num at hformula
      · exact Or.inr h3
    simpa [GSTCanonicalTailStateIso.carry4,
      GSTFourPowerDirectAdditionCarry.directCarry4] using hcarry

/-- Bundled row-controlled direct-to-physical bridge. -/
theorem commonTwoGeThree_to_physical_happy_ge_three
    (K : Nat) (h : CommonTwoGeThree K) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  rcases h with ⟨p, hp, hs, ht⟩
  exact ⟨p, hp, commonTwoAt_ge_three_to_physical_happy K p hp hs ht⟩

/-- Row three residue classes provide a genuine `p = 3` witness. -/
theorem row_three_commonTwoGeThree_of_mod27_classes
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    CommonTwoGeThree K := by
  have hrow := GSTFourPowerDirectResidue27.row_three_overlap_of_mod27_classes K hres
  exact ⟨3, by norm_num, hrow.1, hrow.2⟩

/-- Row four residue classes provide a genuine `p = 4` witness. -/
theorem row_four_commonTwoGeThree_of_mod81_classes
    (K : Nat) (hres : GSTFourPowerDirectResidue81.RowFourClass (K % 81)) :
    CommonTwoGeThree K := by
  have hrow := GSTFourPowerDirectResidue81.row_four_overlap_of_mod81_classes K hres
  exact ⟨4, by norm_num, hrow.1, hrow.2⟩

/-- The exact prefix-hit engine: a matched low-prefix row and the killing trit
create a row `p+1`, hence a `p ≥ 3` common-two witness whenever `2 ≤ p`. -/
theorem commonTwoGeThree_of_prefix_killing_trit
    (K p : Nat) (hp : 2 ≤ p)
    (heq :
      GSTFourPowerDirectResidue.digit3
          (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3
          (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1))
    (hkill :
      GSTFourPowerExponentTritObstruction.exponentTrit K p =
        2 - GSTFourPowerDirectResidue.digit3
          (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1)) :
    CommonTwoGeThree K := by
  have hrow :=
    (GSTFourPowerExponentTritObstruction.row_common_two_iff_prefix_killing_trit K p).2
      ⟨heq, hkill⟩
  exact ⟨p+1, by omega, hrow.1, hrow.2⟩

/-- Bundled prefix-hit route to a row-three-or-higher common-two witness. -/
theorem commonTwoGeThree_of_prefixHitGeThree
    (K : Nat) (hHit : PrefixHitGeThree K) :
    CommonTwoGeThree K := by
  rcases hHit with ⟨p, hp, heq, hkill⟩
  exact commonTwoGeThree_of_prefix_killing_trit K p hp heq hkill

/-- Contrapositive form of the prefix engine: if no row-three-or-higher
common-two witness exists, then no ternary exponent scale `p ≥ 2` can carry
both prefix equality and the matching killing trit. -/
theorem no_commonTwoGeThree_exponent_trit_obstruction
    (K p : Nat) (hp : 2 ≤ p)
    (hNo : ¬ CommonTwoGeThree K)
    (heq :
      GSTFourPowerDirectResidue.digit3
          (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3
          (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1)) :
    GSTFourPowerExponentTritObstruction.exponentTrit K p ≠
      2 - GSTFourPowerDirectResidue.digit3
        (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) := by
  intro hkill
  exact hNo (commonTwoGeThree_of_prefix_killing_trit K p hp heq hkill)

/-- Physical Happy provider for the exact row-three residue classes. -/
theorem happy_ge_three_of_mod27_row_three
    (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  exact commonTwoGeThree_to_physical_happy_ge_three K
    (row_three_commonTwoGeThree_of_mod27_classes K hres)

/-- Physical Happy provider for the exact row-four residue classes. -/
theorem happy_ge_three_of_mod81_row_four
    (K : Nat) (hres : GSTFourPowerDirectResidue81.RowFourClass (K % 81)) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  exact commonTwoGeThree_to_physical_happy_ge_three K
    (row_four_commonTwoGeThree_of_mod81_classes K hres)

/-- Physical Happy provider from the exact parametric prefix-hit engine. -/
theorem happy_ge_three_of_prefixHitGeThree
    (K : Nat) (hHit : PrefixHitGeThree K) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  exact commonTwoGeThree_to_physical_happy_ge_three K
    (commonTwoGeThree_of_prefixHitGeThree K hHit)

/-- Monolith-mined provider gate.  This is the exact remaining provider form:
close row-three-or-higher `CommonTwo`, and the physical Happy theorem follows
without the old infinite-navigation collision seam. -/
theorem four_power_happy_ge_three_from_commonTwoGeThree
    (hProvider : ∀ K : Nat, 8 ≤ K → CommonTwoGeThree K)
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  exact commonTwoGeThree_to_physical_happy_ge_three K (hProvider K hK)

/-- Universal Happy provider from the parametric prefix-hit theorem.  This is
now the direct Chat-2 route: prefix obstruction engine → row `p ≥ 3`
CommonTwo → physical HappyCell. -/
theorem four_power_happy_ge_three_from_prefixHitGeThree
    (hProvider : ∀ K : Nat, 8 ≤ K → PrefixHitGeThree K)
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) := by
  exact happy_ge_three_of_prefixHitGeThree K (hProvider K hK)

/-- The roadmap target as a named proposition, now separated from the bridge
machinery so axiom audits can see the actual remaining mathematical seam. -/
def FourPowerHappyGeThreeFromMonolith : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

#check CommonTwoGeThree
#check PrefixHitGeThree
#check commonTwoAt_ge_three_to_physical_happy
#check commonTwoGeThree_to_physical_happy_ge_three
#check row_three_commonTwoGeThree_of_mod27_classes
#check row_four_commonTwoGeThree_of_mod81_classes
#check commonTwoGeThree_of_prefix_killing_trit
#check commonTwoGeThree_of_prefixHitGeThree
#check no_commonTwoGeThree_exponent_trit_obstruction
#check happy_ge_three_of_mod27_row_three
#check happy_ge_three_of_mod81_row_four
#check happy_ge_three_of_prefixHitGeThree
#check four_power_happy_ge_three_from_commonTwoGeThree
#check four_power_happy_ge_three_from_prefixHitGeThree
#check FourPowerHappyGeThreeFromMonolith
#print axioms commonTwoAt_ge_three_to_physical_happy
#print axioms commonTwoGeThree_to_physical_happy_ge_three
#print axioms row_three_commonTwoGeThree_of_mod27_classes
#print axioms row_four_commonTwoGeThree_of_mod81_classes
#print axioms commonTwoGeThree_of_prefix_killing_trit
#print axioms commonTwoGeThree_of_prefixHitGeThree
#print axioms no_commonTwoGeThree_exponent_trit_obstruction
#print axioms happy_ge_three_of_mod27_row_three
#print axioms happy_ge_three_of_mod81_row_four
#print axioms happy_ge_three_of_prefixHitGeThree
#print axioms four_power_happy_ge_three_from_commonTwoGeThree
#print axioms four_power_happy_ge_three_from_prefixHitGeThree

end GSTFourPowerHappyProvider
