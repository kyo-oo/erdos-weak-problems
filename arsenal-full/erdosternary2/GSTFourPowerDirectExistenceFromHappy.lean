import GSTFourPowerDirectExistence
import GSTFourPowerExactExponentPeriod
import GSTFourPowerDirectAdditionCarry
import GSTFourPowerDirectNo22
import GSTFourPowerNo22Magnitude
import GSTFourPowerAffinePeelClassifier
import GSTFourPowerDirectFailedRelocationState
import GSTFourPowerDirectHappyBridge
import GSTFourPowerDirectCreationMaster
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectExistenceFromHappy

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerDirectNo22
open GSTFourPowerNo22Magnitude
open GSTFourPowerExponentTritObstruction
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffinePeelClassifier
open GSTFourPowerDirectFailedRelocationState
open GSTFourPowerDirectHappyBridge
open GSTFourPowerDirectCreationMaster

/-- Direct stack dossier for a hypothetical no-common-two exponent.  This is the
positive replacement for the old opaque navigation failure packet: every field
is extracted from the direct residue/period/affine/no-22/failure-state spine. -/
structure DirectBadDossier (K : Nat) : Prop where
  exactExponentPeriod :
    ∀ p n : Nat, 4^n % 3^(p+1) = 1 ↔ 3^p ∣ n
  noMod9Five : K % 9 ≠ 5
  noMod9Six : K % 9 ≠ 6
  noMod27Fourteen : K % 27 ≠ 14
  noMod27Eighteen : K % 27 ≠ 18
  noMod27Nineteen : K % 27 ≠ 19
  noMod27TwentyFive : K % 27 ≠ 25
  noRowFourClass : ¬ GSTFourPowerDirectResidue81.RowFourClass (K % 81)
  noSource22 :
    ∀ p : Nat,
      ¬ (digit3 (4^K) p = 2 ∧ digit3 (4^K) (p+1) = 2)
  sourceNo22MagnitudeBound :
    ∀ m : Nat, 4^K < 9^m → 8 * 4^K ≤ 7 * (9^m - 1)
  exponentTritLaw :
    ∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1)
  affineLowBranch :
    (K % 3 = 0 ∧ BadChannel 0 (tail3 (affineOrbit K))) ∨
    (K % 3 = 1 ∧ BadChannel 1 (tail3 (affineOrbit K))) ∨
    (K % 3 = 2 ∧ BadChannel 3 (tail3 (affineOrbit K)))

/-- Build the full direct bad-state dossier from `¬ CommonTwo K`.  This theorem
is intentionally broad: it forces the exact exponent period law, residue
filters, no-`22` source language, sharp no-`22` magnitude bound, exact
exponent-trit obstruction, and affine low-trit branch simultaneously. -/
theorem noCommonTwo_builds_direct_bad_dossier
    (K : Nat) (hNo : ¬ CommonTwo K) :
    DirectBadDossier K := by
  have hNoRaw : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2 := by
    simpa [CommonTwo] using hNo
  have h9 := noCommonTwo_excludes_mod9_five_six K hNo
  have h27 := noCommonTwo_excludes_mod27_row_three K hNo
  have h81 := noCommonTwo_excludes_mod81_row_four K hNo
  have h22 := no_common_pow4_forbids_all_22 K hNoRaw
  have htrit := noCommonTwo_all_exponent_trit_laws K hNo
  have haff := (noCommonTwo_low_trit_branch K).1 hNo
  exact {
    exactExponentPeriod := GSTFourPowerExactExponentPeriod.pow4_mod_one_iff_three_pow_dvd
    noMod9Five := h9.1
    noMod9Six := h9.2
    noMod27Fourteen := h27.1
    noMod27Eighteen := h27.2.1
    noMod27Nineteen := h27.2.2.1
    noMod27TwentyFive := h27.2.2.2
    noRowFourClass := h81
    noSource22 := h22
    sourceNo22MagnitudeBound := by
      intro m hm
      exact no22_nine_power_bound (4^K) m hm h22
    exponentTritLaw := htrit
    affineLowBranch := haff
  }

/-- A direct physical Happy row on `4^K` is already a direct common-two row for
`4^K` and `4^(K+1)`.  The proof uses the exact multiplication-by-four carry
formula, not witness transport. -/
theorem happy_row_to_commonTwo
    (K p : Nat) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    CommonTwo K := by
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTCanonicalTailStateIso.HappyCell,
      GSTCanonicalTailStateIso.digit3, digit3] using hHappy.1
  · have hd : digit3 (4^K) p = 2 := by
      simpa [GSTCanonicalTailStateIso.HappyCell,
        GSTCanonicalTailStateIso.digit3, digit3] using hHappy.1
    have hcarryEq :
        directCarry4 (4^K) p = GSTCanonicalTailStateIso.carry4 (4^K) p := by
      rfl
    have hcarryCases : directCarry4 (4^K) p = 0 ∨ directCarry4 (4^K) p = 3 := by
      rw [hcarryEq]
      exact hHappy.2
    have ht4 : digit3 (4 * (4^K)) p = 2 := by
      rw [digit3_four_mul, hd]
      rcases hcarryCases with h0 | h3
      · rw [h0]
        norm_num
      · rw [h3]
        norm_num
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht4

/-- Closed four-power direct existence theorem.  Rows `5` and `6` are discharged
by the exact row-two residue classifier; all `K ≥ 8` are discharged by the
kernel-checked physical Happy source and immediately converted back to direct
common-two arithmetic by `happy_row_to_commonTwo`. -/
theorem fourPowerDirectExistence_closed :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp3, hHappy⟩ :=
      GSTInfiniteFourPowerNavigation.four_power_happy_ge_three K hK8
    exact happy_row_to_commonTwo K p (by omega) hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact commonTwo_of_mod9_five_or_six 5 (Or.inl (by norm_num))
    · exact commonTwo_of_mod9_five_or_six 6 (Or.inr (by norm_num))
    · exact (hK7 rfl).elim

/-- Monolith-facing certificate provider, now routed through the direct
common-two theorem and the already-green direct creation-master bridge. -/
theorem creation_certificate_inline_direct
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (directExistence_to_creation_master fourPowerDirectExistence_closed)
      K hK5 hK7

/-- Monolith-facing creation master, without a fresh axiom boundary. -/
theorem fourPowerCreationMaster_direct :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
  directExistence_to_creation_master fourPowerDirectExistence_closed

#check DirectBadDossier
#check noCommonTwo_builds_direct_bad_dossier
#check happy_row_to_commonTwo
#check fourPowerDirectExistence_closed
#check creation_certificate_inline_direct
#check fourPowerCreationMaster_direct
#print axioms noCommonTwo_builds_direct_bad_dossier
#print axioms happy_row_to_commonTwo
#print axioms fourPowerDirectExistence_closed
#print axioms creation_certificate_inline_direct
#print axioms fourPowerCreationMaster_direct

end GSTFourPowerDirectExistenceFromHappy
