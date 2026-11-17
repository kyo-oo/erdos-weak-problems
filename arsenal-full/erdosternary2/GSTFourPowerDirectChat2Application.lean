import GSTFourPowerAffineTwoTritClassifier
import GSTFourPowerDirectFailedRelocationState

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectChat2Application

open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue27
open GSTFourPowerDirectResidue81
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerExponentTritObstruction
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffinePeelClassifier
open GSTFourPowerAffineTwoTritClassifier
open GSTFourPowerDirectFailedRelocationState

/-- Chat-2 application surface: the direct problem is exactly channel `1` on
    the affine orbit.  This is the point where the proof must live; it is not a
    Happy-witness propagation statement. -/
theorem chat2_commonTwo_iff_affine_channel_one (K : Nat) :
    CommonTwo K ↔ PairCommonTwo (affineOrbit K) (4 * affineOrbit K + 1) := by
  exact commonTwo_iff_channel_one K

/-- Chat-2 application surface: a hypothetical counterexample is exactly bad
    state `B₁` of the affine digit transducer. -/
theorem chat2_noCommonTwo_iff_bad_channel_one (K : Nat) :
    (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K) := by
  exact noCommonTwo_iff_badChannel_one K

/-- First exponent-trit split of the direct counterexample language.  This is
    the parametric prefix law entry point. -/
theorem chat2_first_trit_counterexample_split (K : Nat) :
    (¬ CommonTwo K) ↔
      (K % 3 = 0 ∧ BadChannel 0 (tail3 (affineOrbit K))) ∨
      (K % 3 = 1 ∧ BadChannel 1 (tail3 (affineOrbit K))) ∨
      (K % 3 = 2 ∧ BadChannel 3 (tail3 (affineOrbit K))) := by
  exact noCommonTwo_low_trit_branch K

/-- Two-trit structural recovery of the `K ≡ 6 (mod 9)` killing class, derived
    from the transducer instead of the residue table. -/
theorem chat2_commonTwo_of_mod9_six (K : Nat) (hK : K % 9 = 6) :
    CommonTwo K := by
  let q : Nat := 2 + 3 * (K / 9)
  have hsplit0 := Nat.mod_add_div K 9
  have hsplit : K = 6 + 9 * (K / 9) := by
    rw [hK] at hsplit0
    omega
  have hq : q % 3 = 2 := by
    dsimp [q]
    omega
  have hKq : K = 3 * q := by
    dsimp [q]
    omega
  rw [hKq]
  exact commonTwo_three_mul_of_q_mod_three_two q hq

/-- Two-trit structural recovery of the `K ≡ 5 (mod 9)` killing class, derived
    from the transducer instead of the residue table. -/
theorem chat2_commonTwo_of_mod9_five (K : Nat) (hK : K % 9 = 5) :
    CommonTwo K := by
  let q : Nat := 1 + 3 * (K / 9)
  have hsplit0 := Nat.mod_add_div K 9
  have hsplit : K = 5 + 9 * (K / 9) := by
    rw [hK] at hsplit0
    omega
  have hq : q % 3 = 1 := by
    dsimp [q]
    omega
  have hKq : K = 3 * q + 2 := by
    dsimp [q]
    omega
  rw [hKq]
  exact commonTwo_three_mul_add_two_of_q_mod_three_one q hq

/-- Bundled row-two recovery from the Chat-2 affine route. -/
theorem chat2_commonTwo_of_mod9_five_or_six
    (K : Nat) (hK : K % 9 = 5 ∨ K % 9 = 6) :
    CommonTwo K := by
  rcases hK with h5 | h6
  · exact chat2_commonTwo_of_mod9_five K h5
  · exact chat2_commonTwo_of_mod9_six K h6

/-- A direct counterexample carries all currently clean arithmetic obstruction
    surfaces simultaneously: row two, row three, row four, and the parametric
    exponent-trit law. -/
theorem chat2_counterexample_obstruction_bundle
    (K : Nat) (hNo : ¬ CommonTwo K) :
    (K % 9 ≠ 5 ∧ K % 9 ≠ 6) ∧
    (K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25) ∧
    (¬ RowFourClass (K % 81)) ∧
    (∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1)) := by
  exact ⟨
    noCommonTwo_excludes_mod9_five_six K hNo,
    noCommonTwo_excludes_mod27_row_three K hNo,
    noCommonTwo_excludes_mod81_row_four K hNo,
    noCommonTwo_all_exponent_trit_laws K hNo⟩

/-- Direct bad-channel consequence of the obstruction bundle.  This is Chat-2's
    realization in its most useful form: any surviving affine bad state inherits
    all row and prefix obstructions. -/
theorem chat2_bad_affine_channel_one_obstruction_bundle
    (K : Nat) (hBad : BadChannel 1 (affineOrbit K)) :
    (K % 9 ≠ 5 ∧ K % 9 ≠ 6) ∧
    (K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25) ∧
    (¬ RowFourClass (K % 81)) ∧
    (∀ p : Nat,
      digit3 (4^(exponentPrefix K p)) (p+1) =
        digit3 (4^((exponentPrefix K p)+1)) (p+1) →
      exponentTrit K p ≠
        2 - digit3 (4^(exponentPrefix K p)) (p+1)) := by
  have hNo : ¬ CommonTwo K := (chat2_noCommonTwo_iff_bad_channel_one K).2 hBad
  exact chat2_counterexample_obstruction_bundle K hNo

/-- The row-two classes are already killed directly in affine bad-channel form. -/
theorem chat2_no_bad_affine_channel_one_of_mod9_five_or_six
    (K : Nat) (hK : K % 9 = 5 ∨ K % 9 = 6) :
    ¬ BadChannel 1 (affineOrbit K) := by
  intro hBad
  have hNo : ¬ CommonTwo K := (chat2_noCommonTwo_iff_bad_channel_one K).2 hBad
  exact hNo (chat2_commonTwo_of_mod9_five_or_six K hK)

/-- Failed relocation is not a future-only propagation goal.  Starting from an
    actual direct `CommonTwo` witness and assuming the next exponent is bad,
    Chat 2's realization exposes an exact physical state one sheet later. -/
theorem chat2_failed_relocation_exposes_physical_state
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    ∃ q : Nat, 2 ≤ q ∧
      directCarry4 (4^(K+1)) q = 3 ∧
      digit3 (4^(K+1)) q = digit3 (4^(K+2)) q ∧
      digit3 (4^(K+1)) q < 2 ∧
      binaryCarry (4^(K+1)) (q+1) = 1 ∧
      (directCarry4 (4^(K+1)) (q+1) = 1 ∨
       directCarry4 (4^(K+1)) (q+1) = 2) := by
  exact commonTwo_failed_relocation_two_step_physical_state K hCommon hNoNext

/-- Conditional final gate for the corrected route: once the counterexample
    language is closed by the affine/exponent-prefix law, the production target
    follows directly.  No `HappyCell` propagation and no monolith axiom occur
    in this bridge. -/
theorem chat2_fourPowerDirectExistence_from_no_counterexample
    (hClosed : ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬¬ CommonTwo K) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  exact Classical.not_not.mp (hClosed K hK5 hK7)

/-- Exact Chat-2 target form: proving production direct existence is equivalent
    to killing the single bad affine channel `B₁` on the orbit of every exponent
    in the required range. -/
theorem chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one :
    FourPowerDirectExistence ↔
      ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K) := by
  constructor
  · intro hDirect K hK5 hK7 hBad
    have hNo : ¬ CommonTwo K := (chat2_noCommonTwo_iff_bad_channel_one K).2 hBad
    exact hNo (hDirect K hK5 hK7)
  · intro hNoBad K hK5 hK7
    by_contra hNo
    exact hNoBad K hK5 hK7 ((chat2_noCommonTwo_iff_bad_channel_one K).1 hNo)

/-- Same closure written as the no-counterexample gate used by the provider
    pipeline.  This is the theorem-level handoff from the roadmap language to
    the affine automaton language. -/
theorem chat2_noCounterexampleClosure_iff_no_bad_affine_channel_one :
    (∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬¬ CommonTwo K) ↔
      ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K) := by
  constructor
  · intro hClosed K hK5 hK7 hBad
    have hNo : ¬ CommonTwo K := (chat2_noCommonTwo_iff_bad_channel_one K).2 hBad
    exact hClosed K hK5 hK7 hNo
  · intro hNoBad K hK5 hK7 hNo
    exact hNoBad K hK5 hK7 ((chat2_noCommonTwo_iff_bad_channel_one K).1 hNo)

#check chat2_commonTwo_iff_affine_channel_one
#check chat2_noCommonTwo_iff_bad_channel_one
#check chat2_first_trit_counterexample_split
#check chat2_commonTwo_of_mod9_five
#check chat2_commonTwo_of_mod9_six
#check chat2_commonTwo_of_mod9_five_or_six
#check chat2_counterexample_obstruction_bundle
#check chat2_bad_affine_channel_one_obstruction_bundle
#check chat2_no_bad_affine_channel_one_of_mod9_five_or_six
#check chat2_failed_relocation_exposes_physical_state
#check chat2_fourPowerDirectExistence_from_no_counterexample
#check chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one
#check chat2_noCounterexampleClosure_iff_no_bad_affine_channel_one
#print axioms chat2_commonTwo_iff_affine_channel_one
#print axioms chat2_noCommonTwo_iff_bad_channel_one
#print axioms chat2_first_trit_counterexample_split
#print axioms chat2_commonTwo_of_mod9_five_or_six
#print axioms chat2_counterexample_obstruction_bundle
#print axioms chat2_bad_affine_channel_one_obstruction_bundle
#print axioms chat2_no_bad_affine_channel_one_of_mod9_five_or_six
#print axioms chat2_failed_relocation_exposes_physical_state
#print axioms chat2_fourPowerDirectExistence_from_no_counterexample
#print axioms chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one
#print axioms chat2_noCounterexampleClosure_iff_no_bad_affine_channel_one

end GSTFourPowerDirectChat2Application
