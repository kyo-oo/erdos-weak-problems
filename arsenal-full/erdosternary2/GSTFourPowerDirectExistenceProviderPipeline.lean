import GSTFourPowerDirectExistenceNoAxiom
import GSTFourPowerDirectCreationMaster
import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectChat2Application
import GSTFourPowerHappyProvider

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Provider pipeline for replacing the four-power direct-existence boundary

This file is the controlled next phase after the isolated bridge compiled green.
It does not edit the monolith and adds no unchecked proof hole.

It now exposes the legitimate proof gates:

* `FourPowerHappyGeThreeProvider`, the physical Happy-row provider originally
  needed by the isolated bridge;
* `FourPowerCommonTwoGeThreeProvider`, the sharpened monolith-mined provider:
  direct common-two witnesses already forced at rows `p ≥ 3`;
* `FourPowerDirectNoCounterexampleClosure`, the direct `CommonTwo`
  counterexample closure; and
* `FourPowerDirectNoBadAffineChannelOne`, the Chat-2 realization: the final
  production target is exactly the claim that bad affine channel `B₁` never
  occurs on `affineOrbit K` for `K ≥ 5`, `K ≠ 7`.

The third/fourth gates are the corrected roadmap route.  The new Happy provider
bridge avoids the abandoned future-only propagation path and does not import the
unresolved infinite-navigation collision file.
-/

namespace GSTFourPowerDirectExistenceProviderPipeline

open GSTFourPowerDirectExistence
open GSTFourPowerDirectExistenceNoAxiom
open GSTFourPowerDirectChat2Application
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton

/-- Goal A: a theorem-backed physical Happy-row provider for every `K ≥ 8`.
This is sufficient for the already-green bridge, but it is not the only route. -/
def FourPowerHappyGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

/-- Goal A′: the sharpened direct witness provider mined from the monolith:
a common-two witness already above the first two rows.  This is exactly the
missing bridge input for the requested physical Happy provider. -/
def FourPowerCommonTwoGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K → GSTFourPowerHappyProvider.CommonTwoGeThree K

/-- Goal B: close the direct arithmetic counterexample language.
This is the productive route after the failed future-only relocation subgoal:
prove there is no genuine `CommonTwo` counterexample for `K ≥ 5`, except the
single excluded exponent `7`. -/
def FourPowerDirectNoCounterexampleClosure : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬¬ CommonTwo K

/-- Goal C / Chat-2 gate: kill exactly the bad affine channel that is equivalent
    to a direct `CommonTwo` counterexample. -/
def FourPowerDirectNoBadAffineChannelOne : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)

/-- Monolith-mined provider gate: once row-three-or-higher direct common-two
witnesses are mined, the physical Happy-row provider follows immediately. -/
theorem fourPowerHappyGeThreeProvider_from_commonTwoGeThree
    (hProvider : FourPowerCommonTwoGeThreeProvider) :
    FourPowerHappyGeThreeProvider := by
  intro K hK
  exact
    GSTFourPowerHappyProvider.four_power_happy_ge_three_from_commonTwoGeThree
      hProvider K hK

/-- The already-green isolated bridge converts Goal A into the closed
`FourPowerDirectExistence` theorem. -/
theorem fourPowerDirectExistence_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    FourPowerDirectExistence := by
  exact fourPowerDirectExistence_from_physical_happy_ge_three hProvider

/-- Direct-existence route from the sharpened monolith-mined row-three-or-higher
provider. -/
theorem fourPowerDirectExistence_noAxiom_from_commonTwoGeThree
    (hProvider : FourPowerCommonTwoGeThreeProvider) :
    FourPowerDirectExistence := by
  exact
    fourPowerDirectExistence_noAxiom_from_provider
      (fourPowerHappyGeThreeProvider_from_commonTwoGeThree hProvider)

/-- Chat-2 production gate in `CommonTwo` language: once the counterexample
language is closed, the direct universal theorem follows immediately. -/
theorem fourPowerDirectExistence_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure) :
    FourPowerDirectExistence := by
  exact chat2_fourPowerDirectExistence_from_no_counterexample hClosed

/-- Chat-2 production gate in the final affine-automaton language. -/
theorem fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
    (hNoBad : FourPowerDirectNoBadAffineChannelOne) :
    FourPowerDirectExistence := by
  exact chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one.mpr hNoBad

/-- The two Chat-2 closure formulations are definitionally the same target via
    the clean bad-channel equivalence. -/
theorem chat2_counterexample_closure_iff_no_bad_affine_channel_one :
    FourPowerDirectNoCounterexampleClosure ↔ FourPowerDirectNoBadAffineChannelOne := by
  exact chat2_noCounterexampleClosure_iff_no_bad_affine_channel_one

/-- Chat-2 obstruction export: every attempted counterexample now carries the
combined row-two, row-three, row-four, and parametric exponent-prefix
obstructions from the direct theorem layer. -/
theorem chat2_counterexample_obstruction_from_pipeline
    (K : Nat) (hNo : ¬ CommonTwo K) :
    (K % 9 ≠ 5 ∧ K % 9 ≠ 6) ∧
    (K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧ K % 27 ≠ 19 ∧ K % 27 ≠ 25) ∧
    (¬ GSTFourPowerDirectResidue81.RowFourClass (K % 81)) ∧
    (∀ p : Nat,
      GSTFourPowerDirectResidue.digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
        GSTFourPowerDirectResidue.digit3 (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1) →
      GSTFourPowerExponentTritObstruction.exponentTrit K p ≠
        2 - GSTFourPowerDirectResidue.digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1)) := by
  exact chat2_counterexample_obstruction_bundle K hNo

/-- Once Goal A is theorem-backed, the existing direct creation master follows
without the old production boundary. -/
theorem fourPowerCreationMaster_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_provider hProvider)

/-- Creation master route from the sharpened monolith-mined row-three-or-higher
provider. -/
theorem fourPowerCreationMaster_noAxiom_from_commonTwoGeThree
    (hProvider : FourPowerCommonTwoGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_commonTwoGeThree hProvider)

/-- Chat-2 creation master route from direct `CommonTwo` closure. -/
theorem fourPowerCreationMaster_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_chat2_closure hClosed)

/-- Chat-2 creation master route from the exact no-bad-affine-channel target. -/
theorem fourPowerCreationMaster_noAxiom_from_no_bad_affine_channel_one
    (hNoBad : FourPowerDirectNoBadAffineChannelOne) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one hNoBad)

/-- Transplant-ready certificate wrapper for the original Happy-provider gate. -/
theorem fourPowerCreationCertificate_noAxiom_from_provider
    (hProvider : FourPowerHappyGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_provider hProvider) K hK5 hK7

/-- Transplant-ready certificate wrapper for the sharpened monolith-mined
row-three-or-higher provider. -/
theorem fourPowerCreationCertificate_noAxiom_from_commonTwoGeThree
    (hProvider : FourPowerCommonTwoGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_commonTwoGeThree hProvider) K hK5 hK7

/-- Transplant-ready certificate wrapper for the Chat-2 direct closure gate. -/
theorem fourPowerCreationCertificate_noAxiom_from_chat2_closure
    (hClosed : FourPowerDirectNoCounterexampleClosure)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_chat2_closure hClosed) K hK5 hK7

/-- Transplant-ready certificate wrapper for the exact no-bad-affine-channel
    Chat-2 gate. -/
theorem fourPowerCreationCertificate_noAxiom_from_no_bad_affine_channel_one
    (hNoBad : FourPowerDirectNoBadAffineChannelOne)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (fourPowerCreationMaster_noAxiom_from_no_bad_affine_channel_one hNoBad) K hK5 hK7

#check FourPowerHappyGeThreeProvider
#check FourPowerCommonTwoGeThreeProvider
#check FourPowerDirectNoCounterexampleClosure
#check FourPowerDirectNoBadAffineChannelOne
#check fourPowerHappyGeThreeProvider_from_commonTwoGeThree
#check fourPowerDirectExistence_noAxiom_from_provider
#check fourPowerDirectExistence_noAxiom_from_commonTwoGeThree
#check fourPowerDirectExistence_noAxiom_from_chat2_closure
#check fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
#check chat2_counterexample_closure_iff_no_bad_affine_channel_one
#check chat2_counterexample_obstruction_from_pipeline
#check fourPowerCreationMaster_noAxiom_from_provider
#check fourPowerCreationMaster_noAxiom_from_commonTwoGeThree
#check fourPowerCreationMaster_noAxiom_from_chat2_closure
#check fourPowerCreationMaster_noAxiom_from_no_bad_affine_channel_one
#check fourPowerCreationCertificate_noAxiom_from_provider
#check fourPowerCreationCertificate_noAxiom_from_commonTwoGeThree
#check fourPowerCreationCertificate_noAxiom_from_chat2_closure
#check fourPowerCreationCertificate_noAxiom_from_no_bad_affine_channel_one
#print axioms fourPowerHappyGeThreeProvider_from_commonTwoGeThree
#print axioms fourPowerDirectExistence_noAxiom_from_provider
#print axioms fourPowerDirectExistence_noAxiom_from_commonTwoGeThree
#print axioms fourPowerDirectExistence_noAxiom_from_chat2_closure
#print axioms fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
#print axioms chat2_counterexample_closure_iff_no_bad_affine_channel_one
#print axioms chat2_counterexample_obstruction_from_pipeline
#print axioms fourPowerCreationMaster_noAxiom_from_provider
#print axioms fourPowerCreationMaster_noAxiom_from_commonTwoGeThree
#print axioms fourPowerCreationMaster_noAxiom_from_chat2_closure
#print axioms fourPowerCreationMaster_noAxiom_from_no_bad_affine_channel_one
#print axioms fourPowerCreationCertificate_noAxiom_from_provider
#print axioms fourPowerCreationCertificate_noAxiom_from_commonTwoGeThree
#print axioms fourPowerCreationCertificate_noAxiom_from_chat2_closure
#print axioms fourPowerCreationCertificate_noAxiom_from_no_bad_affine_channel_one

end GSTFourPowerDirectExistenceProviderPipeline
