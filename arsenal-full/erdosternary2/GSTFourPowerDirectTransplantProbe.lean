import GSTFourPowerDirectExistenceNoAxiom
import GSTFourPowerDirectCreationMaster

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Isolated transplant probe for the four-power direct-existence seam

This file does not edit the monolith.  It proves the exact production-shaped
objects that the monolith needs, but only from the explicit clean provider:

`∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)`.

The purpose is to certify that the already-green isolated bridge can feed the
creation-master boundary while avoiding the old production-boundary name.
-/

namespace GSTFourPowerDirectTransplantProbe

open GSTFourPowerDirectExistence
open GSTCanonicalTailStateIso

/-- The explicit theorem-backed provider still required before the final
monolith boundary can be deleted. -/
abbrev HappyGeThreeProvider : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ p : Nat, 3 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p)

/-- Production-shaped direct existence, obtained only by applying the isolated
no-axiom bridge. -/
theorem directExistence_from_isolated_noaxiom
    (happy_ge_three : HappyGeThreeProvider) :
    FourPowerDirectExistence := by
  exact
    GSTFourPowerDirectExistenceNoAxiom
      .fourPowerDirectExistence_from_physical_happy_ge_three
      happy_ge_three

/-- Production-shaped creation master obtained from the isolated no-axiom
bridge and the existing direct creation-master adapter. -/
theorem creationMaster_from_isolated_noaxiom
    (happy_ge_three : HappyGeThreeProvider) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := by
  exact
    GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      (directExistence_from_isolated_noaxiom happy_ge_three)

/-- Exact certificate API shape used by the monolith tail, still parameterized
by the explicit clean provider. -/
theorem creationCertificate_from_isolated_noaxiom
    (happy_ge_three : HappyGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact (creationMaster_from_isolated_noaxiom happy_ge_three) K hK5 hK7

#check HappyGeThreeProvider
#check directExistence_from_isolated_noaxiom
#check creationMaster_from_isolated_noaxiom
#check creationCertificate_from_isolated_noaxiom
#print axioms directExistence_from_isolated_noaxiom
#print axioms creationMaster_from_isolated_noaxiom
#print axioms creationCertificate_from_isolated_noaxiom

end GSTFourPowerDirectTransplantProbe
