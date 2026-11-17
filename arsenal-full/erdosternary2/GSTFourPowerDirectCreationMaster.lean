import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectExistence
import GSTFourPowerDirectAdditionCarry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectCreationMaster

open GSTFourPowerOntologicalAdapter
open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry

/-- A direct common-two row is already exactly the historical creation
certificate on the source four-power.  This is the positive algebraic bridge:
the source row has digit two, and the target digit-two equation forces the
multiplication carry to be zero modulo three.  No navigation, collision, or
phase-window contradiction is used. -/
theorem commonTwo_to_creation_certificate
    (K : Nat) (h : CommonTwo K) :
    CreationCertificate (4^K) := by
  rcases h with ⟨p, hp, hsrc, htgt⟩
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [GSTFourPowerDirectResidue.digit3] using hsrc
  · have htgtMul : digit3 (4 * (4^K)) p = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using htgt
    have hformula := digit3_four_mul (4^K) p
    rw [hsrc, htgtMul] at hformula
    let c := directCarry4 (4^K) p
    have hcLt : c < 4 := by
      dsimp [c]
      exact directCarry4_lt_four (4^K) p
    have hcEq : (2 + c) % 3 = 2 := by
      dsimp [c]
      exact hformula.symm
    have hcMod : c % 3 = 0 := by
      interval_cases c
      · norm_num
      · norm_num at hcEq
      · norm_num at hcEq
      · norm_num
    left
    dsimp [c] at hcMod
    simpa [directCarry4] using hcMod

/-- The direct arithmetic existence theorem supplies the exact historical
four-power creation master.  This is the production-facing replacement for the
old collision/navigation route. -/
theorem directExistence_to_creation_master
    (hDirect : FourPowerDirectExistence) :
    FourPowerCreationMaster := by
  intro K hK5 hK7
  exact commonTwo_to_creation_certificate K (hDirect K hK5 hK7)

#check commonTwo_to_creation_certificate
#check directExistence_to_creation_master
#print axioms commonTwo_to_creation_certificate
#print axioms directExistence_to_creation_master

end GSTFourPowerDirectCreationMaster