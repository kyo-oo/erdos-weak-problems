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


/-- The historical creation certificate is also sufficient for a direct
common-two witness.  Its zero-carry branch fires at the same row; its
carry-one branch advances one exact multiplication edge and fires at the
next row with carry three. -/
theorem creation_certificate_to_commonTwo
    (K : Nat) (h : CreationCertificate (4^K)) :
    CommonTwo K := by
  rcases h with ⟨p, hp, hsrcRaw, hcase⟩
  have hsrc : digit3 (4^K) p = 2 := by
    simpa [GSTFourPowerDirectResidue.digit3] using hsrcRaw
  rcases hcase with hzero | hone
  · have hCmod : directCarry4 (4^K) p % 3 = 0 := by
      simpa [directCarry4] using hzero
    have hClt := directCarry4_lt_four (4^K) p
    have hC : directCarry4 (4^K) p = 0 ∨
        directCarry4 (4^K) p = 3 := by
      omega
    have ht := digit3_four_mul (4^K) p
    rw [hsrc] at ht
    rcases hC with hC0 | hC3
    · rw [hC0] at ht
      norm_num at ht
      refine ⟨p, hp, hsrc, ?_⟩
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
    · rw [hC3] at ht
      norm_num at ht
      refine ⟨p, hp, hsrc, ?_⟩
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
  · have hCmod : directCarry4 (4^K) p % 3 = 1 := by
      simpa [directCarry4] using hone.1
    have hClt := directCarry4_lt_four (4^K) p
    have hC : directCarry4 (4^K) p = 1 := by
      omega
    have hnext := directCarry4_forward_exact_all (4^K) p
    rw [hC, hsrc] at hnext
    norm_num at hnext
    have hsrcNext : digit3 (4^K) (p+1) = 2 := by
      simpa [GSTFourPowerDirectResidue.digit3] using hone.2
    have ht := digit3_four_mul (4^K) (p+1)
    rw [hsrcNext, hnext] at ht
    norm_num at ht
    refine ⟨p+1, by omega, hsrcNext, ?_⟩
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht

/-- **EXACT CREATION INTERFACE.**  Direct common-two arithmetic and the
historical creation certificate are the same proposition for every exponent. -/
theorem commonTwo_iff_creation_certificate (K : Nat) :
    CommonTwo K ↔ CreationCertificate (4^K) :=
  ⟨commonTwo_to_creation_certificate K,
    creation_certificate_to_commonTwo K⟩


/-- The direct arithmetic existence theorem supplies the exact historical
four-power creation master.  This is the production-facing replacement for the
old collision/navigation route. -/
theorem directExistence_to_creation_master
    (hDirect : FourPowerDirectExistence) :
    FourPowerCreationMaster := by
  intro K hK5 hK7
  exact commonTwo_to_creation_certificate K (hDirect K hK5 hK7)


/-- The universal direct-existence surface and the historical creation master
are therefore exactly equivalent, not merely connected by a one-way adapter. -/
theorem directExistence_iff_creation_master :
    FourPowerDirectExistence ↔ FourPowerCreationMaster := by
  constructor
  · exact directExistence_to_creation_master
  · intro hMaster K hK5 hK7
    exact creation_certificate_to_commonTwo K (hMaster K hK5 hK7)


#check commonTwo_to_creation_certificate
#check directExistence_to_creation_master
#check creation_certificate_to_commonTwo
#check commonTwo_iff_creation_certificate
#check directExistence_iff_creation_master
#print axioms commonTwo_to_creation_certificate
#print axioms directExistence_to_creation_master
#print axioms commonTwo_iff_creation_certificate
#print axioms directExistence_iff_creation_master

end GSTFourPowerDirectCreationMaster