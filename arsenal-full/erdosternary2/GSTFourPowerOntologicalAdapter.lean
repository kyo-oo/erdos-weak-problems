import GSTCanonicalCarryDynamics

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTFourPowerOntologicalAdapter

open GSTCanonicalTailStateIso
open GSTCanonicalCarryDynamics

/-- Historical CREATE certificate, stated without any monolith dependency. -/
def CreationCertificate (R : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧
    ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
     ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
      R / 3^(p+1) % 3 = 2))

/-- Exact standalone proposition formerly intended to be supplied by
`gst_four_power_creation_certificate_inline`.  It is a dependency, not an axiom. -/
def FourPowerCreationMaster : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → CreationCertificate (4^K)

/-- Navigation-Creation conversion.  The carry-one branch advances one exact
x4/base-3 carry edge and becomes a carry-three Happy gate. -/
theorem creation_certificate_to_navigation
    (R : Nat) (hCreate : CreationCertificate R) : Navigation R := by
  obtain ⟨p, _hp, hdRaw, hcase⟩ := hCreate
  have hd : digit3 R p = 2 := by
    simpa [digit3] using hdRaw
  have hClt : carry4 R p < 4 := carry4_lt_four R p
  rcases hcase with hzero | hone
  · have hCmod : carry4 R p % 3 = 0 := by
      simpa [carry4] using hzero
    have hC : carry4 R p = 0 ∨ carry4 R p = 3 := by omega
    exact ⟨p, hd, hC⟩
  · have hCmod : carry4 R p % 3 = 1 := by
      simpa [carry4] using hone.1
    have hC : carry4 R p = 1 := by
      have hmodlt : carry4 R p % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    have hnext := carry4_forward_exact R p
    have hCnext : carry4 R (p+1) = 3 := by
      rw [hC, hd] at hnext
      norm_num at hnext
      exact hnext
    have hdnext : digit3 R (p+1) = 2 := by
      simpa [digit3] using hone.2
    exact ⟨p+1, hdnext, Or.inr hCnext⟩

/-- FP-NAV, with the exact historical creation theorem exposed as its one
mathematical input. -/
theorem gst_four_power_ontological_navigation_of_master
    (hMaster : FourPowerCreationMaster)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    Navigation (4^K) :=
  creation_certificate_to_navigation (4^K) (hMaster K hK5 hK7)

end GSTFourPowerOntologicalAdapter
