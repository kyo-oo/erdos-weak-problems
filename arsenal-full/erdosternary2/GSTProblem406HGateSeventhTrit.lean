import GSTProblem406HGateCoreClass
import GSTProblem406HGateCoreIntegration

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Worldtrace seventh postcut row: 58 new unbounded CommonTwo families

Original physical source: 4^(4+u*3^L).
Original physical neighbor: 4^(5+u*3^L).
This file proves same-row digit-two pairs for all L≥6 and ALL natural
multipliers in 58 residue classes modulo 2187, at physical row L+7.

The proof uses the existing exact GST source+neighbor two-wave block
transport and the stabilized LTE coefficient. Its finite arithmetic
only classifies multiplier residues, not bounded physical exponents.
No new universal hGate assumption is introduced.

The universal third-wave gate for every K≥5 except K=7 is not
concluded from these families.
-/

namespace GSTProblem406HGateSeventhTrit

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTProblem406HGateCoreClass

/-- Exact seventh Worldtrace coefficient at every unbounded scale L≥6. -/
theorem lteCoeff_mod2187_664 (L : Nat) (hL : 6 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 2187 = 664 := by
  have hstep (t : Nat) (ht : 6 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 2187 =
        GSTCanonicalTailLTE.lteCoeff t % 2187 := by
    have hdiv : 2187 ∣ 3^(t+1) := by
      have hd : 3^7 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^7 = 2187 by decide] using hd
    calc
      GSTCanonicalTailLTE.lteCoeff (t+1) % 2187 =
          (GSTCanonicalTailLTE.lteCoeff (t+1) % 3^(t+1)) % 2187 :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (GSTCanonicalTailLTE.lteCoeff t % 3^(t+1)) % 2187 := by
            rw [GSTWorldtraceCoeffStability.coeff_step_mod]
      _ = GSTCanonicalTailLTE.lteCoeff t % 2187 :=
            Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ k : Nat,
      GSTCanonicalTailLTE.lteCoeff (6+k) % 2187 = 664 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 6+(k+1)=(6+k)+1 by omega]
        rw [hstep (6+k) (by omega)]
        exact ih
  rw [show L=6+(L-6) by omega]
  exact hbase (L-6)

/-- All unbounded multipliers: exact reduction of a two-wave
physical Worldtrace coefficient to its seventh-trit residue. -/
private theorem coefficient_product_mod2187
    (L u M m : Nat) (hL : 6 ≤ L)
    (hm : (664*M)%2187=m) :
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%2187=(m*u)%2187 := by
  have hc : (GSTCanonicalTailLTE.lteCoeff L*M)%2187=m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*M)%2187 =
        ((GSTCanonicalTailLTE.lteCoeff L%2187)*(M%2187))%2187 :=
          Nat.mul_mod _ _ _
      _ = (664*M)%2187 := by
          rw [lteCoeff_mod2187_664 L hL]
          simpa using (Nat.mul_mod 664 M 2187).symm
      _ = m := hm
  calc
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%2187 =
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%2187 := by ring
    _ = (u*m)%2187 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%2187 =
          ((u%2187)*((GSTCanonicalTailLTE.lteCoeff L*M)%2187))%2187 :=
            Nat.mul_mod _ _ _
        _ = ((u%2187)*m)%2187 := by rw [hc]
        _ = (u*m)%2187 := by
              simpa using (Nat.mul_mod u m 2187).symm
    _ = (m*u)%2187 := by ac_rfl

/-- Exactly 58 previously uncovered multiplier residues whose first
new simultaneous two occurs in seventh postcut trit. -/
def SeventhNewClass (r : Nat) : Prop :=
  r=22 ∨
  r=52 ∨
  r=70 ∨
  r=160 ∨
  r=211 ∨
  r=259 ∨
  r=280 ∨
  r=310 ∨
  r=328 ∨
  r=349 ∨
  r=397 ∨
  r=418 ∨
  r=448 ∨
  r=517 ∨
  r=535 ∨
  r=556 ∨
  r=586 ∨
  r=724 ∨
  r=745 ∨
  r=775 ∨
  r=793 ∨
  r=814 ∨
  r=862 ∨
  r=883 ∨
  r=913 ∨
  r=1021 ∨
  r=1051 ∨
  r=1072 ∨
  r=1120 ∨
  r=1171 ∨
  r=1210 ∨
  r=1240 ∨
  r=1258 ∨
  r=1279 ∨
  r=1309 ∨
  r=1327 ∨
  r=1348 ∨
  r=1396 ∨
  r=1447 ∨
  r=1537 ∨
  r=1585 ∨
  r=1606 ∨
  r=1636 ∨
  r=1705 ∨
  r=1723 ∨
  r=1744 ∨
  r=1774 ∨
  r=1813 ∨
  r=1861 ∨
  r=1882 ∨
  r=1912 ∨
  r=1933 ∨
  r=1981 ∨
  r=2050 ∨
  r=2071 ∨
  r=2101 ∨
  r=2119 ∨
  r=2170

/-- Finite residue verification, NOT a scan of natural exponents. -/
private theorem seventh_new_classes_kernel
    (r : Nat) (hr : SeventhNewClass r) :
    digit3 (1585*r) 6=2 ∧ digit3 (1966*r) 6=2 := by
  unfold SeventhNewClass at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r <;> norm_num [digit3]

/-- Genuine same-row CommonTwo: for ALL scales L≥6 and unbounded
multipliers u in any of the 58 new classes modulo 3^7, both
physical powers have ternary digit 2 at row L+7. -/
theorem commonTwo_new_seventh_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : SeventhNewClass (u%2187)) :
    CommonTwo (4+u*3^L) := by
  have hpair := seventh_new_classes_kernel (u%2187) hu
  have hsource_mod : digit3 (1585*u) 6 =
      digit3 (1585*(u%2187)) 6 := by
    apply digit3_eq_of_mod_next
    change (1585*u)%2187=(1585*(u%2187))%2187
    simp [Nat.mul_mod]
  have hneighbor_mod : digit3 (1966*u) 6 =
      digit3 (1966*(u%2187)) 6 := by
    apply digit3_eq_of_mod_next
    change (1966*u)%2187=(1966*(u%2187))%2187
    simp [Nat.mul_mod]
  have hsource : digit3 (1585*u) 6=2 := by
    rw [hsource_mod]
    exact hpair.1
  have hneighbor : digit3 (1966*u) 6=2 := by
    rw [hneighbor_mod]
    exact hpair.2
  have hreadsource :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*256) 6 =
        digit3 (1585*u) 6 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(6+1)=2187 by decide] using
      (coefficient_product_mod2187 L u 256 1585 hL (by norm_num))
  have hreadneighbor :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*1024) 6 =
        digit3 (1966*u) 6 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(6+1)=2187 by decide] using
      (coefficient_product_mod2187 L u 1024 1966 hL (by norm_num))
  apply two_wave_any_width_certificate_to_CommonTwo L u 7 6
    hL (by decide) (by omega) (by decide)
  · rw [hreadsource]
    exact hsource
  · rw [hreadneighbor]
    exact hneighbor

/-- Transfer directly into the ORIGINAL thirdWave gate body. -/
theorem original_thirdWave_new_seventh_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : SeventhNewClass (u%2187)) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^L) := by
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact commonTwo_new_seventh_trit_classes L u hL hu

/-- Transfer directly into the original CreationCertificate, without
any generic or universal hGate premise. -/
theorem original_creation_new_seventh_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : SeventhNewClass (u%2187)) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^(4+u*3^L)) := by
  apply GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate
  exact commonTwo_new_seventh_trit_classes L u hL hu

#print axioms lteCoeff_mod2187_664
#print axioms commonTwo_new_seventh_trit_classes
#print axioms original_thirdWave_new_seventh_trit_classes
#print axioms original_creation_new_seventh_trit_classes

end GSTProblem406HGateSeventhTrit
