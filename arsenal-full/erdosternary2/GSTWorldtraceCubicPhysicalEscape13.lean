import GSTWorldtraceCubicBlockLift
import GSTFourPowerDirectExistence
import GSTFourPowerThirdWave
import GSTFourPowerDirectCreationMaster

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST cubic physical third-band common-two breakthrough

At L=3 and multiplier u=13 the first *postcut* overlap is delayed
until the third GST scale band, outside the quadratic-window limit.
The exact physical powers are 4^355 and 4^356. At ternary row p=13
both have digit two, whereas their second-order approximation at this
position predicts (1,1).

The coefficient and quotient arithmetic are certified exactly; the
period identity produces an unbounded family u=13 (mod 59049).
This gives the original thirdWave and creation-certificate bodies on
this new infinite family without a global HGate assumption.
-/

namespace GSTWorldtraceCubicPhysicalEscape13

open GSTWorldtraceCubicBlockLift
open GSTWorldtraceQuadraticBlockLift
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

private theorem coefficient_c3_exact :
    GSTCanonicalTailLTE.lteCoeff 3 = 222399981598543 := by
  decide

private theorem triangle13_exact : triangle 13 = 78 := by decide
private theorem tetra13_exact : tetra 13 = 286 := by decide

/-- Physical source: exact cubic quotient block at ternary position 13. -/
theorem seed13_source_quotient :
    (4^(4+13*3^3)/3^4)%59049 = 43369 := by
  have h := pow4_cubic_window_lift 4 13 3 10 (by decide) (by decide)
  have hprecise :
      (4^(4+13*3^3)/3^4)%59049 =
      (4^4/3^4+13*GSTCanonicalTailLTE.lteCoeff 3*4^4+
        triangle 13*3^4*(GSTCanonicalTailLTE.lteCoeff 3)^2*4^4+
        tetra 13*(3^4)^2*(GSTCanonicalTailLTE.lteCoeff 3)^3*4^4)%59049 := by
    simpa only [show (3:Nat)^10=59049 by decide] using h
  calc
    (4^(4+13*3^3)/3^4)%59049 =
      (4^4/3^4+13*GSTCanonicalTailLTE.lteCoeff 3*4^4+
        triangle 13*3^4*(GSTCanonicalTailLTE.lteCoeff 3)^2*4^4+
        tetra 13*(3^4)^2*(GSTCanonicalTailLTE.lteCoeff 3)^3*4^4)%59049 :=
        hprecise
    _ = 43369 := by
      rw [coefficient_c3_exact,triangle13_exact,tetra13_exact]
      decide

/-- Physical neighbor: exact same-row cubic quotient, not a surrogate. -/
theorem seed13_neighbor_quotient :
    (4^(5+13*3^3)/3^4)%59049 = 55378 := by
  have h := pow4_cubic_window_lift 5 13 3 10 (by decide) (by decide)
  have hprecise :
      (4^(5+13*3^3)/3^4)%59049 =
      (4^5/3^4+13*GSTCanonicalTailLTE.lteCoeff 3*4^5+
        triangle 13*3^4*(GSTCanonicalTailLTE.lteCoeff 3)^2*4^5+
        tetra 13*(3^4)^2*(GSTCanonicalTailLTE.lteCoeff 3)^3*4^5)%59049 := by
    simpa only [show (3:Nat)^10=59049 by decide] using h
  calc
    (4^(5+13*3^3)/3^4)%59049 =
      (4^5/3^4+13*GSTCanonicalTailLTE.lteCoeff 3*4^5+
        triangle 13*3^4*(GSTCanonicalTailLTE.lteCoeff 3)^2*4^5+
        tetra 13*(3^4)^2*(GSTCanonicalTailLTE.lteCoeff 3)^3*4^5)%59049 :=
        hprecise
    _ = 55378 := by
      rw [coefficient_c3_exact,triangle13_exact,tetra13_exact]
      decide

/-- Exact row-13 readback from 10 quotient trits after physical cut 4. -/
private theorem row13_readback
    (M residue : Nat) (hr : residue < 59049)
    (hd : (residue/19683)%3=2)
    (hQ : (4^(M+13*3^3)/3^4)%59049=residue) :
    digit3 (4^(M+13*3^3)) 13=2 := by
  have hmod :
      (4^(M+13*3^3)/3^4)%3^(9+1) =
        residue%3^(9+1) := by
    simpa only [show (3:Nat)^(9+1)=59049 by decide,
      Nat.mod_eq_of_lt hr] using hQ
  have hread : digit3 (4^(M+13*3^3)/3^4) 9 =
      digit3 residue 9 :=
    digit3_eq_of_mod_next _ _ 9 hmod
  have hdigit : digit3 residue 9=2 := by
    simpa only [digit3, show (3:Nat)^9=19683 by decide] using hd
  calc
    digit3 (4^(M+13*3^3)) 13 =
      digit3 (4^(M+13*3^3)/3^4) 9 := by
        unfold digit3
        rw [show (3:Nat)^13=3^4*3^9 by norm_num,
          ← Nat.div_div_eq_div_mul]
    _ = digit3 residue 9 := hread
    _ = 2 := hdigit

/-- Genuine nonlinear third-band collision in the original two perfect
powers at K=355: no HGate postulate is used. -/
theorem cubic_seed13_original_commonTwo : CommonTwo (4+13*3^3) := by
  refine ⟨13, by decide, ?_, ?_⟩
  · exact row13_readback 4 43369
      (by decide) (by decide) seed13_source_quotient
  · have he : (4+13*3^3)+1=5+13*3^3 := by omega
    rw [he]
    exact row13_readback 5 55378
      (by decide) (by decide) seed13_neighbor_quotient

/-- The physical cubic seed repeats at the SAME ternary row for ALL
natural multipliers u congruent 13 mod 59049 (3^10), giving an exact
infinite family of original four-power source-neighbor collisions. -/
theorem cubic_unbounded_multiplier_family
    (u : Nat) (hu : u%59049=13) :
    CommonTwo (4+u*3^3) := by
  have hrepr : u=13+59049*(u/59049) := by
    have h := Nat.mod_add_div u 59049
    omega
  have hp : (59049:Nat)*3^3=3^13 := by norm_num
  have hshape : 4+u*3^3 = (4+13*3^3)+3^13*(u/59049) := by
    calc
      4+u*3^3=4+(13+59049*(u/59049))*3^3 := by
        exact congrArg (fun a : Nat => 4+a*3^3) hrepr
      _ = (4+13*3^3)+3^13*(u/59049) := by
        rw [← hp]
        ring
  have hshape1 :
      (4+u*3^3)+1=(5+13*3^3)+3^13*(u/59049) := by
    omega
  have hs : digit3 (4^(4+13*3^3)) 13=2 :=
    row13_readback 4 43369 (by decide) (by decide) seed13_source_quotient
  have hn : digit3 (4^(5+13*3^3)) 13=2 :=
    row13_readback 5 55378 (by decide) (by decide) seed13_neighbor_quotient
  refine ⟨13, by decide, ?_, ?_⟩
  · rw [hshape]
    exact (pow4_digit_period 13 (4+13*3^3) (u/59049)).trans hs
  · rw [hshape1]
    exact (pow4_digit_period 13 (5+13*3^3) (u/59049)).trans hn

/-- Exact historical thirdWave body, without the global third-wave gate. -/
theorem cubic_family_original_thirdWave
    (u : Nat) (hu : u%59049=13) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^3) := by
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact cubic_unbounded_multiplier_family u hu

/-- Exact historical GST creation certificate on this new family. -/
theorem cubic_family_original_creation_certificate
    (u : Nat) (hu : u%59049=13) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^(4+u*3^3)) := by
  apply GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate
  exact cubic_unbounded_multiplier_family u hu

#print axioms seed13_source_quotient
#print axioms seed13_neighbor_quotient
#print axioms cubic_unbounded_multiplier_family
#print axioms cubic_family_original_thirdWave
#print axioms cubic_family_original_creation_certificate

end GSTWorldtraceCubicPhysicalEscape13
