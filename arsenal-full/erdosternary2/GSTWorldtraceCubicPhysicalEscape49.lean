import GSTWorldtraceCubicBlockLift
import GSTFourPowerDirectExistence
import GSTFourPowerThirdWave
import GSTFourPowerDirectCreationMaster

set_option maxRecDepth 1000000
set_option maxHeartbeats 60000000

/-!
# Third-band GST physical proof at a NONTRIVIAL high scale

The original perfect powers 4^35725 and 4^35726 have simultaneous
ternary digit 2 at row 27. This specific collision requires the exact
third-order Worldtrace carry: linear and quadratic truncations do not
have the same digit pair at that position.

L=6, u=49, M=4 and 5, T=3^7, w=21, row p=L+1+20=27.
The exact cubic polynomial gives source residue 7080391750 and
neighbor residue 7400860594 modulo 3^21=10460353203.
The result extends to every unbounded multiplier u=49 (mod 3^21).
-/

namespace GSTWorldtraceCubicPhysicalEscape49

open GSTWorldtraceCubicBlockLift
open GSTWorldtraceQuadraticBlockLift
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

private theorem triangle49_exact : triangle 49=1176 := by decide
private theorem tetra49_exact : tetra 49=18424 := by decide

private theorem source_cubic_word_exact :
    (4^(4+49*3^6)/3^7)%10460353203=7080391750 := by
  have h := pow4_cubic_window_lift 4 49 6 21 (by decide) (by decide)
  calc
    (4^(4+49*3^6)/3^7)%10460353203 =
        (4^4/3^7+
          49*GSTCanonicalTailLTE.lteCoeff 6*4^4+
          triangle 49*3^7*(GSTCanonicalTailLTE.lteCoeff 6)^2*4^4+
          tetra 49*(3^7)^2*(GSTCanonicalTailLTE.lteCoeff 6)^3*4^4)%
          10460353203 := by
            simpa only [show (3:Nat)^21=10460353203 by decide] using h
    _ = 7080391750 := by
          rw [triangle49_exact,tetra49_exact]
          norm_num [GSTCanonicalTailLTE.lteCoeff]

private theorem neighbor_cubic_word_exact :
    (4^(5+49*3^6)/3^7)%10460353203=7400860594 := by
  have h := pow4_cubic_window_lift 5 49 6 21 (by decide) (by decide)
  calc
    (4^(5+49*3^6)/3^7)%10460353203 =
        (4^5/3^7+
          49*GSTCanonicalTailLTE.lteCoeff 6*4^5+
          triangle 49*3^7*(GSTCanonicalTailLTE.lteCoeff 6)^2*4^5+
          tetra 49*(3^7)^2*(GSTCanonicalTailLTE.lteCoeff 6)^3*4^5)%
          10460353203 := by
            simpa only [show (3:Nat)^21=10460353203 by decide] using h
    _ = 7400860594 := by
          rw [triangle49_exact,tetra49_exact]
          norm_num [GSTCanonicalTailLTE.lteCoeff]

private theorem physical_row27_readback
    (M r : Nat) (hr : r<10460353203)
    (hd : (r/3486784401)%3=2)
    (hQ : (4^(M+49*3^6)/3^7)%10460353203=r) :
    digit3 (4^(M+49*3^6)) 27=2 := by
  have hmod :
      (4^(M+49*3^6)/3^7)%3^(20+1)=r%3^(20+1) := by
    simpa only [show (3:Nat)^(20+1)=10460353203 by decide,
      Nat.mod_eq_of_lt hr] using hQ
  have hread : digit3 (4^(M+49*3^6)/3^7) 20 =
      digit3 r 20 :=
    digit3_eq_of_mod_next _ _ 20 hmod
  have htwo : digit3 r 20=2 := by
    simpa only [digit3,show (3:Nat)^20=3486784401 by decide] using hd
  calc
    digit3 (4^(M+49*3^6)) 27 =
      digit3 (4^(M+49*3^6)/3^7) 20 := by
        unfold digit3
        rw [show (3:Nat)^27=3^7*3^20 by norm_num,
          ← Nat.div_div_eq_div_mul]
    _ = digit3 r 20 := hread
    _ = 2 := htwo

/-- Third-band exact original common-two event at exponent K=35725. -/
theorem cubic_seed49_physical_CommonTwo :
    CommonTwo (4+49*3^6) := by
  refine ⟨27, by decide, ?_, ?_⟩
  · exact physical_row27_readback 4 7080391750
      (by decide) (by decide) source_cubic_word_exact
  · have he : (4+49*3^6)+1=5+49*3^6 := by omega
    rw [he]
    exact physical_row27_readback 5 7400860594
      (by decide) (by decide) neighbor_cubic_word_exact

/-- UNBOUNDED original physical perfect-power source family at scale 6,
with exact cubic row 27. Every multiplier is represented,
not merely tested over a finite range. -/
theorem cubic_unbounded_high_scale_family
    (u : Nat) (hu : u%10460353203=49) :
    CommonTwo (4+u*3^6) := by
  have hrepr : u=49+10460353203*(u/10460353203) := by
    have hh := Nat.mod_add_div u 10460353203
    omega
  have hp : (10460353203:Nat)*3^6=3^27 := by norm_num
  have hshape :
      4+u*3^6=(4+49*3^6)+3^27*(u/10460353203) := by
    calc
      4+u*3^6=4+(49+10460353203*(u/10460353203))*3^6 := by
        exact congrArg (fun a : Nat => 4+a*3^6) hrepr
      _=(4+49*3^6)+3^27*(u/10460353203) := by
        rw [← hp]
        ring
  have hshape1 :
      (4+u*3^6)+1=(5+49*3^6)+3^27*(u/10460353203) := by omega
  have hs : digit3 (4^(4+49*3^6)) 27=2 :=
    physical_row27_readback 4 7080391750
      (by decide) (by decide) source_cubic_word_exact
  have hn : digit3 (4^(5+49*3^6)) 27=2 :=
    physical_row27_readback 5 7400860594
      (by decide) (by decide) neighbor_cubic_word_exact
  refine ⟨27, by decide, ?_, ?_⟩
  · rw [hshape]
    exact (pow4_digit_period 27 (4+49*3^6)
      (u/10460353203)).trans hs
  · rw [hshape1]
    exact (pow4_digit_period 27 (5+49*3^6)
      (u/10460353203)).trans hn

theorem cubic_high_scale_original_thirdWave
    (u : Nat) (hu : u%10460353203=49) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^6) := by
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact cubic_unbounded_high_scale_family u hu

theorem cubic_high_scale_original_creation_certificate
    (u : Nat) (hu : u%10460353203=49) :
    GSTFourPowerOntologicalAdapter.CreationCertificate
      (4^(4+u*3^6)) := by
  apply GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate
  exact cubic_unbounded_high_scale_family u hu

#print axioms cubic_seed49_physical_CommonTwo
#print axioms cubic_unbounded_high_scale_family
#print axioms cubic_high_scale_original_thirdWave
#print axioms cubic_high_scale_original_creation_certificate

end GSTWorldtraceCubicPhysicalEscape49
