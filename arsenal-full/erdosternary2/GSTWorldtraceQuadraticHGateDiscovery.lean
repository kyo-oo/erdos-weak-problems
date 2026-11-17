import GSTWorldtraceQuadraticBlockLift
import GSTProblem406HGateCoreIntegration

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
# Exact nonlinear GST HGate: first second-band physical collision

At L=6, u=31, the physical pair 4^(4+u*3^6),
4^(5+u*3^6) has NO SAME-ROW digit two in any of the first EIGHT
post-cut positions. At the next row p=15, the linear Worldtrace
extrapolation gives digit pair (0,0), but the quadratic correction
makes it (2,2).

The exact quadratic transport is used to certify the seed. Exact
periodicity of PHYSICAL powers turns it into an unbounded family
u == 31 (mod 19683), without a global hGate hypothesis.
-/

namespace GSTWorldtraceQuadraticHGateDiscovery

open GSTWorldtraceQuadraticBlockLift
open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Certified physical seed coefficient at the nonlinear scale. -/
private theorem c6_mod19683 :
    GSTCanonicalTailLTE.lteCoeff 6%19683=7225 := by
  decide

/-- The GST quadratic output polynomial depends only on the coefficient's
modulo-19683 fingerprint, not on its gigantic original tower value. -/
private theorem seed31_quadratic_polynomial_mod (A : Nat) :
    (31*GSTCanonicalTailLTE.lteCoeff 6*A +
       triangle 31*2187*(GSTCanonicalTailLTE.lteCoeff 6)^2*A)%19683 =
    (31*7225*A+465*2187*7225^2*A)%19683 := by
  have htri : triangle 31=465 := by decide
  rw [htri]
  let q := GSTCanonicalTailLTE.lteCoeff 6 / 19683
  have hcRepr :
      GSTCanonicalTailLTE.lteCoeff 6=7225+19683*q := by
    have hd := Nat.mod_add_div (GSTCanonicalTailLTE.lteCoeff 6) 19683
    dsimp [q]
    rw [c6_mod19683] at hd
    omega
  calc
    (31*GSTCanonicalTailLTE.lteCoeff 6*A +
      465*2187*(GSTCanonicalTailLTE.lteCoeff 6)^2*A)%19683 =
        (31*(7225+19683*q)*A+
          465*2187*(7225+19683*q)^2*A)%19683 := by rw [hcRepr]
    _ = ((31*7225*A+465*2187*7225^2*A)+
          19683*(31*q*A+465*2187*(2*7225*q+19683*q^2)*A))%19683 := by
            congr 1
            ring
    _ = (31*7225*A+465*2187*7225^2*A)%19683 := by
          rw [Nat.add_mul_mod_self_left]

/-- Source and neighboring full powers share an exact quadratic seed
certificate, with only small modular arithmetic remaining. -/
private theorem seed31_quotient_mod (M A answer : Nat)
    (hM : 4^M=A) (hDiv : A/2187=0)
    (hcalc :
      (31*7225*A+465*2187*7225^2*A)%19683=answer) :
    (4^(M+31*3^6)/3^7)%19683=answer := by
  have hquad :=
    pow4_quadratic_window_lift M 31 6 9 (by decide) (by decide)
  calc
    (4^(M+31*3^6)/3^7)%19683 =
      (4^M/3^7 +
        31*GSTCanonicalTailLTE.lteCoeff 6*4^M +
        triangle 31*3^7*(GSTCanonicalTailLTE.lteCoeff 6)^2*4^M)%19683 := by
          simpa only [show (3:Nat)^9=19683 by decide,
            show (3:Nat)^7=2187 by decide] using hquad
    _ =
      (31*GSTCanonicalTailLTE.lteCoeff 6*A +
        triangle 31*2187*(GSTCanonicalTailLTE.lteCoeff 6)^2*A)%19683 := by
          rw [hM]
          norm_num [hDiv]
    _ = (31*7225*A+465*2187*7225^2*A)%19683 :=
      seed31_quadratic_polynomial_mod A
    _ = answer := hcalc

theorem seed31_source_mod19683 :
    (4^(4+31*3^6)/3^7)%19683=14143 :=
  seed31_quotient_mod 4 256 14143 (by decide) (by decide) (by decide)

theorem seed31_neighbor_mod19683 :
    (4^(5+31*3^6)/3^7)%19683=17206 :=
  seed31_quotient_mod 5 1024 17206 (by decide) (by decide) (by decide)

/-- The 9th quotient trit is the physical row 15, with no rounding
errors or auxiliary abstract surrogate. -/
private theorem read_seed31_ninth_trit
    (M r : Nat)
    (hR : r<19683)
    (hr : (r/6561)%3=2)
    (hQ : (4^(M+31*3^6)/3^7)%19683=r) :
    digit3 (4^(M+31*3^6)) 15=2 := by
  have hm : (4^(M+31*3^6)/3^7)%3^(8+1)=r%3^(8+1) := by
    simpa only [show (3:Nat)^(8+1)=19683 by decide,
      Nat.mod_eq_of_lt hR] using hQ
  have hread : digit3 (4^(M+31*3^6)/3^7) 8=digit3 r 8 :=
    digit3_eq_of_mod_next _ _ 8 hm
  have hright : digit3 r 8=2 := by
    simpa only [digit3,show (3:Nat)^8=6561 by decide] using hr
  calc
    digit3 (4^(M+31*3^6)) 15 =
      digit3 (4^(M+31*3^6)/3^7) 8 := by
        unfold digit3
        rw [show (3:Nat)^15=3^7*3^8 by norm_num,
          ← Nat.div_div_eq_div_mul]
    _ = digit3 r 8 := hread
    _ = 2 := hright

/-- New EXACT quadratic physical HGate at K=22603 and K+1=22604:
the linear approximation gives two zero trits, while the quadratic
correction provides two actual digit-two trits at row 15. -/
theorem seed31_nonlinear_physical_CommonTwo :
    CommonTwo (4+31*3^6) := by
  refine ⟨15, by decide, ?_, ?_⟩
  · exact read_seed31_ninth_trit 4 14143
      (by decide) (by decide) seed31_source_mod19683
  · have he : (4+31*3^6)+1=5+31*3^6 := by omega
    rw [he]
    exact read_seed31_ninth_trit 5 17206
      (by decide) (by decide) seed31_neighbor_mod19683

/-- Unbounded nonlinear ninth-row GST family.
The newly proved physical seed remains at the same row 15 for
ALL natural multipliers u == 31 modulo 19683. -/
theorem commonTwo_new_nonlinear_ninth_trit_family
    (u : Nat) (hu : u%19683=31) :
    CommonTwo (4+u*3^6) := by
  have hrepr : u=31+19683*(u/19683) := by
    have h := Nat.mod_add_div u 19683
    omega
  have hshape :
      4+u*3^6=(4+31*3^6)+3^15*(u/19683) := by
    calc
      4+u*3^6=4+(31+19683*(u/19683))*3^6 := by
        exact congrArg (fun x : Nat => 4+x*3^6) hrepr
      _ = (4+31*3^6)+3^15*(u/19683) := by
        have hp : (19683:Nat)*3^6=3^15 := by norm_num
        rw [← hp]
        ring
  have hshape1 :
      (4+u*3^6)+1=(5+31*3^6)+3^15*(u/19683) := by
    omega
  have hs : digit3 (4^(4+31*3^6)) 15=2 :=
    read_seed31_ninth_trit 4 14143
      (by decide) (by decide) seed31_source_mod19683
  have hn : digit3 (4^(5+31*3^6)) 15=2 :=
    read_seed31_ninth_trit 5 17206
      (by decide) (by decide) seed31_neighbor_mod19683
  refine ⟨15, by decide, ?_, ?_⟩
  · rw [hshape]
    exact (pow4_digit_period 15 (4+31*3^6) (u/19683)).trans hs
  · rw [hshape1]
    exact (pow4_digit_period 15 (5+31*3^6) (u/19683)).trans hn

/-- The nonlinear family plugs directly into the ORIGINAL thirdWave
statement, not an artificially redefined Good or controller surrogate. -/
theorem original_thirdWave_on_nonlinear_ninth_trit
    (u : Nat) (hu : u%19683=31) :
    GSTFourPowerThirdWave.thirdWave (4+u*3^6) := by
  apply (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
  exact commonTwo_new_nonlinear_ninth_trit_family u hu

/-- Original creation certificate for the new physical quadratic source. -/
theorem original_creation_certificate_on_nonlinear_ninth_trit
    (u : Nat) (hu : u%19683=31) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^(4+u*3^6)) := by
  apply GSTFourPowerDirectCreationMaster.commonTwo_to_creation_certificate
  exact commonTwo_new_nonlinear_ninth_trit_family u hu

#print axioms c6_mod19683
#print axioms seed31_source_mod19683
#print axioms seed31_neighbor_mod19683
#print axioms commonTwo_new_nonlinear_ninth_trit_family
#print axioms original_thirdWave_on_nonlinear_ninth_trit
#print axioms original_creation_certificate_on_nonlinear_ninth_trit

end GSTWorldtraceQuadraticHGateDiscovery
