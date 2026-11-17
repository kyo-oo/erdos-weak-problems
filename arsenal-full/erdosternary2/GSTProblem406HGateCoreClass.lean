import GSTOmegaResidueClassExit
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Targeted hGate discharge route: direct infinite CommonTwo classes

Unlike the previous source-only digit-two certificates, this module proves
a SAME-ROW digit two in 4^K AND 4^(K+1), which is the precise
GSTFourPowerDirectExistence.CommonTwo / third-wave gate assertion.

For every L>=6 and unbounded u with u%3 !=0, this proof covers 11
of the 18 core classes modulo 27. No upper bound on u or L.
The remaining seven classes are not asserted impossible.
-/

namespace GSTProblem406HGateCoreClass

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Exact neighbor wave: 4^5=1024 is below 3^(L+1) for L>=6,
so the first three new quotient digits are 22u mod27. -/
theorem neighbor_quotient_mod27
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(5+u*3^L)/3^(L+1))%27=(22*u)%27 := by
  have hsmall : (4:Nat)^5 < 3^(L+1) := by
    have hnum : (4:Nat)^5 < 3^7 := by decide
    have hpow : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdiv : (4:Nat)^5/3^(L+1)=0 :=
    Nat.div_eq_of_lt hsmall
  have h1024 : (1024:Nat)/3^(L+1)=0 := by
    simpa only [show (4:Nat)^5=1024 by decide] using hdiv
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    5 u L 3 (by omega) (by omega)
  have hblock :
      (4^(5+u*3^L)/3^(L+1))%27 =
        (u*GSTCanonicalTailLTE.lteCoeff L*1024)%27 := by
    simpa only [show (3:Nat)^3=27 by decide,
      show (4:Nat)^5=1024 by decide,
      h1024, Nat.zero_add] using h
  have hc : (GSTCanonicalTailLTE.lteCoeff L*1024)%27=22 := by
    rw [Nat.mul_mod,
      GSTOmegaExactDelayedEscape.lteCoeff_mod27_sixteen L (by omega)] <;> decide
  calc
    (4^(5+u*3^L)/3^(L+1))%27 =
      (u*GSTCanonicalTailLTE.lteCoeff L*1024)%27 := hblock
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L*1024))%27 := by ring
    _ = (u*22)%27 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*1024))%27 =
          ((u%27)*((GSTCanonicalTailLTE.lteCoeff L*1024)%27))%27 :=
            Nat.mul_mod _ _ _
        _ = ((u%27)*22)%27 := by rw [hc]
        _ = (u*22)%27 := by
          simpa using (Nat.mul_mod u 22 27).symm
    _ = (22*u)%27 := by ac_rfl

/-- The neighbor's actual p=L+1+k ternary digit equals a trit of 22u. -/
theorem neighbor_three_digit_bridge
    (L u k : Nat) (hL : 6 ≤ L) (hk : k < 3) :
    digit3 (4^(5+u*3^L)) (L+1+k) = digit3 (22*u) k := by
  have hmod27 := neighbor_quotient_mod27 L u hL
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hmod :
      (4^(5+u*3^L)/3^(L+1))%3^(k+1) =
        (22*u)%3^(k+1) := by
    calc
      (4^(5+u*3^L)/3^(L+1))%3^(k+1) =
        ((4^(5+u*3^L)/3^(L+1))%27)%3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((22*u)%27)%3^(k+1) := by rw [hmod27]
      _ = (22*u)%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread := digit3_eq_of_mod_next
      (4^(5+u*3^L)/3^(L+1)) (22*u) k hmod
  calc
    digit3 (4^(5+u*3^L)) (L+1+k) =
      digit3 (4^(5+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (22*u) k := hread

/-- Exact finite-residue classifier, universally valid for any unbounded
u in a certified residue class. -/
private theorem eleven_of_eighteen_kernel :
    ∀ r : Fin 27,
      r.val%3≠0 →
      r.val≠4 → r.val≠10 → r.val≠13 →
      r.val≠16 → r.val≠19 → r.val≠22 → r.val≠25 →
      ∃ k : Fin 3,
        digit3 (19*r.val) k.val=2 ∧
        digit3 (22*r.val) k.val=2 := by decide

private theorem same_digit_mul_mod27
    (u m k : Nat) (hk : k<3) :
    digit3 (m*u) k = digit3 (m*(u%27)) k := by
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hbig : (m*u)%27=(m*(u%27))%27 := by
    simp [Nat.mul_mod]
  have hmod : (m*u)%3^(k+1)=(m*(u%27))%3^(k+1) := by
    calc
      (m*u)%3^(k+1)=((m*u)%27)%3^(k+1) :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((m*(u%27))%27)%3^(k+1) := by rw [hbig]
      _ = (m*(u%27))%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  exact digit3_eq_of_mod_next _ _ k hmod

/-- The gate itself, proved for eleven whole residue classes of unbounded
exponents K=4+u3^L, not a weaker source-only digit-two statement. -/
theorem commonTwo_unbounded_core_classes
    (L u : Nat) (hL : 6≤L) (h3 : u%3≠0)
    (h4 : u%27≠4) (h10 : u%27≠10)
    (h13 : u%27≠13) (h16 : u%27≠16)
    (h19 : u%27≠19) (h22 : u%27≠22)
    (h25 : u%27≠25) :
    CommonTwo (4+u*3^L) := by
  let r : Fin 27 := ⟨u%27, Nat.mod_lt _ (by decide)⟩
  have hr3 : r.val%3≠0 := by
    have h : (u%27)%3 = u%3 :=
      Nat.mod_mod_of_dvd u (by decide : 3 ∣ 27)
    dsimp [r]
    rw [h]
    exact h3
  obtain ⟨k,hpair⟩ :=
    eleven_of_eighteen_kernel r hr3 h4 h10 h13 h16 h19 h22 h25
  have hsource : digit3 (19*u) k.val=2 := by
    rw [same_digit_mul_mod27 u 19 k.val k.isLt]
    exact hpair.1
  have hneighbor : digit3 (22*u) k.val=2 := by
    rw [same_digit_mul_mod27 u 22 k.val k.isLt]
    exact hpair.2
  refine ⟨L+1+k.val, by omega, ?_, ?_⟩
  · rw [show 4+u*3^L=4+u*3^L by rfl]
    rw [GSTOmegaResidueClassExit.three_trit_digit_bridge L u k.val
      (by omega) k.isLt]
    exact hsource
  · have hexp : (4+u*3^L)+1 = 5+u*3^L := by omega
    rw [hexp, neighbor_three_digit_bridge L u k.val hL k.isLt]
    exact hneighbor



/-! ## New discovery: a fourth Worldtrace trit resolves additional live hGate classes

The two physical consecutive powers are retained; neither a generic BAD
controller nor a substituted source-only digit property occurs.
The coefficient stabilizes modulo 81 for ALL scales L >= 3.
The exact fourth quotient trits are 46*u and 22*u mod 81.

The three multiplier congruence classes u=10,40,58 (mod 81)
did not have a shared digit two among the first three trits, but
their fourth trit is simultaneously two in both powers. -/

/-- The fourth coefficient trit stabilizes at 16 modulo 81 after scale 3. -/
theorem lteCoeff_mod81_sixteen (L : Nat) (hL : 3 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 81 = 16 := by
  have hstep (t : Nat) (ht : 3 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 81 =
        GSTCanonicalTailLTE.lteCoeff t % 81 := by
    have hdiv : 81 ∣ 3^(t+1) := by
      have hd : 3^4 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^4 = 81 by decide] using hd
    calc
      GSTCanonicalTailLTE.lteCoeff (t+1) % 81 =
          (GSTCanonicalTailLTE.lteCoeff (t+1) % 3^(t+1)) % 81 :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (GSTCanonicalTailLTE.lteCoeff t % 3^(t+1)) % 81 := by
            rw [GSTWorldtraceCoeffStability.coeff_step_mod]
      _ = GSTCanonicalTailLTE.lteCoeff t % 81 :=
            Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ k : Nat,
      GSTCanonicalTailLTE.lteCoeff (3+k) % 81 = 16 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 3+(k+1) = (3+k)+1 by omega]
        rw [hstep (3+k) (by omega)]
        exact ih
  rw [show L = 3+(L-3) by omega]
  exact hbase (L-3)

/-- A single whole-block identity covers BOTH source M=4 and neighbor M=5,
with exact physical source 4^M and without any abstract transport premise. -/
theorem fourth_block_quotient_mod81
    (M u L m : Nat) (hL : 6 ≤ L)
    (hsmall : 4^M < 3^(L+1))
    (hm : (16 * 4^M) % 81 = m) :
    (4^(M+u*3^L)/3^(L+1))%81 = (m*u)%81 := by
  have hdiv : 4^M / 3^(L+1) = 0 := Nat.div_eq_of_lt hsmall
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 4 (by omega) (by omega)
  have hblock :
      (4^(M+u*3^L)/3^(L+1))%81 =
        (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%81 := by
    simpa only [show (3:Nat)^4=81 by decide,
      hdiv, Nat.zero_add] using h
  have hc : (GSTCanonicalTailLTE.lteCoeff L*4^M)%81 = m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*4^M)%81 =
          ((GSTCanonicalTailLTE.lteCoeff L%81)*((4^M)%81))%81 :=
            Nat.mul_mod _ _ _
      _ = (16*(4^M))%81 := by
            rw [lteCoeff_mod81_sixteen L (by omega)]
            simpa using (Nat.mul_mod 16 (4^M) 81).symm
      _ = m := hm
  calc
    (4^(M+u*3^L)/3^(L+1))%81 =
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%81 := hblock
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L*4^M))%81 := by ring
    _ = (u*m)%81 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*4^M))%81 =
            ((u%81)*((GSTCanonicalTailLTE.lteCoeff L*4^M)%81))%81 :=
              Nat.mul_mod _ _ _
        _ = ((u%81)*m)%81 := by rw [hc]
        _ = (u*m)%81 := by
              simpa using (Nat.mul_mod u m 81).symm
    _ = (m*u)%81 := by ac_rfl

/-- Full source power's fourth post-cut digit equals the fourth trit of 46*u. -/
theorem source_fourth_quotient_mod81
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(4+u*3^L)/3^(L+1))%81 = (46*u)%81 := by
  apply fourth_block_quotient_mod81 4 u L 46 hL
  · have hb : (4:Nat)^4 < 3^7 := by decide
    have hp : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    exact lt_of_lt_of_le hb hp
  · norm_num

/-- Full neighbor power's fourth post-cut digit equals 22*u. -/
theorem neighbor_fourth_quotient_mod81
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(5+u*3^L)/3^(L+1))%81 = (22*u)%81 := by
  apply fourth_block_quotient_mod81 5 u L 22 hL
  · have hb : (4:Nat)^5 < 3^7 := by decide
    have hp : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    exact lt_of_lt_of_le hb hp
  · norm_num

/-- Read the exact fourth trit from a quotient block without truncating
either of the two original perfect powers. -/
private theorem fourth_block_digit_bridge (M u L m : Nat)
    (hmod : (4^(M+u*3^L)/3^(L+1))%81 = (m*u)%81) :
    digit3 (4^(M+u*3^L)) (L+4) = digit3 (m*u) 3 := by
  have hread : digit3 (4^(M+u*3^L)/3^(L+1)) 3 =
      digit3 (m*u) 3 :=
    digit3_eq_of_mod_next _ _ 3 (by
      simpa only [show (3:Nat)^(3+1)=81 by decide] using hmod)
  calc
    digit3 (4^(M+u*3^L)) (L+4) =
        digit3 (4^(M+u*3^L)/3^(L+1)) 3 := by
          unfold digit3
          have hp : 3^(L+4) = 3^(L+1)*3^3 := by
            rw [show L+4 = (L+1)+3 by omega, pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (m*u) 3 := hread

/-- Four-trit residue reduction, independent of the size of u. -/
private theorem same_digit_mul_mod81 (u m : Nat) :
    digit3 (m*u) 3 = digit3 (m*(u%81)) 3 := by
  apply digit3_eq_of_mod_next
  change (m*u)%81 = (m*(u%81))%81
  simp [Nat.mul_mod]

/-- Exact finite classification of the three NEW multiplier classes. -/
private theorem new_fourth_residue_pair
    (u : Nat) (hu : u%81=10 ∨ u%81=40 ∨ u%81=58) :
    digit3 (46*u) 3 = 2 ∧ digit3 (22*u) 3 = 2 := by
  constructor
  · rw [same_digit_mul_mod81 u 46]
    rcases hu with h | h | h
    all_goals rw [h] <;> norm_num [digit3]
  · rw [same_digit_mul_mod81 u 22]
    rcases hu with h | h | h
    all_goals rw [h] <;> norm_num [digit3]

/-- New UNBOUNDED exact hGate family: ALL L >= 6 and ALL natural u in
three previously unproved modulo-81 classes yield the SAME row L+4 digit
two in consecutive physical powers 4^(4+u3^L) and 4^(5+u3^L). -/
theorem commonTwo_new_fourth_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : u%81=10 ∨ u%81=40 ∨ u%81=58) :
    CommonTwo (4+u*3^L) := by
  obtain ⟨hs, hn⟩ := new_fourth_residue_pair u hu
  refine ⟨L+4, by omega, ?_, ?_⟩
  · rw [fourth_block_digit_bridge 4 u L 46
      (source_fourth_quotient_mod81 L u hL)]
    exact hs
  · have he : (4+u*3^L)+1 = 5+u*3^L := by omega
    rw [he, fourth_block_digit_bridge 5 u L 22
      (neighbor_fourth_quotient_mod81 L u hL)]
    exact hn

#print axioms lteCoeff_mod81_sixteen
#print axioms fourth_block_quotient_mod81
#print axioms commonTwo_new_fourth_trit_classes



/-! ## Fifth-trit GST exact new residue classes

At one higher Worldtrace cut, c_L = 178 modulo 243 for all L >= 6.
Source coefficient (256*c_L) = 127 and neighbor (1024*c_L) = 22
modulo 243. An additional TEN 3-free multiplier classes that were
not in the previous fourth-trit new classes now have a simultaneous
digit 2 in their fifth postcut trit.
-/

/-- Stable fifth Worldtrace coefficient, uniformly over every L >= 6. -/
theorem lteCoeff_mod243_178 (L : Nat) (hL : 6 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 243 = 178 := by
  have hstep (t : Nat) (ht : 4 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 243 =
        GSTCanonicalTailLTE.lteCoeff t % 243 := by
    have hdiv : 243 ∣ 3^(t+1) := by
      have hd : 3^5 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^5=243 by decide] using hd
    calc
      GSTCanonicalTailLTE.lteCoeff (t+1) % 243 =
          (GSTCanonicalTailLTE.lteCoeff (t+1) % 3^(t+1)) % 243 :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (GSTCanonicalTailLTE.lteCoeff t % 3^(t+1)) % 243 := by
            rw [GSTWorldtraceCoeffStability.coeff_step_mod]
      _ = GSTCanonicalTailLTE.lteCoeff t % 243 :=
            Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ k : Nat,
      GSTCanonicalTailLTE.lteCoeff (4+k) % 243 = 178 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 4+(k+1)=(4+k)+1 by omega]
        rw [hstep (4+k) (by omega)]
        exact ih
  rw [show L=4+(L-4) by omega]
  exact hbase (L-4)

/-- Reusable fifth-block quotient law with the original physical source. -/
theorem fifth_block_quotient_mod243
    (M u L m : Nat) (hL : 6 ≤ L)
    (hsmall : 4^M < 3^(L+1))
    (hm : (178*4^M)%243 = m) :
    (4^(M+u*3^L)/3^(L+1))%243=(m*u)%243 := by
  have hdiv : 4^M/3^(L+1)=0 := Nat.div_eq_of_lt hsmall
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 5 (by omega) (by omega)
  have hblock :
      (4^(M+u*3^L)/3^(L+1))%243 =
        (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%243 := by
    simpa only [show (3:Nat)^5=243 by decide,
      hdiv, Nat.zero_add] using h
  have hc : (GSTCanonicalTailLTE.lteCoeff L*4^M)%243=m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*4^M)%243 =
        ((GSTCanonicalTailLTE.lteCoeff L%243)*((4^M)%243))%243 :=
          Nat.mul_mod _ _ _
      _ = (178*4^M)%243 := by
          rw [lteCoeff_mod243_178 L hL]
          simpa using (Nat.mul_mod 178 (4^M) 243).symm
      _ = m := hm
  calc
    (4^(M+u*3^L)/3^(L+1))%243 =
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%243 := hblock
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L*4^M))%243 := by ring
    _ = (u*m)%243 := by
        calc
          (u*(GSTCanonicalTailLTE.lteCoeff L*4^M))%243 =
              ((u%243)*((GSTCanonicalTailLTE.lteCoeff L*4^M)%243))%243 :=
                Nat.mul_mod _ _ _
          _ = ((u%243)*m)%243 := by rw [hc]
          _ = (u*m)%243 := by
                simpa using (Nat.mul_mod u m 243).symm
    _ = (m*u)%243 := by ac_rfl

theorem source_fifth_quotient_mod243
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(4+u*3^L)/3^(L+1))%243=(127*u)%243 := by
  apply fifth_block_quotient_mod243 4 u L 127 hL
  · have hb : (4:Nat)^4 < 3^7 := by decide
    have hp : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    exact lt_of_lt_of_le hb hp
  · norm_num

theorem neighbor_fifth_quotient_mod243
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(5+u*3^L)/3^(L+1))%243=(22*u)%243 := by
  apply fifth_block_quotient_mod243 5 u L 22 hL
  · have hb : (4:Nat)^5 < 3^7 := by decide
    have hp : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    exact lt_of_lt_of_le hb hp
  · norm_num

private theorem fifth_block_digit_bridge (M u L m : Nat)
    (hmod : (4^(M+u*3^L)/3^(L+1))%243=(m*u)%243) :
    digit3 (4^(M+u*3^L)) (L+5)=digit3 (m*u) 4 := by
  have hread : digit3 (4^(M+u*3^L)/3^(L+1)) 4 =
      digit3 (m*u) 4 :=
    digit3_eq_of_mod_next _ _ 4 (by
      simpa only [show (3:Nat)^(4+1)=243 by decide] using hmod)
  calc
    digit3 (4^(M+u*3^L)) (L+5) =
        digit3 (4^(M+u*3^L)/3^(L+1)) 4 := by
          unfold digit3
          have hp : 3^(L+5) = 3^(L+1)*3^4 := by
            rw [show L+5=(L+1)+4 by omega, pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (m*u) 4 := hread

private theorem same_digit_mul_mod243 (u m : Nat) :
    digit3 (m*u) 4=digit3 (m*(u%243)) 4 := by
  apply digit3_eq_of_mod_next
  change (m*u)%243=(m*(u%243))%243
  simp [Nat.mul_mod]

/-- Ten new modulo-243 multiplier residue classes, verified by exact
finite kernel arithmetic, and applied below to ALL unbounded multipliers. -/
def FifthNewClass (r : Nat) : Prop :=
  r=19 ∨ r=76 ∨ r=97 ∨ r=118 ∨ r=130 ∨
  r=151 ∨ r=187 ∨ r=208 ∨ r=229 ∨ r=241

private theorem fifth_new_classes_kernel :
    ∀ r : Fin 243, FifthNewClass r.val →
      digit3 (127*r.val) 4=2 ∧ digit3 (22*r.val) 4=2 := by
  intro r hr
  unfold FifthNewClass at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h
  all_goals norm_num [digit3, h]

/-- For every L>=6 and every u in TEN unbounded residue classes mod243,
there is an actual SAME-ROW source-neighbor digit pair at row L+5. -/
theorem commonTwo_new_fifth_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : FifthNewClass (u%243)) :
    CommonTwo (4+u*3^L) := by
  let r : Fin 243 := ⟨u%243, Nat.mod_lt _ (by decide)⟩
  have hpair : digit3 (127*r.val) 4=2 ∧
      digit3 (22*r.val) 4=2 :=
    fifth_new_classes_kernel r hu
  have hs : digit3 (127*u) 4=2 := by
    rw [same_digit_mul_mod243 u 127]
    exact hpair.1
  have hn : digit3 (22*u) 4=2 := by
    rw [same_digit_mul_mod243 u 22]
    exact hpair.2
  refine ⟨L+5, by omega, ?_, ?_⟩
  · rw [fifth_block_digit_bridge 4 u L 127
      (source_fifth_quotient_mod243 L u hL)]
    exact hs
  · have he : (4+u*3^L)+1=5+u*3^L := by omega
    rw [he, fifth_block_digit_bridge 5 u L 22
      (neighbor_fifth_quotient_mod243 L u hL)]
    exact hn

#print axioms lteCoeff_mod243_178
#print axioms source_fifth_quotient_mod243
#print axioms neighbor_fifth_quotient_mod243
#print axioms commonTwo_new_fifth_trit_classes



/-! ## Arbitrary-window two-wave GST physical source transfer

The finite fourth/fifth classifier was only the catalyst: the underlying
Worldtrace affine block is uniform in **any window width** up to L+1.
This is a reusable non-circular proof mechanism for discovering future
same-row gates. It does NOT presume such a certificate exists for
every exponent, so there is no hidden universal hGate assumption. -/

/-- The full source and neighbor quotient blocks are synchronized at every
width 1<=w<=L+1, with the ACTUAL consecutive perfect powers preserved. -/
theorem two_wave_any_width_block_exact
    (L u w : Nat) (hL : 6 ≤ L) (hw : 1 ≤ w)
    (hband : w ≤ L+1) :
    (4^(4+u*3^L)/3^(L+1))%3^w =
      (u*GSTCanonicalTailLTE.lteCoeff L*256)%3^w ∧
    (4^(5+u*3^L)/3^(L+1))%3^w =
      (u*GSTCanonicalTailLTE.lteCoeff L*1024)%3^w := by
  have hs : (4:Nat)^4 < 3^(L+1) := by
    have h0 : (4:Nat)^4 < 3^7 := by decide
    have h1 : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hn : (4:Nat)^5 < 3^(L+1) := by
    have h0 : (4:Nat)^5 < 3^7 := by decide
    have h1 : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdivs : (4:Nat)^4/3^(L+1)=0 := Nat.div_eq_of_lt hs
  have hdivn : (4:Nat)^5/3^(L+1)=0 := Nat.div_eq_of_lt hn
  have h4 := GSTWorldtraceBlockLift.pow4_whole_block_lift
    4 u L w hw hband
  have h5 := GSTWorldtraceBlockLift.pow4_whole_block_lift
    5 u L w hw hband
  have h256 : (256:Nat)/3^(L+1)=0 := by
    simpa only [show (4:Nat)^4=256 by decide] using hdivs
  have h1024 : (1024:Nat)/3^(L+1)=0 := by
    simpa only [show (4:Nat)^5=1024 by decide] using hdivn
  constructor
  · simpa only [show (4:Nat)^4=256 by decide,
        h256, Nat.zero_add] using h4
  · simpa only [show (4:Nat)^5=1024 by decide,
        h1024, Nat.zero_add] using h5

/-- Exact digit readback from ANY physical shifted tower quotient,
when an abstract block word A matches its first w trits. -/
private theorem any_width_block_digit_bridge
    (M L u w k A : Nat) (hk : k < w)
    (hwindow :
      (4^(M+u*3^L)/3^(L+1))%3^w = A%3^w) :
    digit3 (4^(M+u*3^L)) (L+1+k)=digit3 A k := by
  have hdiv : 3^(k+1) ∣ 3^w := Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      (4^(M+u*3^L)/3^(L+1))%3^(k+1)=A%3^(k+1) := by
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(k+1) =
          ((4^(M+u*3^L)/3^(L+1))%3^w)%3^(k+1) :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (A%3^w)%3^(k+1) := by rw [hwindow]
      _ = A%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread := digit3_eq_of_mod_next
      (4^(M+u*3^L)/3^(L+1)) A k hmod
  calc
    digit3 (4^(M+u*3^L)) (L+1+k) =
        digit3 (4^(M+u*3^L)/3^(L+1)) k := by
          unfold digit3
          have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
          rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 A k := hread

/-- A general finite-width GST source-neighbor *certificate* is sufficient
for an original common-two witness at a physical row. This works for all
natural u and all variable widths w<=L+1; unlike a fixed prefix scan,
it permits the observation horizon to grow with the source exponent. -/
theorem two_wave_any_width_certificate_to_CommonTwo
    (L u w k : Nat) (hL : 6 ≤ L) (hw : 1 ≤ w)
    (hband : w ≤ L+1) (hk : k < w)
    (hs : digit3 (u*GSTCanonicalTailLTE.lteCoeff L*256) k = 2)
    (hn : digit3 (u*GSTCanonicalTailLTE.lteCoeff L*1024) k = 2) :
    CommonTwo (4+u*3^L) := by
  obtain ⟨h4, h5⟩ :=
    two_wave_any_width_block_exact L u w hL hw hband
  refine ⟨L+1+k, by omega, ?_, ?_⟩
  · rw [any_width_block_digit_bridge 4 L u w k
      (u*GSTCanonicalTailLTE.lteCoeff L*256) hk h4]
    exact hs
  · have he : (4+u*3^L)+1=5+u*3^L := by omega
    rw [he, any_width_block_digit_bridge 5 L u w k
      (u*GSTCanonicalTailLTE.lteCoeff L*1024) hk h5]
    exact hn

#print axioms two_wave_any_width_block_exact
#print axioms two_wave_any_width_certificate_to_CommonTwo



/-! ## Sixth postcut trit: new congruence classes from the all-window theorem

The sixth quotient fingerprint uses c_L mod 729 = 664. The source
256*c_L reduces to 127 and the physical neighbor 1024*c_L to 508.
An additional 22 three-free residue classes mod 729 have a SAME-ROW
two in their sixth trit. The arbitrary-width GST theorem above makes
this extension a finite certificate application, not a new ad hoc
physical transport axiom. -/

/-- Sixth-trit GST Worldtrace coefficient stabilization at every scale
L>=6, with exact recurrence and no universal HGate premise. -/
theorem lteCoeff_mod729_664 (L : Nat) (hL : 6 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 729 = 664 := by
  have hstep (t : Nat) (ht : 5 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 729 =
        GSTCanonicalTailLTE.lteCoeff t % 729 := by
    have hdiv : 729 ∣ 3^(t+1) := by
      have hd : 3^6 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^6=729 by decide] using hd
    calc
      GSTCanonicalTailLTE.lteCoeff (t+1) % 729 =
          (GSTCanonicalTailLTE.lteCoeff (t+1) % 3^(t+1)) % 729 :=
            (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (GSTCanonicalTailLTE.lteCoeff t % 3^(t+1)) % 729 := by
            rw [GSTWorldtraceCoeffStability.coeff_step_mod]
      _ = GSTCanonicalTailLTE.lteCoeff t % 729 :=
            Nat.mod_mod_of_dvd _ hdiv
  have hbase : ∀ k : Nat,
      GSTCanonicalTailLTE.lteCoeff (5+k) % 729 = 664 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 5+(k+1)=(5+k)+1 by omega]
        rw [hstep (5+k) (by omega)]
        exact ih
  rw [show L=5+(L-5) by omega]
  exact hbase (L-5)

/-- Single coefficient-modulus reduction, for both fourth-power source
256 and fifth-power neighbor 1024, valid for unbounded multiplier u. -/
private theorem sixth_coefficient_product_mod729
    (L u M m : Nat) (hL : 6 ≤ L)
    (hm : (664*M)%729=m) :
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%729=(m*u)%729 := by
  have hc : (GSTCanonicalTailLTE.lteCoeff L*M)%729=m := by
    calc
      (GSTCanonicalTailLTE.lteCoeff L*M)%729 =
        ((GSTCanonicalTailLTE.lteCoeff L%729)*(M%729))%729 :=
          Nat.mul_mod _ _ _
      _ = (664*M)%729 := by
          rw [lteCoeff_mod729_664 L hL]
          simpa using (Nat.mul_mod 664 M 729).symm
      _ = m := hm
  calc
    (u*GSTCanonicalTailLTE.lteCoeff L*M)%729 =
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%729 := by ring
    _ = (u*m)%729 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*M))%729 =
            ((u%729)*((GSTCanonicalTailLTE.lteCoeff L*M)%729))%729 :=
              Nat.mul_mod _ _ _
        _ = ((u%729)*m)%729 := by rw [hc]
        _ = (u*m)%729 := by
              simpa using (Nat.mul_mod u m 729).symm
    _ = (m*u)%729 := by ac_rfl

/-- Exact ten-free sixth-trit residue families (22 additional classes). -/
def SixthNewClass (r : Nat) : Prop :=
  r=4 ∨ r=67 ∨ r=73 ∨ r=103 ∨ r=166 ∨ r=199 ∨ r=205 ∨ r=235 ∨ r=268 ∨ r=274 ∨ r=337 ∨ r=367 ∨ r=400 ∨ r=436 ∨ r=469 ∨ r=499 ∨ r=532 ∨ r=538 ∨ r=631 ∨ r=664 ∨ r=670 ∨ r=700

private theorem sixth_new_classes_kernel
    (r : Nat) (hr : SixthNewClass r) :
    digit3 (127*r) 5=2 ∧ digit3 (508*r) 5=2 := by
  unfold SixthNewClass at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r <;> norm_num [digit3]

/-- Twenty-two new modulo-729 infinite multiplier classes for every L>=6:
the literal physical powers 4^K and 4^(K+1) share digit two at L+6. -/
theorem commonTwo_new_sixth_trit_classes
    (L u : Nat) (hL : 6 ≤ L)
    (hu : SixthNewClass (u%729)) :
    CommonTwo (4+u*3^L) := by
  have hpair := sixth_new_classes_kernel (u%729) hu
  have hsource_mod : digit3 (127*u) 5 =
      digit3 (127*(u%729)) 5 := by
    apply digit3_eq_of_mod_next
    change (127*u)%729=(127*(u%729))%729
    simp [Nat.mul_mod]
  have hneighbor_mod : digit3 (508*u) 5 =
      digit3 (508*(u%729)) 5 := by
    apply digit3_eq_of_mod_next
    change (508*u)%729=(508*(u%729))%729
    simp [Nat.mul_mod]
  have hsource : digit3 (127*u) 5=2 := by
    rw [hsource_mod]
    exact hpair.1
  have hneighbor : digit3 (508*u) 5=2 := by
    rw [hneighbor_mod]
    exact hpair.2
  have hreadsource :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*256) 5 =
        digit3 (127*u) 5 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(5+1)=729 by decide] using
      (sixth_coefficient_product_mod729 L u 256 127 hL (by norm_num))
  have hreadneighbor :
      digit3 (u*GSTCanonicalTailLTE.lteCoeff L*1024) 5 =
        digit3 (508*u) 5 := by
    apply digit3_eq_of_mod_next
    simpa only [show (3:Nat)^(5+1)=729 by decide] using
      (sixth_coefficient_product_mod729 L u 1024 508 hL (by norm_num))
  apply two_wave_any_width_certificate_to_CommonTwo L u 6 5
    hL (by decide) (by omega) (by decide)
  · rw [hreadsource]
    exact hsource
  · rw [hreadneighbor]
    exact hneighbor

#print axioms lteCoeff_mod729_664
#print axioms commonTwo_new_sixth_trit_classes

#print axioms neighbor_quotient_mod27
#print axioms neighbor_three_digit_bridge
#print axioms eleven_of_eighteen_kernel
#print axioms commonTwo_unbounded_core_classes

end GSTProblem406HGateCoreClass
