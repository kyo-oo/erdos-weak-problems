import GSTWorldtraceBlockLift
import GSTWorldtraceCoeffStability
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact physical pure power-of-three exponent family for Problem 406

This is a new hGate family outside the earlier 4+u*3^L families.
Both powers 4^(u*3^L) and 4^(u*3^L+1) occur literally, not
abstract or assumed controllers.  The coefficient is stable at all L>=4.
-/

namespace GSTProblem406UnboundedPureThreePowerFamily

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Stable five-trit physical GST coefficient, valid already at L=4. -/
theorem coeff_mod243 (L : Nat) (hL : 4 ≤ L) :
    GSTCanonicalTailLTE.lteCoeff L % 243 = 178 := by
  have hstep (t : Nat) (ht : 4 ≤ t) :
      GSTCanonicalTailLTE.lteCoeff (t+1) % 243 =
        GSTCanonicalTailLTE.lteCoeff t % 243 := by
    have hdiv : 243 ∣ 3^(t+1) := by
      have hd : 3^5 ∣ 3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega)
      simpa only [show (3:Nat)^5 = 243 by decide] using hd
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

/-- Source 4^(u*3^L) or neighbor 4^(1+u*3^L) postcut
quotient is literally the stable GST linear block for five trits. -/
theorem physical_pair_quotient_mod243
    (M L u : Nat) (hL : 4 ≤ L) (hM : M=0 ∨ M=1) :
    (4^(M+u*3^L) / 3^(L+1)) % 243 =
      (178*u*4^M) % 243 := by
  have hlarge : 4 < 3^(L+1) := by
    have hp : 3^5 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at hp ⊢
    omega
  have hsmall : 4^M < 3^(L+1) := by
    rcases hM with h | h
    · subst M
      norm_num at * <;> omega
    · subst M
      norm_num at * <;> omega
  have hd : 4^M / 3^(L+1) = 0 := Nat.div_eq_of_lt hsmall
  have hh := GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L 5 (by omega) (by omega)
  have hq : (4^(M+u*3^L)/3^(L+1))%243 =
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%243 := by
    simpa only [show (3:Nat)^5=243 by decide, hd, Nat.zero_add] using hh
  have hc := coeff_mod243 L hL
  calc
    (4^(M+u*3^L)/3^(L+1))%243 =
      (u*GSTCanonicalTailLTE.lteCoeff L*4^M)%243 := hq
    _ = (u*178*4^M)%243 := by simp [Nat.mul_mod, hc]
    _ = (178*u*4^M)%243 := by congr 1; ring

/-- Every one of the first five postcut trits is read from
the real untruncated consecutive perfect powers. -/
theorem physical_pair_digit_bridge
    (M L u j : Nat) (hL : 4 ≤ L)
    (hM : M=0 ∨ M=1) (hj : j<5) :
    digit3 (4^(M+u*3^L)) (L+1+j) =
      digit3 (178*u*4^M) j := by
  have hq := physical_pair_quotient_mod243 M L u hL hM
  have hd : 3^(j+1) ∣ 243 := by
    have h : 3^(j+1) ∣ 3^5 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^5=243 by decide] using h
  have heq : (4^(M+u*3^L)/3^(L+1))%3^(j+1) =
      (178*u*4^M)%3^(j+1) := by
    calc
      (4^(M+u*3^L)/3^(L+1))%3^(j+1) =
          ((4^(M+u*3^L)/3^(L+1))%243)%3^(j+1) :=
            (Nat.mod_mod_of_dvd _ hd).symm
      _ = ((178*u*4^M)%243)%3^(j+1) := by rw [hq]
      _ = (178*u*4^M)%3^(j+1) := Nat.mod_mod_of_dvd _ hd
  have hread := digit3_eq_of_mod_next
    (4^(M+u*3^L)/3^(L+1)) (178*u*4^M) j heq
  calc
    digit3 (4^(M+u*3^L)) (L+1+j) =
       digit3 (4^(M+u*3^L)/3^(L+1)) j := by
        unfold digit3
        have hp : 3^(L+1+j)=3^(L+1)*3^j := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (178*u*4^M) j := hread

/-- Any certified five-trit residue is a genuine common-2 witness
for an unbounded family of powers, not a conjectural universal gate. -/
theorem commonTwo_pure_scaled_family
    (L u j : Nat) (hL : 4 ≤ L) (hj : j<5)
    (hs : digit3 (178*u) j=2)
    (hn : digit3 (712*u) j=2) :
    CommonTwo (u*3^L) := by
  refine ⟨L+1+j, by omega, ?_, ?_⟩
  · have h := physical_pair_digit_bridge 0 L u j hL (Or.inl rfl) hj
    have h' : digit3 (4^(u*3^L)) (L+1+j) = digit3 (178*u) j := by
      simpa only [Nat.zero_add, pow_zero, Nat.mul_one] using h
    exact h'.trans hs
  · have h := physical_pair_digit_bridge 1 L u j hL (Or.inr rfl) hj
    have he : (u*3^L)+1=1+u*3^L := by omega
    rw [he]
    have h4 : 178*u*4^1=712*u := by norm_num; ring
    rw [h4] at h
    exact h.trans hn

/-- A wholly unconditional infinite physical class:
all L>=4 and all multipliers u==1 mod243 have simultaneous
digit 2 in both original powers at the same row L+5. -/
theorem commonTwo_multiplier_one_mod243
    (L u : Nat) (hL : 4 ≤ L) (hu : u%243=1) :
    CommonTwo (u*3^L) := by
  have hs : digit3 (178*u) 4=2 := by
    have hh : (178*u)%243=178 := by
      calc
        (178*u)%243=(178*(u%243))%243 := by simp [Nat.mul_mod]
        _ = 178 := by simp [hu]
    have hh' : (178*u)%3^(4+1)=178%3^(4+1) := by
      simpa only [show (3:Nat)^(4+1)=243 by decide] using hh
    rw [digit3_eq_of_mod_next (178*u) 178 4 hh']
    norm_num [digit3]
  have hn : digit3 (712*u) 4=2 := by
    have hh : (712*u)%243=712%243 := by
      calc
        (712*u)%243=(712*(u%243))%243 := by simp [Nat.mul_mod]
        _ = 712%243 := by simp [hu]
    have hh' : (712*u)%3^(4+1)=712%3^(4+1) := by
      simpa only [show (3:Nat)^(4+1)=243 by decide] using hh
    rw [digit3_eq_of_mod_next (712*u) 712 4 hh']
    norm_num [digit3]
  exact commonTwo_pure_scaled_family L u 4 hL (by decide) hs hn

/-- In particular, all pure powers of 3 of exponent L>=4
are safe: K=3^L, and the first proved row is L+5. -/
theorem commonTwo_pure_three_power (L : Nat) (hL : 4 ≤ L) :
    CommonTwo (3^L) := by
  simpa using (commonTwo_multiplier_one_mod243 L 1 hL (by decide))

#print axioms coeff_mod243
#print axioms physical_pair_quotient_mod243
#print axioms physical_pair_digit_bridge
#print axioms commonTwo_pure_scaled_family
#print axioms commonTwo_multiplier_one_mod243
#print axioms commonTwo_pure_three_power

end GSTProblem406UnboundedPureThreePowerFamily
