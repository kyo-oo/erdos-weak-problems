import GSTGraphV2InfiniteControl
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTFinalPurePowerResidueTransplant

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialLTE

/-!
# Literal pure-power residue transplant

This file copies the useful arithmetic body of the Aug-15/16 pure-power
residue / carry-word stack into the active final residual branch.  It is a
production transplant, not a reference to a candidate theorem.  The objects
below are all exact Nat identities and do not introduce a terminal wave,
finite-support assumption, `proof-hole`, axiom, or native decision shortcut.
-/

/-! ## Horizontal carry word -/

def stripQuotient (r M j : Nat) : Nat :=
  (4^j * r) / M

def stripCarry (r M j : Nat) : Nat :=
  (4 * ((4^j * r) % M)) / M

theorem stripQuotient_succ
    (r M j : Nat) (hM : 0 < M) :
    stripQuotient r M (j+1) =
      4 * stripQuotient r M j + stripCarry r M j := by
  simp only [stripQuotient, stripCarry]
  have hsplit :
      4^j * r = M * ((4^j * r) / M) + (4^j * r) % M := by
    exact (Nat.div_add_mod (4^j * r) M).symm
  have hnumPow : 4^(j+1) * r = 4 * (4^j * r) := by
    rw [Nat.pow_succ]
    ac_rfl
  calc
    (4^(j+1) * r) / M = (4 * (4^j * r)) / M :=
      congrArg (fun x : Nat => x / M) hnumPow
    _ = (4 * (M * ((4^j * r) / M) + (4^j * r) % M)) / M := by
      rw [← hsplit]
    _ = (4 * ((4^j * r) % M) + M * (4 * ((4^j * r) / M))) / M := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (4 * ((4^j * r) % M)) / M + 4 * ((4^j * r) / M) := by
      rw [Nat.add_mul_div_left _ _ hM]
    _ = 4 * ((4^j * r) / M) + (4 * ((4^j * r) % M)) / M := by ac_rfl

theorem stripCarry_lt_four
    (r M j : Nat) (hM : 0 < M) :
    stripCarry r M j < 4 := by
  unfold stripCarry
  have hr : (4^j * r) % M < M := Nat.mod_lt _ hM
  have hnum : 4 * ((4^j * r) % M) < M * 4 := by
    have h := Nat.mul_lt_mul_of_pos_left hr (by decide : 0 < 4)
    simpa [Nat.mul_comm] using h
  exact Nat.div_lt_of_lt_mul hnum

theorem stripQuotient_succ_mod4
    (r M j : Nat) (hM : 0 < M) :
    stripQuotient r M (j+1) % 4 = stripCarry r M j := by
  rw [stripQuotient_succ r M j hM]
  have hc := stripCarry_lt_four r M j hM
  omega

theorem stripQuotient_succ_div4
    (r M j : Nat) (hM : 0 < M) :
    stripQuotient r M (j+1) / 4 = stripQuotient r M j := by
  rw [stripQuotient_succ r M j hM]
  have hc := stripCarry_lt_four r M j hM
  have h4 : 0 < (4:Nat) := by decide
  have hshape :
      4 * stripQuotient r M j + stripCarry r M j =
        stripCarry r M j + 4 * stripQuotient r M j := by ac_rfl
  rw [hshape, Nat.add_mul_div_left _ _ h4]
  have hzero : stripCarry r M j / 4 = 0 := Nat.div_eq_of_lt hc
  simp [hzero]

theorem stripQuotient_shift_div
    (r M i k : Nat) (hM : 0 < M) :
    stripQuotient r M (i+k) / 4^k = stripQuotient r M i := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := stripQuotient_succ_div4 r M (i+k) hM
      have hidx : i + (k+1) = (i+k)+1 := by omega
      rw [hidx]
      have hpow : 4^(k+1) = 4 * 4^k := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hpow, ← Nat.div_div_eq_div_mul]
      rw [hstep]
      exact ih

theorem stripCarry_is_information_digit
    (r M i k : Nat) (hM : 0 < M) :
    stripQuotient r M (i+k+1) / 4^k % 4 = stripCarry r M i := by
  have hshift := stripQuotient_shift_div r M (i+1) k hM
  have hidx : (i+1)+k = i+k+1 := by omega
  rw [hidx] at hshift
  rw [hshift]
  exact stripQuotient_succ_mod4 r M i hM

/-! ## Arbitrary-width exact strip -/

def wideCarry (B R p : Nat) : Nat :=
  (B * (R % 3^p)) / 3^p

def wideDigit (R p : Nat) : Nat :=
  R / 3^p % 3

theorem wideCarry_forward_exact
    (B R p : Nat) :
    wideCarry B R (p+1) =
      (wideCarry B R p + B * wideDigit R p) / 3 := by
  simp only [wideCarry, wideDigit, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show B * (3^p * (R / 3^p % 3)) =
      3^p * (B * (R / 3^p % 3)) by ac_rfl]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

theorem wideQuotient_decomposition
    (B R p : Nat) :
    (B*R) / 3^p = wideCarry B R p + B * (R / 3^p) := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hdiv : R = 3^p * (R / 3^p) + R % 3^p :=
    (Nat.div_add_mod R (3^p)).symm
  calc
    (B*R) / 3^p =
        (B * (3^p * (R / 3^p) + R % 3^p)) / 3^p := by rw [← hdiv]
    _ = (B * (R % 3^p) + 3^p * (B * (R / 3^p))) / 3^p := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (B * (R % 3^p)) / 3^p + B * (R / 3^p) := by
      rw [Nat.add_mul_div_left _ _ hp]
    _ = wideCarry B R p + B * (R / 3^p) := by rfl

theorem wideOutputDigit_exact
    (B R p : Nat) :
    wideDigit (B*R) p =
      (wideCarry B R p + B * wideDigit R p) % 3 := by
  unfold wideDigit
  rw [wideQuotient_decomposition]
  have hmul :
      (B * (R / 3^p)) % 3 =
        (B * ((R / 3^p) % 3)) % 3 := by
    calc
      (B * (R / 3^p)) % 3 =
          ((B % 3) * ((R / 3^p) % 3)) % 3 :=
            Nat.mul_mod B (R / 3^p) 3
      _ = (B * ((R / 3^p) % 3)) % 3 := by
        simpa only [Nat.mod_mod] using
          (Nat.mul_mod B ((R / 3^p) % 3) 3).symm
  have haddL := Nat.add_mod
      (wideCarry B R p) (B * (R / 3^p)) 3
  have haddR := Nat.add_mod
      (wideCarry B R p) (B * ((R / 3^p) % 3)) 3
  rw [haddL, haddR, hmul]

theorem stripConservation_exact
    (B R p : Nat) :
    B * wideDigit R p + wideCarry B R p =
      wideDigit (B*R) p + 3 * wideCarry B R (p+1) := by
  have hcarry := wideCarry_forward_exact B R p
  have hdigit := wideOutputDigit_exact B R p
  let X := wideCarry B R p + B * wideDigit R p
  have hdivmod : X = X % 3 + 3 * (X / 3) := by
    have h := Nat.mod_add_div X 3
    omega
  dsimp [X] at hdivmod
  rw [← hcarry, ← hdigit] at hdivmod
  omega

/-! ## Exact exponent-trit lift -/

theorem pow4_mod3_one (m : Nat) : 4^m % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

theorem pow4_exponent_lift_one_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 1) % 3 := by
  let L := 3^(p+1)
  have hL : 0 < L := by
    dsimp [L]
    exact Nat.pow_pos (by decide)
  have hpow : 4^(m + 3^p) = 4^m * (1 + L*c) := by
    rw [Nat.pow_add, hA]
  have hshape :
      4^m * (1 + L*c) = 4^m + L * (4^m*c) := by ring
  unfold digit3
  rw [show 3^(p+1) = L by rfl, hpow, hshape]
  rw [Nat.add_mul_div_left _ _ hL]
  rw [Nat.add_mod, Nat.mul_mod, pow4_mod3_one, hc]

theorem pow4_exponent_lift_two_digit
    (p m c : Nat)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + 2*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + 2) % 3 := by
  have h1 := pow4_exponent_lift_one_digit p m c hA hc
  have h2 := pow4_exponent_lift_one_digit p (m + 3^p) c hA hc
  have hexp : m + 2*3^p = (m + 3^p) + 3^p := by omega
  rw [hexp]
  rw [h2, h1]
  have hd : digit3 (4^m) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  omega

theorem pow4_exponent_trit_lift_digit
    (p m c a : Nat)
    (ha : a < 3)
    (hA : 4^(3^p) = 1 + 3^(p+1)*c)
    (hc : c % 3 = 1) :
    digit3 (4^(m + a*3^p)) (p+1) =
      (digit3 (4^m) (p+1) + a) % 3 := by
  have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases haCases with h0 | h1 | h2
  · subst a
    simp only [Nat.zero_mul, Nat.add_zero]
    have hd : digit3 (4^m) (p+1) < 3 := by
      unfold digit3
      exact Nat.mod_lt _ (by decide)
    omega
  · subst a
    simpa using pow4_exponent_lift_one_digit p m c hA hc
  · subst a
    simpa using pow4_exponent_lift_two_digit p m c hA hc

/-! ## Pure-power aligned residue tower -/

def residueTowerModulus (D q : Nat) : Nat := 3*D*3^q

theorem residueTower_step
    (D T q : Nat) :
    1 + 3*D*(T % 3^(q+1)) =
      (1 + 3*D*(T % 3^q)) +
        residueTowerModulus D q * digit3 T q := by
  unfold residueTowerModulus digit3
  rw [Nat.pow_succ, Nat.mod_mul]
  ring

theorem purePowerStripInputResidue
    (D T E K q : Nat)
    (hD : 1 ≤ D)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K) :
    4^K % (3*D*3^q) = 1 + 3*D*(T % 3^q) := by
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hMpos : 0 < 3*D*3^q := by positivity
  have hrlt : 1 + 3*D*(T % 3^q) < 3*D*3^q := by
    have hr : T % 3^q < 3^q := Nat.mod_lt _ hqpos
    have h3D : 1 < 3*D := by omega
    have hmul : 3*D*(T % 3^q + 1) ≤ 3*D*3^q :=
      Nat.mul_le_mul_left (3*D) (Nat.succ_le_of_lt hr)
    have hstep : 1 + 3*D*(T % 3^q) < 3*D*(T % 3^q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact lt_of_lt_of_le hstep hmul
  have hT : T = 3^q * (T / 3^q) + T % 3^q :=
    (Nat.div_add_mod T (3^q)).symm
  have hdecomp :
      E = (1 + 3*D*(T % 3^q)) + (3*D*3^q) * (T / 3^q) := by
    rw [hE]
    conv_lhs => rw [hT]
    ring
  have hmulmod :
      ((3*D*3^q) * (T / 3^q)) % (3*D*3^q) = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
  rw [← hPow, hdecomp, Nat.add_mod, hmulmod, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hrlt

theorem purePowerResidueTower_exact
    (D T E K q : Nat)
    (hD : 1 ≤ D)
    (hE : E = 1 + 3*D*T)
    (hPow : E = 4^K) :
    4^K % residueTowerModulus D q =
      1 + 3*D*(T % 3^q) := by
  unfold residueTowerModulus
  exact purePowerStripInputResidue D T E K q hD hE hPow

theorem residueTowerModulus_canonical
    (s q : Nat) :
    residueTowerModulus (3^(s+1)) q = 3^(s+2+q) := by
  unfold residueTowerModulus
  calc
    3 * 3^(s+1) * 3^q = 3^1 * 3^(s+1) * 3^q := by norm_num
    _ = 3^(1+(s+1)) * 3^q := by rw [← Nat.pow_add]
    _ = 3^((1+(s+1))+q) := by rw [← Nat.pow_add]
    _ = 3^(s+2+q) := by congr 1 <;> omega

theorem residueStripCarry_is_exact_power_carry
    (s K q i : Nat) :
    stripCarry
        (4^K % residueTowerModulus (3^(s+1)) q)
        (residueTowerModulus (3^(s+1)) q) i =
      carry4 (4^(K+i)) (s+2+q) := by
  have hM := residueTowerModulus_canonical s q
  unfold stripCarry carry4
  rw [hM]
  have hres :
      (4^i * (4^K % 3^(s+2+q))) % 3^(s+2+q) =
        (4^i * 4^K) % 3^(s+2+q) := by
    simp [Nat.mul_mod]
  rw [hres]
  have hpow : 4^i * 4^K = 4^(K+i) := by
    calc
      4^i * 4^K = 4^(i+K) := (Nat.pow_add 4 i K).symm
      _ = 4^(K+i) := by rw [Nat.add_comm]
  rw [hpow]

theorem residueStripQuotient_is_exact_power_wideCarry
    (s K q width : Nat) :
    stripQuotient
        (4^K % residueTowerModulus (3^(s+1)) q)
        (residueTowerModulus (3^(s+1)) q) width =
      (4^width * (4^K % 3^(s+2+q))) / 3^(s+2+q) := by
  unfold stripQuotient
  rw [residueTowerModulus_canonical]

theorem exactPowerRectangle_conservation
    (s N K q : Nat) :
    4^(N+1) * digit3 (4^K) (s+2+q) +
        wideCarry (4^(N+1)) (4^K) (s+2+q) =
      digit3 (4^(K+N+1)) (s+2+q) +
        3 * wideCarry (4^(N+1)) (4^K) ((s+2+q)+1) := by
  have h := stripConservation_exact
    (4^(N+1)) (4^K) (s+2+q)
  have hpow : 4^(N+1) * 4^K = 4^(K+N+1) := by
    calc
      4^(N+1) * 4^K = 4^((N+1)+K) := (Nat.pow_add 4 (N+1) K).symm
      _ = 4^(K+N+1) := by congr 1 <;> omega
  simpa [wideDigit, digit3, hpow] using h

#check stripQuotient_succ
#check stripCarry_is_information_digit
#check stripConservation_exact
#check pow4_exponent_trit_lift_digit
#check purePowerStripInputResidue
#check residueStripCarry_is_exact_power_carry
#check exactPowerRectangle_conservation

end GSTFinalPurePowerResidueTransplant
