import Mathlib
import MonolithGate.GSTWorldtraceArithmetic
import MonolithGate.GSTTheActConstruction
import MonolithGate.GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# THE NINTH CASCADE LEVEL — PART A — the binomial ladder, the quintic blade, the row-nine read, and the uniform ladder wrappers (levels two through nine) (S092 content repair)

The S091 terminal record named the module's content repair as the
campaign's last red lane: the 1502-line single module's elaboration
needs >13.7 GB (a stable plateau, measured across runs 45896152381 and
45901579365) and does not fit a 16 GB hosted runner as one process.
THE CURE (the S089m/w law, the dbf0092 pattern): the module split at
its own section boundaries — every proof byte-identical, each part
elaborated in its own process. Part 1 of 4.
-/


open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTheActConstruction (feedback_fire_of_class)
open GSTFourPowerDirectResidue (digit3_eq_of_mod_next)

/-! ## §1 The six-term binomial ladder -/

/-- **The six-term binomial ladder.** -/
theorem one_add_pow_six_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x
      + Nat.choose j 5 * x * x * x * x * x
      + x*x*x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    have h04 : Nat.choose 0 4 = 0 := by decide
    have h05 : Nat.choose 0 5 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03, h04, h05]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, GSTWorldtraceArithmetic.wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    have hc4 : Nat.choose (j+1) 4 = Nat.choose j 3 + Nat.choose j 4 :=
      Nat.choose_succ_succ j 3
    have hc5 : Nat.choose (j+1) 5 = Nat.choose j 4 + Nat.choose j 5 :=
      Nat.choose_succ_succ j 4
    rw [Nat.pow_succ, hR, hc2, hc3, hc4, hc5]
    refine ⟨Nat.choose j 5 + R + x*R, ?_⟩
    ring

/-! ## §2 The quintic blade -/

/-- **THE QUINTIC BLADE.** -/
theorem wt_quintic_mod59049 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4
      + 3969746172*Nat.choose m 5 [MOD 59049] := by
  obtain ⟨R, hR⟩ := one_add_pow_six_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + Nat.choose m 4 * 63 * 63 * 63 * 63
        + Nat.choose m 5 * 63 * 63 * 63 * 63 * 63
        + 63*63*63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5
        + 250094008836*R := by ring
  rw [GSTWorldtraceArithmetic.wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
      + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5
      + 250094008836*R) % 59049
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) % 59049
  have hd : 59049 ∣ 250094008836*R := by
    refine ⟨4235364*R, ?_⟩
    ring
  have hz : 250094008836*R % 59049 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-! ## §3 The row-nine read -/

/-- **ROW NINE IS THE QUINTIC.** -/
theorem wt_row_nine_read (m : Nat) :
    digit3 (4^(1+3*m)) 9
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) 9 := by
  have h59049 : (3:Nat)^(9+1) = 59049 := by decide
  have h := wt_quintic_mod59049 m
  rw [← h59049] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-! ## §4 The uniform kills — the ladder wrappers, levels two through nine -/

/-- **THE UNIFORM KILL, LEVEL 2.** -/
theorem ladder_fire_mod9 (K r t : Nat)
    (hr : r < 3) (ht : t < 3)
    (hnoise : (digit3 (4^r) 2 + t) % 3 = 2)
    (hclass : K % 9 = r + 3 * t) :
    digit3 (4^K) 2 = 2 := by
  have hK : K % 3^(1+1) = r + 3^1 * t := by
    rw [show (3:Nat)^(1+1) = 9 from by decide,
        show (3:Nat)^1 = 3 from by decide]
    exact hclass
  have hr' : r < 3^1 := by
    rw [show (3:Nat)^1 = 3 from by decide]
    exact hr
  exact feedback_fire_of_class 1 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 3.** -/
theorem ladder_fire_mod27 (K r t : Nat)
    (hr : r < 9) (ht : t < 3)
    (hnoise : (digit3 (4^r) 3 + t) % 3 = 2)
    (hclass : K % 27 = r + 9 * t) :
    digit3 (4^K) 3 = 2 := by
  have hK : K % 3^(2+1) = r + 3^2 * t := by
    rw [show (3:Nat)^(2+1) = 27 from by decide,
        show (3:Nat)^2 = 9 from by decide]
    exact hclass
  have hr' : r < 3^2 := by
    rw [show (3:Nat)^2 = 9 from by decide]
    exact hr
  exact feedback_fire_of_class 2 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 4.** -/
theorem ladder_fire_mod81 (K r t : Nat)
    (hr : r < 27) (ht : t < 3)
    (hnoise : (digit3 (4^r) 4 + t) % 3 = 2)
    (hclass : K % 81 = r + 27 * t) :
    digit3 (4^K) 4 = 2 := by
  have hK : K % 3^(3+1) = r + 3^3 * t := by
    rw [show (3:Nat)^(3+1) = 81 from by decide,
        show (3:Nat)^3 = 27 from by decide]
    exact hclass
  have hr' : r < 3^3 := by
    rw [show (3:Nat)^3 = 27 from by decide]
    exact hr
  exact feedback_fire_of_class 3 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 5.** -/
theorem ladder_fire_mod243 (K r t : Nat)
    (hr : r < 81) (ht : t < 3)
    (hnoise : (digit3 (4^r) 5 + t) % 3 = 2)
    (hclass : K % 243 = r + 81 * t) :
    digit3 (4^K) 5 = 2 := by
  have hK : K % 3^(4+1) = r + 3^4 * t := by
    rw [show (3:Nat)^(4+1) = 243 from by decide,
        show (3:Nat)^4 = 81 from by decide]
    exact hclass
  have hr' : r < 3^4 := by
    rw [show (3:Nat)^4 = 81 from by decide]
    exact hr
  exact feedback_fire_of_class 4 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 6.** -/
theorem ladder_fire_mod729 (K r t : Nat)
    (hr : r < 243) (ht : t < 3)
    (hnoise : (digit3 (4^r) 6 + t) % 3 = 2)
    (hclass : K % 729 = r + 243 * t) :
    digit3 (4^K) 6 = 2 := by
  have hK : K % 3^(5+1) = r + 3^5 * t := by
    rw [show (3:Nat)^(5+1) = 729 from by decide,
        show (3:Nat)^5 = 243 from by decide]
    exact hclass
  have hr' : r < 3^5 := by
    rw [show (3:Nat)^5 = 243 from by decide]
    exact hr
  exact feedback_fire_of_class 5 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 7.** -/
theorem ladder_fire_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2 := by
  have hK : K % 3^(6+1) = r + 3^6 * t := by
    rw [show (3:Nat)^(6+1) = 2187 from by decide,
        show (3:Nat)^6 = 729 from by decide]
    exact hclass
  have hr' : r < 3^6 := by
    rw [show (3:Nat)^6 = 729 from by decide]
    exact hr
  exact feedback_fire_of_class 6 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 8.** -/
theorem ladder_fire_mod6561 (K r t : Nat)
    (hr : r < 2187) (ht : t < 3)
    (hnoise : (digit3 (4^r) 8 + t) % 3 = 2)
    (hclass : K % 6561 = r + 2187 * t) :
    digit3 (4^K) 8 = 2 := by
  have hK : K % 3^(7+1) = r + 3^7 * t := by
    rw [show (3:Nat)^(7+1) = 6561 from by decide,
        show (3:Nat)^7 = 2187 from by decide]
    exact hclass
  have hr' : r < 3^7 := by
    rw [show (3:Nat)^7 = 2187 from by decide]
    exact hr
  exact feedback_fire_of_class 7 r t K hr' ht hnoise hK
/-- **THE UNIFORM KILL, LEVEL 9.** -/
theorem fire_of_mod19683 (K r t : Nat)
    (hr : r < 6561) (ht : t < 3)
    (hnoise : (digit3 (4^r) 9 + t) % 3 = 2)
    (hclass : K % 19683 = r + 6561 * t) :
    digit3 (4^K) 9 = 2 := by
  have hK : K % 3^(8+1) = r + 3^8 * t := by
    rw [show (3:Nat)^(8+1) = 19683 from by decide,
        show (3:Nat)^8 = 6561 from by decide]
    exact hclass
  have hr' : r < 3^8 := by
    rw [show (3:Nat)^8 = 6561 from by decide]
    exact hr
  exact feedback_fire_of_class 8 r t K hr' ht hnoise hK

