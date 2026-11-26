import Mathlib
import MonolithGate.GSTWorldtraceArithmetic
import MonolithGate.GSTTheActConstruction
import MonolithGate.GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# THE NINTH CASCADE LEVEL (S085 r34v3, the final assembly round)

One storey deeper than the engine's deepest green level, and the ladder
rewritten SELF-CONTAINED: the worldtrace ladder at level nine — the quintic
blade mod 59049, the row-nine read, the uniform kills `ladder_fire_mod*` for
EVERY level two through nine (each through the engine's own level-generic
`feedback_fire_of_class`), the 128 dead classes of `dust_fire_row_nine`, the
kill chain `no22_of_cascade_eight`, and the re-doubled Cantorian pin
`cantorian_dust_mod_19683` (the 256-survivor map, based on the engine's
receipt-verified level-six pin plus three levels of fire exclusions).

Computational certificate (two-method): all fire lists and the 256
survivors recomputed by modular exponentiation AND direct big-integer
ternary expansion — zero mismatches; the doubling law holds at every
level; the quintic blade validated on every m < 3000.
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

/-! ## §5 The ninth cascade level — the 128 dead classes -/

/-- **CASCADE LEVEL NINE (row nine).** -/
theorem dust_fire_row_nine (K : Nat)
    (hK : K % 19683 = 40 ∨ K % 19683 = 94 ∨ K % 19683 = 109 ∨ K % 19683 = 193 ∨ K % 19683 = 244 ∨ K % 19683 = 283 ∨ K % 19683 = 325 ∨ K % 19683 = 733 ∨ K % 19683 = 928 ∨ K % 19683 = 1009 ∨ K % 19683 = 1144 ∨ K % 19683 = 1171 ∨ K % 19683 = 1252 ∨ K % 19683 = 1387 ∨ K % 19683 = 1540 ∨ K % 19683 = 1957 ∨ K % 19683 = 2434 ∨ K % 19683 = 2470 ∨ K % 19683 = 2512 ∨ K % 19683 = 2767 ∨ K % 19683 = 2920 ∨ K % 19683 = 3115 ∨ K % 19683 = 3196 ∨ K % 19683 = 3331 ∨ K % 19683 = 3727 ∨ K % 19683 = 4144 ∨ K % 19683 = 4162 ∨ K % 19683 = 4297 ∨ K % 19683 = 4387 ∨ K % 19683 = 4495 ∨ K % 19683 = 4621 ∨ K % 19683 = 4897 ∨ K % 19683 = 4954 ∨ K % 19683 = 5197 ∨ K % 19683 = 5296 ∨ K % 19683 = 5617 ∨ K % 19683 = 5842 ∨ K % 19683 = 5998 ∨ K % 19683 = 6157 ∨ K % 19683 = 6349 ∨ K % 19683 = 6484 ∨ K % 19683 = 6574 ∨ K % 19683 = 6682 ∨ K % 19683 = 6841 ∨ K % 19683 = 6925 ∨ K % 19683 = 6997 ∨ K % 19683 = 7084 ∨ K % 19683 = 7156 ∨ K % 19683 = 7291 ∨ K % 19683 = 7384 ∨ K % 19683 = 7483 ∨ K % 19683 = 7564 ∨ K % 19683 = 7786 ∨ K % 19683 = 7804 ∨ K % 19683 = 8029 ∨ K % 19683 = 8185 ∨ K % 19683 = 8344 ∨ K % 19683 = 9028 ∨ K % 19683 = 9112 ∨ K % 19683 = 9184 ∨ K % 19683 = 9343 ∨ K % 19683 = 9478 ∨ K % 19683 = 9724 ∨ K % 19683 = 9751 ∨ K % 19683 = 9973 ∨ K % 19683 = 10234 ∨ K % 19683 = 10246 ∨ K % 19683 = 11449 ∨ K % 19683 = 11674 ∨ K % 19683 = 11773 ∨ K % 19683 = 11785 ∨ K % 19683 = 11908 ∨ K % 19683 = 11911 ∨ K % 19683 = 12421 ∨ K % 19683 = 12433 ∨ K % 19683 = 12676 ∨ K % 19683 = 12835 ∨ K % 19683 = 12988 ∨ K % 19683 = 13051 ∨ K % 19683 = 13123 ∨ K % 19683 = 13126 ∨ K % 19683 = 13288 ∨ K % 19683 = 13618 ∨ K % 19683 = 13636 ∨ K % 19683 = 13861 ∨ K % 19683 = 13960 ∨ K % 19683 = 13972 ∨ K % 19683 = 14095 ∨ K % 19683 = 14215 ∨ K % 19683 = 14287 ∨ K % 19683 = 14350 ∨ K % 19683 = 14779 ∨ K % 19683 = 14854 ∨ K % 19683 = 14863 ∨ K % 19683 = 14995 ∨ K % 19683 = 15022 ∨ K % 19683 = 15160 ∨ K % 19683 = 15175 ∨ K % 19683 = 15238 ∨ K % 19683 = 15310 ∨ K % 19683 = 15313 ∨ K % 19683 = 15391 ∨ K % 19683 = 15475 ∨ K % 19683 = 15805 ∨ K % 19683 = 16066 ∨ K % 19683 = 16402 ∨ K % 19683 = 16474 ∨ K % 19683 = 16537 ∨ K % 19683 = 16555 ∨ K % 19683 = 16690 ∨ K % 19683 = 16780 ∨ K % 19683 = 16966 ∨ K % 19683 = 17041 ∨ K % 19683 = 17182 ∨ K % 19683 = 17347 ∨ K % 19683 = 17536 ∨ K % 19683 = 17578 ∨ K % 19683 = 17590 ∨ K % 19683 = 17605 ∨ K % 19683 = 17689 ∨ K % 19683 = 17740 ∨ K % 19683 = 18253 ∨ K % 19683 = 18667 ∨ K % 19683 = 18742 ∨ K % 19683 = 18748 ∨ K % 19683 = 18877 ∨ K % 19683 = 18883 ∨ K % 19683 = 18967) :
    digit3 (4^K) 9 = 2 := by
  rcases hK with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · exact fire_of_mod19683 K 40 0 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 94 0 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 109 0 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 193 0 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 244 0 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 283 0 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 325 0 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 733 0 (by decide) (by decide)
      (by rw [show (733:Nat) = 1 + 3*244 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 928 0 (by decide) (by decide)
      (by rw [show (928:Nat) = 1 + 3*309 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1009 0 (by decide) (by decide)
      (by rw [show (1009:Nat) = 1 + 3*336 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1144 0 (by decide) (by decide)
      (by rw [show (1144:Nat) = 1 + 3*381 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1171 0 (by decide) (by decide)
      (by rw [show (1171:Nat) = 1 + 3*390 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1252 0 (by decide) (by decide)
      (by rw [show (1252:Nat) = 1 + 3*417 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1387 0 (by decide) (by decide)
      (by rw [show (1387:Nat) = 1 + 3*462 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1540 0 (by decide) (by decide)
      (by rw [show (1540:Nat) = 1 + 3*513 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1957 0 (by decide) (by decide)
      (by rw [show (1957:Nat) = 1 + 3*652 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2434 0 (by decide) (by decide)
      (by rw [show (2434:Nat) = 1 + 3*811 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2470 0 (by decide) (by decide)
      (by rw [show (2470:Nat) = 1 + 3*823 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2512 0 (by decide) (by decide)
      (by rw [show (2512:Nat) = 1 + 3*837 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2767 0 (by decide) (by decide)
      (by rw [show (2767:Nat) = 1 + 3*922 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2920 0 (by decide) (by decide)
      (by rw [show (2920:Nat) = 1 + 3*973 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3115 0 (by decide) (by decide)
      (by rw [show (3115:Nat) = 1 + 3*1038 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3196 0 (by decide) (by decide)
      (by rw [show (3196:Nat) = 1 + 3*1065 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3331 0 (by decide) (by decide)
      (by rw [show (3331:Nat) = 1 + 3*1110 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3727 0 (by decide) (by decide)
      (by rw [show (3727:Nat) = 1 + 3*1242 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4144 0 (by decide) (by decide)
      (by rw [show (4144:Nat) = 1 + 3*1381 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4162 0 (by decide) (by decide)
      (by rw [show (4162:Nat) = 1 + 3*1387 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4297 0 (by decide) (by decide)
      (by rw [show (4297:Nat) = 1 + 3*1432 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4387 0 (by decide) (by decide)
      (by rw [show (4387:Nat) = 1 + 3*1462 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4495 0 (by decide) (by decide)
      (by rw [show (4495:Nat) = 1 + 3*1498 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4621 0 (by decide) (by decide)
      (by rw [show (4621:Nat) = 1 + 3*1540 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4897 0 (by decide) (by decide)
      (by rw [show (4897:Nat) = 1 + 3*1632 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4954 0 (by decide) (by decide)
      (by rw [show (4954:Nat) = 1 + 3*1651 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5197 0 (by decide) (by decide)
      (by rw [show (5197:Nat) = 1 + 3*1732 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5296 0 (by decide) (by decide)
      (by rw [show (5296:Nat) = 1 + 3*1765 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5617 0 (by decide) (by decide)
      (by rw [show (5617:Nat) = 1 + 3*1872 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5842 0 (by decide) (by decide)
      (by rw [show (5842:Nat) = 1 + 3*1947 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5998 0 (by decide) (by decide)
      (by rw [show (5998:Nat) = 1 + 3*1999 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6157 0 (by decide) (by decide)
      (by rw [show (6157:Nat) = 1 + 3*2052 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6349 0 (by decide) (by decide)
      (by rw [show (6349:Nat) = 1 + 3*2116 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6484 0 (by decide) (by decide)
      (by rw [show (6484:Nat) = 1 + 3*2161 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 121 1 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 280 1 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 364 1 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 436 1 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 523 1 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 595 1 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 730 1 (by decide) (by decide)
      (by rw [show (730:Nat) = 1 + 3*243 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 823 1 (by decide) (by decide)
      (by rw [show (823:Nat) = 1 + 3*274 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 922 1 (by decide) (by decide)
      (by rw [show (922:Nat) = 1 + 3*307 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1003 1 (by decide) (by decide)
      (by rw [show (1003:Nat) = 1 + 3*334 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1225 1 (by decide) (by decide)
      (by rw [show (1225:Nat) = 1 + 3*408 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1243 1 (by decide) (by decide)
      (by rw [show (1243:Nat) = 1 + 3*414 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1468 1 (by decide) (by decide)
      (by rw [show (1468:Nat) = 1 + 3*489 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1624 1 (by decide) (by decide)
      (by rw [show (1624:Nat) = 1 + 3*541 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1783 1 (by decide) (by decide)
      (by rw [show (1783:Nat) = 1 + 3*594 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2467 1 (by decide) (by decide)
      (by rw [show (2467:Nat) = 1 + 3*822 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2551 1 (by decide) (by decide)
      (by rw [show (2551:Nat) = 1 + 3*850 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2623 1 (by decide) (by decide)
      (by rw [show (2623:Nat) = 1 + 3*874 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2782 1 (by decide) (by decide)
      (by rw [show (2782:Nat) = 1 + 3*927 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2917 1 (by decide) (by decide)
      (by rw [show (2917:Nat) = 1 + 3*972 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3163 1 (by decide) (by decide)
      (by rw [show (3163:Nat) = 1 + 3*1054 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3190 1 (by decide) (by decide)
      (by rw [show (3190:Nat) = 1 + 3*1063 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3412 1 (by decide) (by decide)
      (by rw [show (3412:Nat) = 1 + 3*1137 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3673 1 (by decide) (by decide)
      (by rw [show (3673:Nat) = 1 + 3*1224 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3685 1 (by decide) (by decide)
      (by rw [show (3685:Nat) = 1 + 3*1228 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4888 1 (by decide) (by decide)
      (by rw [show (4888:Nat) = 1 + 3*1629 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5113 1 (by decide) (by decide)
      (by rw [show (5113:Nat) = 1 + 3*1704 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5212 1 (by decide) (by decide)
      (by rw [show (5212:Nat) = 1 + 3*1737 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5224 1 (by decide) (by decide)
      (by rw [show (5224:Nat) = 1 + 3*1741 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5347 1 (by decide) (by decide)
      (by rw [show (5347:Nat) = 1 + 3*1782 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5350 1 (by decide) (by decide)
      (by rw [show (5350:Nat) = 1 + 3*1783 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5860 1 (by decide) (by decide)
      (by rw [show (5860:Nat) = 1 + 3*1953 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5872 1 (by decide) (by decide)
      (by rw [show (5872:Nat) = 1 + 3*1957 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6115 1 (by decide) (by decide)
      (by rw [show (6115:Nat) = 1 + 3*2038 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6274 1 (by decide) (by decide)
      (by rw [show (6274:Nat) = 1 + 3*2091 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6427 1 (by decide) (by decide)
      (by rw [show (6427:Nat) = 1 + 3*2142 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 6490 1 (by decide) (by decide)
      (by rw [show (6490:Nat) = 1 + 3*2163 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 166 2 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 514 2 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 739 2 (by decide) (by decide)
      (by rw [show (739:Nat) = 1 + 3*246 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 838 2 (by decide) (by decide)
      (by rw [show (838:Nat) = 1 + 3*279 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 850 2 (by decide) (by decide)
      (by rw [show (850:Nat) = 1 + 3*283 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 973 2 (by decide) (by decide)
      (by rw [show (973:Nat) = 1 + 3*324 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1093 2 (by decide) (by decide)
      (by rw [show (1093:Nat) = 1 + 3*364 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1165 2 (by decide) (by decide)
      (by rw [show (1165:Nat) = 1 + 3*388 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1228 2 (by decide) (by decide)
      (by rw [show (1228:Nat) = 1 + 3*409 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1657 2 (by decide) (by decide)
      (by rw [show (1657:Nat) = 1 + 3*552 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1732 2 (by decide) (by decide)
      (by rw [show (1732:Nat) = 1 + 3*577 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1741 2 (by decide) (by decide)
      (by rw [show (1741:Nat) = 1 + 3*580 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1873 2 (by decide) (by decide)
      (by rw [show (1873:Nat) = 1 + 3*624 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 1900 2 (by decide) (by decide)
      (by rw [show (1900:Nat) = 1 + 3*633 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2038 2 (by decide) (by decide)
      (by rw [show (2038:Nat) = 1 + 3*679 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2053 2 (by decide) (by decide)
      (by rw [show (2053:Nat) = 1 + 3*684 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2116 2 (by decide) (by decide)
      (by rw [show (2116:Nat) = 1 + 3*705 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2188 2 (by decide) (by decide)
      (by rw [show (2188:Nat) = 1 + 3*729 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2191 2 (by decide) (by decide)
      (by rw [show (2191:Nat) = 1 + 3*730 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2269 2 (by decide) (by decide)
      (by rw [show (2269:Nat) = 1 + 3*756 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2353 2 (by decide) (by decide)
      (by rw [show (2353:Nat) = 1 + 3*784 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2683 2 (by decide) (by decide)
      (by rw [show (2683:Nat) = 1 + 3*894 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 2944 2 (by decide) (by decide)
      (by rw [show (2944:Nat) = 1 + 3*981 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3280 2 (by decide) (by decide)
      (by rw [show (3280:Nat) = 1 + 3*1093 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3352 2 (by decide) (by decide)
      (by rw [show (3352:Nat) = 1 + 3*1117 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3415 2 (by decide) (by decide)
      (by rw [show (3415:Nat) = 1 + 3*1138 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3433 2 (by decide) (by decide)
      (by rw [show (3433:Nat) = 1 + 3*1144 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3568 2 (by decide) (by decide)
      (by rw [show (3568:Nat) = 1 + 3*1189 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3658 2 (by decide) (by decide)
      (by rw [show (3658:Nat) = 1 + 3*1219 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3844 2 (by decide) (by decide)
      (by rw [show (3844:Nat) = 1 + 3*1281 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 3919 2 (by decide) (by decide)
      (by rw [show (3919:Nat) = 1 + 3*1306 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4060 2 (by decide) (by decide)
      (by rw [show (4060:Nat) = 1 + 3*1353 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4225 2 (by decide) (by decide)
      (by rw [show (4225:Nat) = 1 + 3*1408 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4414 2 (by decide) (by decide)
      (by rw [show (4414:Nat) = 1 + 3*1471 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4456 2 (by decide) (by decide)
      (by rw [show (4456:Nat) = 1 + 3*1485 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4468 2 (by decide) (by decide)
      (by rw [show (4468:Nat) = 1 + 3*1489 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4483 2 (by decide) (by decide)
      (by rw [show (4483:Nat) = 1 + 3*1494 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4567 2 (by decide) (by decide)
      (by rw [show (4567:Nat) = 1 + 3*1522 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 4618 2 (by decide) (by decide)
      (by rw [show (4618:Nat) = 1 + 3*1539 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5131 2 (by decide) (by decide)
      (by rw [show (5131:Nat) = 1 + 3*1710 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5545 2 (by decide) (by decide)
      (by rw [show (5545:Nat) = 1 + 3*1848 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5620 2 (by decide) (by decide)
      (by rw [show (5620:Nat) = 1 + 3*1873 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5626 2 (by decide) (by decide)
      (by rw [show (5626:Nat) = 1 + 3*1875 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5755 2 (by decide) (by decide)
      (by rw [show (5755:Nat) = 1 + 3*1918 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5761 2 (by decide) (by decide)
      (by rw [show (5761:Nat) = 1 + 3*1920 from by decide, wt_row_nine_read]; decide)
      (by omega)
  · exact fire_of_mod19683 K 5845 2 (by decide) (by decide)
      (by rw [show (5845:Nat) = 1 + 3*1948 from by decide, wt_row_nine_read]; decide)
      (by omega)

/-- **CASCADE LEVEL NINE, KILL CHAIN.** -/
theorem no22_of_cascade_eight (K : Nat)
    (h : K % 19683 = 40 ∨ K % 19683 = 94 ∨ K % 19683 = 109 ∨ K % 19683 = 193 ∨ K % 19683 = 244 ∨ K % 19683 = 283 ∨ K % 19683 = 325 ∨ K % 19683 = 733 ∨ K % 19683 = 928 ∨ K % 19683 = 1009 ∨ K % 19683 = 1144 ∨ K % 19683 = 1171 ∨ K % 19683 = 1252 ∨ K % 19683 = 1387 ∨ K % 19683 = 1540 ∨ K % 19683 = 1957 ∨ K % 19683 = 2434 ∨ K % 19683 = 2470 ∨ K % 19683 = 2512 ∨ K % 19683 = 2767 ∨ K % 19683 = 2920 ∨ K % 19683 = 3115 ∨ K % 19683 = 3196 ∨ K % 19683 = 3331 ∨ K % 19683 = 3727 ∨ K % 19683 = 4144 ∨ K % 19683 = 4162 ∨ K % 19683 = 4297 ∨ K % 19683 = 4387 ∨ K % 19683 = 4495 ∨ K % 19683 = 4621 ∨ K % 19683 = 4897 ∨ K % 19683 = 4954 ∨ K % 19683 = 5197 ∨ K % 19683 = 5296 ∨ K % 19683 = 5617 ∨ K % 19683 = 5842 ∨ K % 19683 = 5998 ∨ K % 19683 = 6157 ∨ K % 19683 = 6349 ∨ K % 19683 = 6484 ∨ K % 19683 = 6574 ∨ K % 19683 = 6682 ∨ K % 19683 = 6841 ∨ K % 19683 = 6925 ∨ K % 19683 = 6997 ∨ K % 19683 = 7084 ∨ K % 19683 = 7156 ∨ K % 19683 = 7291 ∨ K % 19683 = 7384 ∨ K % 19683 = 7483 ∨ K % 19683 = 7564 ∨ K % 19683 = 7786 ∨ K % 19683 = 7804 ∨ K % 19683 = 8029 ∨ K % 19683 = 8185 ∨ K % 19683 = 8344 ∨ K % 19683 = 9028 ∨ K % 19683 = 9112 ∨ K % 19683 = 9184 ∨ K % 19683 = 9343 ∨ K % 19683 = 9478 ∨ K % 19683 = 9724 ∨ K % 19683 = 9751 ∨ K % 19683 = 9973 ∨ K % 19683 = 10234 ∨ K % 19683 = 10246 ∨ K % 19683 = 11449 ∨ K % 19683 = 11674 ∨ K % 19683 = 11773 ∨ K % 19683 = 11785 ∨ K % 19683 = 11908 ∨ K % 19683 = 11911 ∨ K % 19683 = 12421 ∨ K % 19683 = 12433 ∨ K % 19683 = 12676 ∨ K % 19683 = 12835 ∨ K % 19683 = 12988 ∨ K % 19683 = 13051 ∨ K % 19683 = 13123 ∨ K % 19683 = 13126 ∨ K % 19683 = 13288 ∨ K % 19683 = 13618 ∨ K % 19683 = 13636 ∨ K % 19683 = 13861 ∨ K % 19683 = 13960 ∨ K % 19683 = 13972 ∨ K % 19683 = 14095 ∨ K % 19683 = 14215 ∨ K % 19683 = 14287 ∨ K % 19683 = 14350 ∨ K % 19683 = 14779 ∨ K % 19683 = 14854 ∨ K % 19683 = 14863 ∨ K % 19683 = 14995 ∨ K % 19683 = 15022 ∨ K % 19683 = 15160 ∨ K % 19683 = 15175 ∨ K % 19683 = 15238 ∨ K % 19683 = 15310 ∨ K % 19683 = 15313 ∨ K % 19683 = 15391 ∨ K % 19683 = 15475 ∨ K % 19683 = 15805 ∨ K % 19683 = 16066 ∨ K % 19683 = 16402 ∨ K % 19683 = 16474 ∨ K % 19683 = 16537 ∨ K % 19683 = 16555 ∨ K % 19683 = 16690 ∨ K % 19683 = 16780 ∨ K % 19683 = 16966 ∨ K % 19683 = 17041 ∨ K % 19683 = 17182 ∨ K % 19683 = 17347 ∨ K % 19683 = 17536 ∨ K % 19683 = 17578 ∨ K % 19683 = 17590 ∨ K % 19683 = 17605 ∨ K % 19683 = 17689 ∨ K % 19683 = 17740 ∨ K % 19683 = 18253 ∨ K % 19683 = 18667 ∨ K % 19683 = 18742 ∨ K % 19683 = 18748 ∨ K % 19683 = 18877 ∨ K % 19683 = 18883 ∨ K % 19683 = 18967) :
    noTernaryTwo (4^K) = false := by
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inl h0))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inl h1)))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inl h2))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13)))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h14))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15)))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h16))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h17)))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h19)))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h20))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h21)))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h22))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h24))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h25)))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h26))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h27)))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h28))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h29)))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h30))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h31)))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h32))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h33)))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h34))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h35)))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h36))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h37)))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h38))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h39)))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h40))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h41)))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h42))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h43)))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h44))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h45)))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h46))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h47)))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h48))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h49)))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h50))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h51)))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h52))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h53)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h54))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h55)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h56))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h57)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h58))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h59)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h60))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h61)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h64))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h65)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h66))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h67)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h68))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h69)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h70))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h71)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h72))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h73)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h74))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h75)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h76))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h77)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h78))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h79)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h80))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h81)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h82))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h83)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h84))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h85)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h86))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h87)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h88))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h89)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h90))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h91)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h92))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h93)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h94))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h95)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h96))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h97)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h98))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h99)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h100))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h101)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h102))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h103)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h104))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h105)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h106))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h107)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h108))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h109)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h110))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h111)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h112))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h113)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h114))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h115)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h116))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h117)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h118))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h119)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h120))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h121)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h122))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h124))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h125)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-! ## §6 The re-doubled Cantorian pin — the 256-survivor map -/

/-- **THE CANTORIAN PIN, LEVEL NINE.** -/
theorem cantorian_dust_mod_19683 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 19683 = 1 ∨ K % 19683 = 4 ∨ K % 19683 = 13 ∨ K % 19683 = 121 ∨ K % 19683 = 166 ∨ K % 19683 = 280 ∨ K % 19683 = 364 ∨ K % 19683 = 436 ∨ K % 19683 = 496 ∨ K % 19683 = 514 ∨ K % 19683 = 523 ∨ K % 19683 = 595 ∨ K % 19683 = 730 ∨ K % 19683 = 739 ∨ K % 19683 = 823 ∨ K % 19683 = 838 ∨ K % 19683 = 850 ∨ K % 19683 = 922 ∨ K % 19683 = 973 ∨ K % 19683 = 1003 ∨ K % 19683 = 1093 ∨ K % 19683 = 1165 ∨ K % 19683 = 1225 ∨ K % 19683 = 1228 ∨ K % 19683 = 1243 ∨ K % 19683 = 1468 ∨ K % 19683 = 1624 ∨ K % 19683 = 1657 ∨ K % 19683 = 1732 ∨ K % 19683 = 1741 ∨ K % 19683 = 1783 ∨ K % 19683 = 1873 ∨ K % 19683 = 1900 ∨ K % 19683 = 2038 ∨ K % 19683 = 2053 ∨ K % 19683 = 2116 ∨ K % 19683 = 2188 ∨ K % 19683 = 2191 ∨ K % 19683 = 2269 ∨ K % 19683 = 2353 ∨ K % 19683 = 2467 ∨ K % 19683 = 2551 ∨ K % 19683 = 2623 ∨ K % 19683 = 2683 ∨ K % 19683 = 2782 ∨ K % 19683 = 2917 ∨ K % 19683 = 2944 ∨ K % 19683 = 3163 ∨ K % 19683 = 3190 ∨ K % 19683 = 3280 ∨ K % 19683 = 3352 ∨ K % 19683 = 3412 ∨ K % 19683 = 3415 ∨ K % 19683 = 3433 ∨ K % 19683 = 3568 ∨ K % 19683 = 3658 ∨ K % 19683 = 3673 ∨ K % 19683 = 3685 ∨ K % 19683 = 3844 ∨ K % 19683 = 3919 ∨ K % 19683 = 4060 ∨ K % 19683 = 4225 ∨ K % 19683 = 4414 ∨ K % 19683 = 4456 ∨ K % 19683 = 4468 ∨ K % 19683 = 4483 ∨ K % 19683 = 4567 ∨ K % 19683 = 4618 ∨ K % 19683 = 4888 ∨ K % 19683 = 5113 ∨ K % 19683 = 5131 ∨ K % 19683 = 5212 ∨ K % 19683 = 5224 ∨ K % 19683 = 5347 ∨ K % 19683 = 5350 ∨ K % 19683 = 5545 ∨ K % 19683 = 5620 ∨ K % 19683 = 5626 ∨ K % 19683 = 5755 ∨ K % 19683 = 5761 ∨ K % 19683 = 5845 ∨ K % 19683 = 5860 ∨ K % 19683 = 5872 ∨ K % 19683 = 6115 ∨ K % 19683 = 6274 ∨ K % 19683 = 6427 ∨ K % 19683 = 6490 ∨ K % 19683 = 6562 ∨ K % 19683 = 6565 ∨ K % 19683 = 6601 ∨ K % 19683 = 6655 ∨ K % 19683 = 6670 ∨ K % 19683 = 6727 ∨ K % 19683 = 6754 ∨ K % 19683 = 6805 ∨ K % 19683 = 6844 ∨ K % 19683 = 6886 ∨ K % 19683 = 7057 ∨ K % 19683 = 7075 ∨ K % 19683 = 7294 ∨ K % 19683 = 7300 ∨ K % 19683 = 7399 ∨ K % 19683 = 7411 ∨ K % 19683 = 7489 ∨ K % 19683 = 7534 ∨ K % 19683 = 7570 ∨ K % 19683 = 7654 ∨ K % 19683 = 7705 ∨ K % 19683 = 7726 ∨ K % 19683 = 7732 ∨ K % 19683 = 7789 ∨ K % 19683 = 7813 ∨ K % 19683 = 7948 ∨ K % 19683 = 8101 ∨ K % 19683 = 8218 ∨ K % 19683 = 8293 ∨ K % 19683 = 8302 ∨ K % 19683 = 8434 ∨ K % 19683 = 8461 ∨ K % 19683 = 8518 ∨ K % 19683 = 8599 ∨ K % 19683 = 8614 ∨ K % 19683 = 8677 ∨ K % 19683 = 8749 ∨ K % 19683 = 8752 ∨ K % 19683 = 8830 ∨ K % 19683 = 8914 ∨ K % 19683 = 8995 ∨ K % 19683 = 9031 ∨ K % 19683 = 9073 ∨ K % 19683 = 9244 ∨ K % 19683 = 9328 ∨ K % 19683 = 9481 ∨ K % 19683 = 9505 ∨ K % 19683 = 9676 ∨ K % 19683 = 9757 ∨ K % 19683 = 9841 ∨ K % 19683 = 9892 ∨ K % 19683 = 9913 ∨ K % 19683 = 9976 ∨ K % 19683 = 9994 ∨ K % 19683 = 10129 ∨ K % 19683 = 10219 ∨ K % 19683 = 10288 ∨ K % 19683 = 10405 ∨ K % 19683 = 10480 ∨ K % 19683 = 10621 ∨ K % 19683 = 10705 ∨ K % 19683 = 10723 ∨ K % 19683 = 10786 ∨ K % 19683 = 10858 ∨ K % 19683 = 10948 ∨ K % 19683 = 10975 ∨ K % 19683 = 11017 ∨ K % 19683 = 11029 ∨ K % 19683 = 11044 ∨ K % 19683 = 11056 ∨ K % 19683 = 11128 ∨ K % 19683 = 11179 ∨ K % 19683 = 11182 ∨ K % 19683 = 11458 ∨ K % 19683 = 11515 ∨ K % 19683 = 11692 ∨ K % 19683 = 11758 ∨ K % 19683 = 11857 ∨ K % 19683 = 12106 ∨ K % 19683 = 12178 ∨ K % 19683 = 12181 ∨ K % 19683 = 12187 ∨ K % 19683 = 12316 ∨ K % 19683 = 12322 ∨ K % 19683 = 12403 ∨ K % 19683 = 12406 ∨ K % 19683 = 12559 ∨ K % 19683 = 12718 ∨ K % 19683 = 12910 ∨ K % 19683 = 13045 ∨ K % 19683 = 13135 ∨ K % 19683 = 13162 ∨ K % 19683 = 13216 ∨ K % 19683 = 13231 ∨ K % 19683 = 13243 ∨ K % 19683 = 13315 ∨ K % 19683 = 13366 ∨ K % 19683 = 13402 ∨ K % 19683 = 13405 ∨ K % 19683 = 13447 ∨ K % 19683 = 13486 ∨ K % 19683 = 13558 ∨ K % 19683 = 13645 ∨ K % 19683 = 13717 ∨ K % 19683 = 13852 ∨ K % 19683 = 13855 ∨ K % 19683 = 13945 ∨ K % 19683 = 14044 ∨ K % 19683 = 14050 ∨ K % 19683 = 14125 ∨ K % 19683 = 14131 ∨ K % 19683 = 14266 ∨ K % 19683 = 14293 ∨ K % 19683 = 14347 ∨ K % 19683 = 14365 ∨ K % 19683 = 14374 ∨ K % 19683 = 14509 ∨ K % 19683 = 14590 ∨ K % 19683 = 14662 ∨ K % 19683 = 14746 ∨ K % 19683 = 14905 ∨ K % 19683 = 15079 ∨ K % 19683 = 15556 ∨ K % 19683 = 15589 ∨ K % 19683 = 15592 ∨ K % 19683 = 15634 ∨ K % 19683 = 15673 ∨ K % 19683 = 15745 ∨ K % 19683 = 15889 ∨ K % 19683 = 15904 ∨ K % 19683 = 16039 ∨ K % 19683 = 16042 ∨ K % 19683 = 16237 ∨ K % 19683 = 16285 ∨ K % 19683 = 16312 ∨ K % 19683 = 16318 ∨ K % 19683 = 16453 ∨ K % 19683 = 16534 ∨ K % 19683 = 16795 ∨ K % 19683 = 16807 ∨ K % 19683 = 16849 ∨ K % 19683 = 17266 ∨ K % 19683 = 17284 ∨ K % 19683 = 17419 ∨ K % 19683 = 17509 ∨ K % 19683 = 17617 ∨ K % 19683 = 17743 ∨ K % 19683 = 18010 ∨ K % 19683 = 18019 ∨ K % 19683 = 18076 ∨ K % 19683 = 18235 ∨ K % 19683 = 18319 ∨ K % 19683 = 18334 ∨ K % 19683 = 18346 ∨ K % 19683 = 18418 ∨ K % 19683 = 18469 ∨ K % 19683 = 18472 ∨ K % 19683 = 18739 ∨ K % 19683 = 18964 ∨ K % 19683 = 18982 ∨ K % 19683 = 18994 ∨ K % 19683 = 19120 ∨ K % 19683 = 19237 ∨ K % 19683 = 19279 ∨ K % 19683 = 19396 ∨ K % 19683 = 19471 ∨ K % 19683 = 19549 ∨ K % 19683 = 19606 ∨ K % 19683 = 19612 := by
  have h729 := GSTTheActConstruction.cantorian_dust_mod_729 K hd hc
  have hrow7 := hc 7 (by omega)
  have hrow8 := hc 8 (by omega)
  have hrow9 := hc 9 (by omega)
  have hf70 : K % 2187 ≠ 10 := fun h => absurd
    (ladder_fire_mod2187 K 10 0 (by decide) (by decide)
      (by rw [show (10:Nat) = 1 + 3*3 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf71 : K % 2187 ≠ 28 := fun h => absurd
    (ladder_fire_mod2187 K 28 0 (by decide) (by decide)
      (by rw [show (28:Nat) = 1 + 3*9 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf72 : K % 2187 ≠ 199 := fun h => absurd
    (ladder_fire_mod2187 K 199 0 (by decide) (by decide)
      (by rw [show (199:Nat) = 1 + 3*66 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf73 : K % 2187 ≠ 274 := fun h => absurd
    (ladder_fire_mod2187 K 274 0 (by decide) (by decide)
      (by rw [show (274:Nat) = 1 + 3*91 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf74 : K % 2187 ≠ 415 := fun h => absurd
    (ladder_fire_mod2187 K 415 0 (by decide) (by decide)
      (by rw [show (415:Nat) = 1 + 3*138 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf75 : K % 2187 ≠ 442 := fun h => absurd
    (ladder_fire_mod2187 K 442 0 (by decide) (by decide)
      (by rw [show (442:Nat) = 1 + 3*147 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf76 : K % 2187 ≠ 499 := fun h => absurd
    (ladder_fire_mod2187 K 499 0 (by decide) (by decide)
      (by rw [show (499:Nat) = 1 + 3*166 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf77 : K % 2187 ≠ 517 := fun h => absurd
    (ladder_fire_mod2187 K 517 0 (by decide) (by decide)
      (by rw [show (517:Nat) = 1 + 3*172 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf78 : K % 2187 ≠ 652 := fun h => absurd
    (ladder_fire_mod2187 K 652 0 (by decide) (by decide)
      (by rw [show (652:Nat) = 1 + 3*217 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf79 : K % 2187 ≠ 658 := fun h => absurd
    (ladder_fire_mod2187 K 658 0 (by decide) (by decide)
      (by rw [show (658:Nat) = 1 + 3*219 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf710 : K % 2187 ≠ 742 := fun h => absurd
    (ladder_fire_mod2187 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf711 : K % 2187 ≠ 769 := fun h => absurd
    (ladder_fire_mod2187 K 40 1 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf712 : K % 2187 ≠ 811 := fun h => absurd
    (ladder_fire_mod2187 K 82 1 (by decide) (by decide)
      (by rw [show (82:Nat) = 1 + 3*27 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf713 : K % 2187 ≠ 895 := fun h => absurd
    (ladder_fire_mod2187 K 166 1 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf714 : K % 2187 ≠ 1012 := fun h => absurd
    (ladder_fire_mod2187 K 283 1 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf715 : K % 2187 ≠ 1054 := fun h => absurd
    (ladder_fire_mod2187 K 325 1 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf716 : K % 2187 ≠ 1309 := fun h => absurd
    (ladder_fire_mod2187 K 580 1 (by decide) (by decide)
      (by rw [show (580:Nat) = 1 + 3*193 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf717 : K % 2187 ≠ 1324 := fun h => absurd
    (ladder_fire_mod2187 K 595 1 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf718 : K % 2187 ≠ 1459 := fun h => absurd
    (ladder_fire_mod2187 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf719 : K % 2187 ≠ 1462 := fun h => absurd
    (ladder_fire_mod2187 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf720 : K % 2187 ≠ 1552 := fun h => absurd
    (ladder_fire_mod2187 K 94 2 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf721 : K % 2187 ≠ 1567 := fun h => absurd
    (ladder_fire_mod2187 K 109 2 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf722 : K % 2187 ≠ 1579 := fun h => absurd
    (ladder_fire_mod2187 K 121 2 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf723 : K % 2187 ≠ 1651 := fun h => absurd
    (ladder_fire_mod2187 K 193 2 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf724 : K % 2187 ≠ 1702 := fun h => absurd
    (ladder_fire_mod2187 K 244 2 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf725 : K % 2187 ≠ 1705 := fun h => absurd
    (ladder_fire_mod2187 K 247 2 (by decide) (by decide)
      (by rw [show (247:Nat) = 1 + 3*82 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf726 : K % 2187 ≠ 1738 := fun h => absurd
    (ladder_fire_mod2187 K 280 2 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf727 : K % 2187 ≠ 1822 := fun h => absurd
    (ladder_fire_mod2187 K 364 2 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf728 : K % 2187 ≠ 1894 := fun h => absurd
    (ladder_fire_mod2187 K 436 2 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf729 : K % 2187 ≠ 1954 := fun h => absurd
    (ladder_fire_mod2187 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf730 : K % 2187 ≠ 1972 := fun h => absurd
    (ladder_fire_mod2187 K 514 2 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf731 : K % 2187 ≠ 1981 := fun h => absurd
    (ladder_fire_mod2187 K 523 2 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide,
        GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega)) hrow7
  have hf80 : K % 6561 ≠ 82 := fun h => absurd
    (ladder_fire_mod6561 K 82 0 (by decide) (by decide)
      (by rw [show (82:Nat) = 1 + 3*27 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf81 : K % 6561 ≠ 247 := fun h => absurd
    (ladder_fire_mod6561 K 247 0 (by decide) (by decide)
      (by rw [show (247:Nat) = 1 + 3*82 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf82 : K % 6561 ≠ 580 := fun h => absurd
    (ladder_fire_mod6561 K 580 0 (by decide) (by decide)
      (by rw [show (580:Nat) = 1 + 3*193 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf83 : K % 6561 ≠ 757 := fun h => absurd
    (ladder_fire_mod6561 K 757 0 (by decide) (by decide)
      (by rw [show (757:Nat) = 1 + 3*252 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf84 : K % 6561 ≠ 976 := fun h => absurd
    (ladder_fire_mod6561 K 976 0 (by decide) (by decide)
      (by rw [show (976:Nat) = 1 + 3*325 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf85 : K % 6561 ≠ 1246 := fun h => absurd
    (ladder_fire_mod6561 K 1246 0 (by decide) (by decide)
      (by rw [show (1246:Nat) = 1 + 3*415 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf86 : K % 6561 ≠ 1381 := fun h => absurd
    (ladder_fire_mod6561 K 1381 0 (by decide) (by decide)
      (by rw [show (1381:Nat) = 1 + 3*460 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf87 : K % 6561 ≠ 1471 := fun h => absurd
    (ladder_fire_mod6561 K 1471 0 (by decide) (by decide)
      (by rw [show (1471:Nat) = 1 + 3*490 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf88 : K % 6561 ≠ 1486 := fun h => absurd
    (ladder_fire_mod6561 K 1486 0 (by decide) (by decide)
      (by rw [show (1486:Nat) = 1 + 3*495 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf89 : K % 6561 ≠ 1498 := fun h => absurd
    (ladder_fire_mod6561 K 1498 0 (by decide) (by decide)
      (by rw [show (1498:Nat) = 1 + 3*499 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf810 : K % 6561 ≠ 1975 := fun h => absurd
    (ladder_fire_mod6561 K 1975 0 (by decide) (by decide)
      (by rw [show (1975:Nat) = 1 + 3*658 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf811 : K % 6561 ≠ 2110 := fun h => absurd
    (ladder_fire_mod6561 K 2110 0 (by decide) (by decide)
      (by rw [show (2110:Nat) = 1 + 3*703 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf812 : K % 6561 ≠ 2200 := fun h => absurd
    (ladder_fire_mod6561 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf813 : K % 6561 ≠ 2227 := fun h => absurd
    (ladder_fire_mod6561 K 40 1 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf814 : K % 6561 ≠ 2281 := fun h => absurd
    (ladder_fire_mod6561 K 94 1 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf815 : K % 6561 ≠ 2296 := fun h => absurd
    (ladder_fire_mod6561 K 109 1 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf816 : K % 6561 ≠ 2308 := fun h => absurd
    (ladder_fire_mod6561 K 121 1 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf817 : K % 6561 ≠ 2380 := fun h => absurd
    (ladder_fire_mod6561 K 193 1 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf818 : K % 6561 ≠ 2431 := fun h => absurd
    (ladder_fire_mod6561 K 244 1 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf819 : K % 6561 ≠ 2701 := fun h => absurd
    (ladder_fire_mod6561 K 514 1 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf820 : K % 6561 ≠ 2710 := fun h => absurd
    (ladder_fire_mod6561 K 523 1 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf821 : K % 6561 ≠ 2926 := fun h => absurd
    (ladder_fire_mod6561 K 739 1 (by decide) (by decide)
      (by rw [show (739:Nat) = 1 + 3*246 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf822 : K % 6561 ≠ 3010 := fun h => absurd
    (ladder_fire_mod6561 K 823 1 (by decide) (by decide)
      (by rw [show (823:Nat) = 1 + 3*274 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf823 : K % 6561 ≠ 3025 := fun h => absurd
    (ladder_fire_mod6561 K 838 1 (by decide) (by decide)
      (by rw [show (838:Nat) = 1 + 3*279 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf824 : K % 6561 ≠ 3037 := fun h => absurd
    (ladder_fire_mod6561 K 850 1 (by decide) (by decide)
      (by rw [show (850:Nat) = 1 + 3*283 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf825 : K % 6561 ≠ 3109 := fun h => absurd
    (ladder_fire_mod6561 K 922 1 (by decide) (by decide)
      (by rw [show (922:Nat) = 1 + 3*307 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf826 : K % 6561 ≠ 3160 := fun h => absurd
    (ladder_fire_mod6561 K 973 1 (by decide) (by decide)
      (by rw [show (973:Nat) = 1 + 3*324 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf827 : K % 6561 ≠ 3358 := fun h => absurd
    (ladder_fire_mod6561 K 1171 1 (by decide) (by decide)
      (by rw [show (1171:Nat) = 1 + 3*390 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf828 : K % 6561 ≠ 3430 := fun h => absurd
    (ladder_fire_mod6561 K 1243 1 (by decide) (by decide)
      (by rw [show (1243:Nat) = 1 + 3*414 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf829 : K % 6561 ≠ 3439 := fun h => absurd
    (ladder_fire_mod6561 K 1252 1 (by decide) (by decide)
      (by rw [show (1252:Nat) = 1 + 3*417 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf830 : K % 6561 ≠ 3574 := fun h => absurd
    (ladder_fire_mod6561 K 1387 1 (by decide) (by decide)
      (by rw [show (1387:Nat) = 1 + 3*462 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf831 : K % 6561 ≠ 3655 := fun h => absurd
    (ladder_fire_mod6561 K 1468 1 (by decide) (by decide)
      (by rw [show (1468:Nat) = 1 + 3*489 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf832 : K % 6561 ≠ 3811 := fun h => absurd
    (ladder_fire_mod6561 K 1624 1 (by decide) (by decide)
      (by rw [show (1624:Nat) = 1 + 3*541 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf833 : K % 6561 ≠ 3928 := fun h => absurd
    (ladder_fire_mod6561 K 1741 1 (by decide) (by decide)
      (by rw [show (1741:Nat) = 1 + 3*580 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf834 : K % 6561 ≠ 3970 := fun h => absurd
    (ladder_fire_mod6561 K 1783 1 (by decide) (by decide)
      (by rw [show (1783:Nat) = 1 + 3*594 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf835 : K % 6561 ≠ 4087 := fun h => absurd
    (ladder_fire_mod6561 K 1900 1 (by decide) (by decide)
      (by rw [show (1900:Nat) = 1 + 3*633 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf836 : K % 6561 ≠ 4240 := fun h => absurd
    (ladder_fire_mod6561 K 2053 1 (by decide) (by decide)
      (by rw [show (2053:Nat) = 1 + 3*684 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf837 : K % 6561 ≠ 4303 := fun h => absurd
    (ladder_fire_mod6561 K 2116 1 (by decide) (by decide)
      (by rw [show (2116:Nat) = 1 + 3*705 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf838 : K % 6561 ≠ 4375 := fun h => absurd
    (ladder_fire_mod6561 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf839 : K % 6561 ≠ 4378 := fun h => absurd
    (ladder_fire_mod6561 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf840 : K % 6561 ≠ 4540 := fun h => absurd
    (ladder_fire_mod6561 K 166 2 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf841 : K % 6561 ≠ 4654 := fun h => absurd
    (ladder_fire_mod6561 K 280 2 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf842 : K % 6561 ≠ 4657 := fun h => absurd
    (ladder_fire_mod6561 K 283 2 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf843 : K % 6561 ≠ 4699 := fun h => absurd
    (ladder_fire_mod6561 K 325 2 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf844 : K % 6561 ≠ 4738 := fun h => absurd
    (ladder_fire_mod6561 K 364 2 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf845 : K % 6561 ≠ 4810 := fun h => absurd
    (ladder_fire_mod6561 K 436 2 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf846 : K % 6561 ≠ 4870 := fun h => absurd
    (ladder_fire_mod6561 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf847 : K % 6561 ≠ 4969 := fun h => absurd
    (ladder_fire_mod6561 K 595 2 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf848 : K % 6561 ≠ 5104 := fun h => absurd
    (ladder_fire_mod6561 K 730 2 (by decide) (by decide)
      (by rw [show (730:Nat) = 1 + 3*243 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf849 : K % 6561 ≠ 5107 := fun h => absurd
    (ladder_fire_mod6561 K 733 2 (by decide) (by decide)
      (by rw [show (733:Nat) = 1 + 3*244 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf850 : K % 6561 ≠ 5302 := fun h => absurd
    (ladder_fire_mod6561 K 928 2 (by decide) (by decide)
      (by rw [show (928:Nat) = 1 + 3*309 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf851 : K % 6561 ≠ 5377 := fun h => absurd
    (ladder_fire_mod6561 K 1003 2 (by decide) (by decide)
      (by rw [show (1003:Nat) = 1 + 3*334 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf852 : K % 6561 ≠ 5383 := fun h => absurd
    (ladder_fire_mod6561 K 1009 2 (by decide) (by decide)
      (by rw [show (1009:Nat) = 1 + 3*336 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf853 : K % 6561 ≠ 5467 := fun h => absurd
    (ladder_fire_mod6561 K 1093 2 (by decide) (by decide)
      (by rw [show (1093:Nat) = 1 + 3*364 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf854 : K % 6561 ≠ 5518 := fun h => absurd
    (ladder_fire_mod6561 K 1144 2 (by decide) (by decide)
      (by rw [show (1144:Nat) = 1 + 3*381 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf855 : K % 6561 ≠ 5539 := fun h => absurd
    (ladder_fire_mod6561 K 1165 2 (by decide) (by decide)
      (by rw [show (1165:Nat) = 1 + 3*388 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf856 : K % 6561 ≠ 5599 := fun h => absurd
    (ladder_fire_mod6561 K 1225 2 (by decide) (by decide)
      (by rw [show (1225:Nat) = 1 + 3*408 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf857 : K % 6561 ≠ 5602 := fun h => absurd
    (ladder_fire_mod6561 K 1228 2 (by decide) (by decide)
      (by rw [show (1228:Nat) = 1 + 3*409 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf858 : K % 6561 ≠ 5914 := fun h => absurd
    (ladder_fire_mod6561 K 1540 2 (by decide) (by decide)
      (by rw [show (1540:Nat) = 1 + 3*513 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf859 : K % 6561 ≠ 6031 := fun h => absurd
    (ladder_fire_mod6561 K 1657 2 (by decide) (by decide)
      (by rw [show (1657:Nat) = 1 + 3*552 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf860 : K % 6561 ≠ 6106 := fun h => absurd
    (ladder_fire_mod6561 K 1732 2 (by decide) (by decide)
      (by rw [show (1732:Nat) = 1 + 3*577 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf861 : K % 6561 ≠ 6247 := fun h => absurd
    (ladder_fire_mod6561 K 1873 2 (by decide) (by decide)
      (by rw [show (1873:Nat) = 1 + 3*624 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf862 : K % 6561 ≠ 6331 := fun h => absurd
    (ladder_fire_mod6561 K 1957 2 (by decide) (by decide)
      (by rw [show (1957:Nat) = 1 + 3*652 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf863 : K % 6561 ≠ 6412 := fun h => absurd
    (ladder_fire_mod6561 K 2038 2 (by decide) (by decide)
      (by rw [show (2038:Nat) = 1 + 3*679 from by decide,
        GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega)) hrow8
  have hf90 : K % 19683 ≠ 40 := fun h => absurd
    (dust_fire_row_nine K (Or.inl h)) hrow9
  have hf91 : K % 19683 ≠ 94 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inl h))) hrow9
  have hf92 : K % 19683 ≠ 109 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inl h)))) hrow9
  have hf93 : K % 19683 ≠ 193 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow9
  have hf94 : K % 19683 ≠ 244 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow9
  have hf95 : K % 19683 ≠ 283 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow9
  have hf96 : K % 19683 ≠ 325 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow9
  have hf97 : K % 19683 ≠ 733 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow9
  have hf98 : K % 19683 ≠ 928 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow9
  have hf99 : K % 19683 ≠ 1009 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow9
  have hf910 : K % 19683 ≠ 1144 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow9
  have hf911 : K % 19683 ≠ 1171 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow9
  have hf912 : K % 19683 ≠ 1252 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow9
  have hf913 : K % 19683 ≠ 1387 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow9
  have hf914 : K % 19683 ≠ 1540 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow9
  have hf915 : K % 19683 ≠ 1957 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow9
  have hf916 : K % 19683 ≠ 2434 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow9
  have hf917 : K % 19683 ≠ 2470 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow9
  have hf918 : K % 19683 ≠ 2512 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow9
  have hf919 : K % 19683 ≠ 2767 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow9
  have hf920 : K % 19683 ≠ 2920 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow9
  have hf921 : K % 19683 ≠ 3115 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow9
  have hf922 : K % 19683 ≠ 3196 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow9
  have hf923 : K % 19683 ≠ 3331 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow9
  have hf924 : K % 19683 ≠ 3727 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow9
  have hf925 : K % 19683 ≠ 4144 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow9
  have hf926 : K % 19683 ≠ 4162 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow9
  have hf927 : K % 19683 ≠ 4297 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow9
  have hf928 : K % 19683 ≠ 4387 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow9
  have hf929 : K % 19683 ≠ 4495 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow9
  have hf930 : K % 19683 ≠ 4621 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow9
  have hf931 : K % 19683 ≠ 4897 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))) hrow9
  have hf932 : K % 19683 ≠ 4954 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))) hrow9
  have hf933 : K % 19683 ≠ 5197 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))) hrow9
  have hf934 : K % 19683 ≠ 5296 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))) hrow9
  have hf935 : K % 19683 ≠ 5617 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))) hrow9
  have hf936 : K % 19683 ≠ 5842 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))) hrow9
  have hf937 : K % 19683 ≠ 5998 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))) hrow9
  have hf938 : K % 19683 ≠ 6157 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))) hrow9
  have hf939 : K % 19683 ≠ 6349 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf940 : K % 19683 ≠ 6484 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf941 : K % 19683 ≠ 6574 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf942 : K % 19683 ≠ 6682 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf943 : K % 19683 ≠ 6841 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf944 : K % 19683 ≠ 6925 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf945 : K % 19683 ≠ 6997 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf946 : K % 19683 ≠ 7084 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf947 : K % 19683 ≠ 7156 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf948 : K % 19683 ≠ 7291 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf949 : K % 19683 ≠ 7384 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf950 : K % 19683 ≠ 7483 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf951 : K % 19683 ≠ 7564 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf952 : K % 19683 ≠ 7786 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf953 : K % 19683 ≠ 7804 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf954 : K % 19683 ≠ 8029 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf955 : K % 19683 ≠ 8185 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf956 : K % 19683 ≠ 8344 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf957 : K % 19683 ≠ 9028 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf958 : K % 19683 ≠ 9112 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf959 : K % 19683 ≠ 9184 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf960 : K % 19683 ≠ 9343 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf961 : K % 19683 ≠ 9478 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf962 : K % 19683 ≠ 9724 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf963 : K % 19683 ≠ 9751 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf964 : K % 19683 ≠ 9973 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf965 : K % 19683 ≠ 10234 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf966 : K % 19683 ≠ 10246 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf967 : K % 19683 ≠ 11449 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf968 : K % 19683 ≠ 11674 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf969 : K % 19683 ≠ 11773 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf970 : K % 19683 ≠ 11785 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf971 : K % 19683 ≠ 11908 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf972 : K % 19683 ≠ 11911 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf973 : K % 19683 ≠ 12421 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf974 : K % 19683 ≠ 12433 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf975 : K % 19683 ≠ 12676 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf976 : K % 19683 ≠ 12835 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf977 : K % 19683 ≠ 12988 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf978 : K % 19683 ≠ 13051 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf979 : K % 19683 ≠ 13123 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf980 : K % 19683 ≠ 13126 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf981 : K % 19683 ≠ 13288 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf982 : K % 19683 ≠ 13618 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf983 : K % 19683 ≠ 13636 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf984 : K % 19683 ≠ 13861 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf985 : K % 19683 ≠ 13960 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf986 : K % 19683 ≠ 13972 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf987 : K % 19683 ≠ 14095 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf988 : K % 19683 ≠ 14215 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf989 : K % 19683 ≠ 14287 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf990 : K % 19683 ≠ 14350 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf991 : K % 19683 ≠ 14779 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf992 : K % 19683 ≠ 14854 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf993 : K % 19683 ≠ 14863 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf994 : K % 19683 ≠ 14995 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf995 : K % 19683 ≠ 15022 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf996 : K % 19683 ≠ 15160 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf997 : K % 19683 ≠ 15175 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf998 : K % 19683 ≠ 15238 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf999 : K % 19683 ≠ 15310 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9100 : K % 19683 ≠ 15313 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9101 : K % 19683 ≠ 15391 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9102 : K % 19683 ≠ 15475 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9103 : K % 19683 ≠ 15805 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9104 : K % 19683 ≠ 16066 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9105 : K % 19683 ≠ 16402 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9106 : K % 19683 ≠ 16474 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9107 : K % 19683 ≠ 16537 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9108 : K % 19683 ≠ 16555 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9109 : K % 19683 ≠ 16690 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9110 : K % 19683 ≠ 16780 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9111 : K % 19683 ≠ 16966 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9112 : K % 19683 ≠ 17041 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9113 : K % 19683 ≠ 17182 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9114 : K % 19683 ≠ 17347 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9115 : K % 19683 ≠ 17536 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9116 : K % 19683 ≠ 17578 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9117 : K % 19683 ≠ 17590 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9118 : K % 19683 ≠ 17605 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9119 : K % 19683 ≠ 17689 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9120 : K % 19683 ≠ 17740 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9121 : K % 19683 ≠ 18253 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9122 : K % 19683 ≠ 18667 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9123 : K % 19683 ≠ 18742 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9124 : K % 19683 ≠ 18748 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9125 : K % 19683 ≠ 18877 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9126 : K % 19683 ≠ 18883 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  have hf9127 : K % 19683 ≠ 18967 := fun h => absurd
    (dust_fire_row_nine K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow9
  rcases h729 with p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31
  all_goals omega

/-! ## §7 The receipts -/

#print axioms one_add_pow_six_term
#print axioms wt_quintic_mod59049
#print axioms wt_row_nine_read
#print axioms fire_of_mod19683
#print axioms dust_fire_row_nine
#print axioms no22_of_cascade_eight
#print axioms cantorian_dust_mod_19683

