import Mathlib
import MonolithGate.GSTWorldtraceArithmetic
import MonolithGate.GSTTheActConstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE NINTH CASCADE LEVEL (S085 r34, the final assembly round)

One storey deeper than the vendored engine's deepest green level:
the worldtrace ladder at level nine — the quintic blade mod 59049,
the row-nine read, the uniform kill `fire_of_mod19683` (through the
engine's own level-generic `feedback_fire_of_class`), the 128 dead
classes of `dust_fire_row_nine`, the kill chain `no22_of_cascade_eight`,
and the re-doubled Cantorian pin `cantorian_dust_mod_19683` (the
256-survivor map: every class-one Cantorian power lives in one of 256
classes mod 19683).

Computational certificate (two-method, this round): the 128 fires and
256 survivors recomputed by modular exponentiation AND by direct
big-integer ternary expansion — zero mismatches; the boss's own green
level-eight lists (64 fires, 128 survivors) reproduced exactly by the
same two methods; the quintic blade validated on every m < 3000;
every noise receipt `(digit3 (4^r) 9 + t) % 3 = 2` validated on the
quintic polynomial path (the exact Lean proof path).
-/

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTheActConstruction (feedback_fire_of_class)
open GSTWorldtraceArithmetic (wt_choose_one wt_rebase
  cantorian_dust_mod_6561)

/-! ## §1 The six-term binomial ladder -/

/-- **The six-term binomial ladder.**  One order deeper than the engine's
five-term ladder: the quintic window's engine. -/
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
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
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

/-- **THE QUINTIC BLADE.**  Three windows deeper than the quartic:
`4^(1+3m)` is the quintic polynomial mod 59049 — the order-five
worldtrace.  (63^6 = 3^12 * 7^6 dies mod 3^10 = 59049.) -/
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
  rw [wt_rebase, h64, hR, hexp]
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

/-- **ROW NINE IS THE QUINTIC.**  For EVERY m: the ninth row of the
dust power `4^(1+3m)` is the ninth row of the quintic blade. -/
theorem wt_row_nine_read (m : Nat) :
    digit3 (4^(1+3*m)) 9
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) 9 := by
  have h59049 : (3:Nat)^(9+1) = 59049 := by decide
  have h := wt_quintic_mod59049 m
  rw [← h59049] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-! ## §4 The uniform kill at level nine -/

/-- **THE UNIFORM KILL, LEVEL-NINE FORM.**  `K ≡ r + 6561*t mod 19683`
fires at row nine when the noise receipt holds.  All arithmetic
literal — the engine's own level-generic law at j = 8. -/
theorem fire_of_mod19683 (K r t : Nat)
    (hr : r < 6561) (ht : t < 3)
    (hnoise : (digit3 (4^r) 9 + t) % 3 = 2)
    (hclass : K % 19683 = r + 6561 * t) :
    digit3 (4^K) 9 = 2 := by
  have h19683 : (3:Nat)^(8+1) = 19683 := by decide
  have h6561 : (3:Nat)^8 = 6561 := by decide
  have hK : K % 3^(8+1) = r + 3^8 * t := by
    rw [h19683, h6561]
    exact hclass
  have hr' : r < 3^8 := by
    rw [h6561]
    exact hr
  exact feedback_fire_of_class 8 r t K hr' ht hnoise hK

/-! ## §5 The ninth cascade level — the 128 dead classes -/

/-- **CASCADE LEVEL NINE (row nine).**  Every exponent in one of the
128 dead classes mod 19683 fires its digit two at row nine — the
engine's deepest uniform ladder, one storey deeper than the vendored
level eight.  Each receipt: the parent class `r = 1 + 3*m` (a level-8
survivor), the killing trit `t`, the noise read on the quintic
polynomial — never on the power itself. -/
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

/-- **CASCADE LEVEL NINE, KILL CHAIN.**  The 128 new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_eight (K : Nat)
    (h : K % 19683 = 40 ∨ K % 19683 = 94 ∨ K % 19683 = 109 ∨ K % 19683 = 193 ∨ K % 19683 = 244 ∨ K % 19683 = 283 ∨ K % 19683 = 325 ∨ K % 19683 = 733 ∨ K % 19683 = 928 ∨ K % 19683 = 1009 ∨ K % 19683 = 1144 ∨ K % 19683 = 1171 ∨ K % 19683 = 1252 ∨ K % 19683 = 1387 ∨ K % 19683 = 1540 ∨ K % 19683 = 1957 ∨ K % 19683 = 2434 ∨ K % 19683 = 2470 ∨ K % 19683 = 2512 ∨ K % 19683 = 2767 ∨ K % 19683 = 2920 ∨ K % 19683 = 3115 ∨ K % 19683 = 3196 ∨ K % 19683 = 3331 ∨ K % 19683 = 3727 ∨ K % 19683 = 4144 ∨ K % 19683 = 4162 ∨ K % 19683 = 4297 ∨ K % 19683 = 4387 ∨ K % 19683 = 4495 ∨ K % 19683 = 4621 ∨ K % 19683 = 4897 ∨ K % 19683 = 4954 ∨ K % 19683 = 5197 ∨ K % 19683 = 5296 ∨ K % 19683 = 5617 ∨ K % 19683 = 5842 ∨ K % 19683 = 5998 ∨ K % 19683 = 6157 ∨ K % 19683 = 6349 ∨ K % 19683 = 6484 ∨ K % 19683 = 6574 ∨ K % 19683 = 6682 ∨ K % 19683 = 6841 ∨ K % 19683 = 6925 ∨ K % 19683 = 6997 ∨ K % 19683 = 7084 ∨ K % 19683 = 7156 ∨ K % 19683 = 7291 ∨ K % 19683 = 7384 ∨ K % 19683 = 7483 ∨ K % 19683 = 7564 ∨ K % 19683 = 7786 ∨ K % 19683 = 7804 ∨ K % 19683 = 8029 ∨ K % 19683 = 8185 ∨ K % 19683 = 8344 ∨ K % 19683 = 9028 ∨ K % 19683 = 9112 ∨ K % 19683 = 9184 ∨ K % 19683 = 9343 ∨ K % 19683 = 9478 ∨ K % 19683 = 9724 ∨ K % 19683 = 9751 ∨ K % 19683 = 9973 ∨ K % 19683 = 10234 ∨ K % 19683 = 10246 ∨ K % 19683 = 11449 ∨ K % 19683 = 11674 ∨ K % 19683 = 11773 ∨ K % 19683 = 11785 ∨ K % 19683 = 11908 ∨ K % 19683 = 11911 ∨ K % 19683 = 12421 ∨ K % 19683 = 12433 ∨ K % 19683 = 12676 ∨ K % 19683 = 12835 ∨ K % 19683 = 12988 ∨ K % 19683 = 13051 ∨ K % 19683 = 13123 ∨ K % 19683 = 13126 ∨ K % 19683 = 13288 ∨ K % 19683 = 13618 ∨ K % 19683 = 13636 ∨ K % 19683 = 13861 ∨ K % 19683 = 13960 ∨ K % 19683 = 13972 ∨ K % 19683 = 14095 ∨ K % 19683 = 14215 ∨ K % 19683 = 14287 ∨ K % 19683 = 14350 ∨ K % 19683 = 14779 ∨ K % 19683 = 14854 ∨ K % 19683 = 14863 ∨ K % 19683 = 14995 ∨ K % 19683 = 15022 ∨ K % 19683 = 15160 ∨ K % 19683 = 15175 ∨ K % 19683 = 15238 ∨ K % 19683 = 15310 ∨ K % 19683 = 15313 ∨ K % 19683 = 15391 ∨ K % 19683 = 15475 ∨ K % 19683 = 15805 ∨ K % 19683 = 16066 ∨ K % 19683 = 16402 ∨ K % 19683 = 16474 ∨ K % 19683 = 16537 ∨ K % 19683 = 16555 ∨ K % 19683 = 16690 ∨ K % 19683 = 16780 ∨ K % 19683 = 16966 ∨ K % 19683 = 17041 ∨ K % 19683 = 17182 ∨ K % 19683 = 17347 ∨ K % 19683 = 17536 ∨ K % 19683 = 17578 ∨ K % 19683 = 17590 ∨ K % 19683 = 17605 ∨ K % 19683 = 17689 ∨ K % 19683 = 17740 ∨ K % 19683 = 18253 ∨ K % 19683 = 18667 ∨ K % 19683 = 18742 ∨ K % 19683 = 18748 ∨ K % 19683 = 18877 ∨ K % 19683 = 18883 ∨ K % 19683 = 18967) :
    noTernaryTwo (4^K) = false := by
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h0)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h1)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h2)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h3)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h4)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h5)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h6)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h7)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h8)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h9)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h10)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h11)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h12)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h13)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h14)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h15)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h16)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h17)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h18)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h19)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h20)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h21)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h22)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h23)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h24)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h25)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h26)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h27)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h28)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h29)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h30)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h31)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h32)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h33)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h34)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h35)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h36)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h37)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h38)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h39)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h40)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h41)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h42)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h43)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h44)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h45)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h46)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h47)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h48)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h49)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h50)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h51)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h52)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h53)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h54)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h55)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h56)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h57)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h58)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h59)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h60)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h61)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h62)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h63)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h64)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h65)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h66)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h67)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h68)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h69)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h70)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h71)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h72)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h73)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h74)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h75)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h76)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h77)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h78)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h79)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h80)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h81)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h82)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h83)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h84)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h85)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h86)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h87)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h88)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h89)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h90)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h91)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h92)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h93)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h94)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h95)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h96)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h97)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h98)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h99)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h100)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h101)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h102)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h103)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h104)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h105)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h106)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h107)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h108)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h109)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h110)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h111)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h112)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h113)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h114)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h115)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h116)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h117)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h118)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h119)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h120)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h121)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h122)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h123)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h124)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h125)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h126)
  · exact no22_of_digit_two K 9 (dust_fire_row_nine K h127)

/-! ## §6 The re-doubled Cantorian pin — the 256-survivor map -/

/-- **THE CANTORIAN PIN, LEVEL NINE.**  Every class-one Cantorian
power lives in one of 256 classes modulo 19683 — the survivor map
re-doubled one storey deeper (128 → 256).  The proof: the level-8 pin,
the clean ninth row, and the 128 exclusions — one per dead class. -/
theorem cantorian_dust_mod_19683 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 19683 = 1 ∨ K % 19683 = 4 ∨ K % 19683 = 13 ∨ K % 19683 = 121 ∨ K % 19683 = 166 ∨ K % 19683 = 280 ∨ K % 19683 = 364 ∨ K % 19683 = 436 ∨ K % 19683 = 496 ∨ K % 19683 = 514 ∨ K % 19683 = 523 ∨ K % 19683 = 595 ∨ K % 19683 = 730 ∨ K % 19683 = 739 ∨ K % 19683 = 823 ∨ K % 19683 = 838 ∨ K % 19683 = 850 ∨ K % 19683 = 922 ∨ K % 19683 = 973 ∨ K % 19683 = 1003 ∨ K % 19683 = 1093 ∨ K % 19683 = 1165 ∨ K % 19683 = 1225 ∨ K % 19683 = 1228 ∨ K % 19683 = 1243 ∨ K % 19683 = 1468 ∨ K % 19683 = 1624 ∨ K % 19683 = 1657 ∨ K % 19683 = 1732 ∨ K % 19683 = 1741 ∨ K % 19683 = 1783 ∨ K % 19683 = 1873 ∨ K % 19683 = 1900 ∨ K % 19683 = 2038 ∨ K % 19683 = 2053 ∨ K % 19683 = 2116 ∨ K % 19683 = 2188 ∨ K % 19683 = 2191 ∨ K % 19683 = 2269 ∨ K % 19683 = 2353 ∨ K % 19683 = 2467 ∨ K % 19683 = 2551 ∨ K % 19683 = 2623 ∨ K % 19683 = 2683 ∨ K % 19683 = 2782 ∨ K % 19683 = 2917 ∨ K % 19683 = 2944 ∨ K % 19683 = 3163 ∨ K % 19683 = 3190 ∨ K % 19683 = 3280 ∨ K % 19683 = 3352 ∨ K % 19683 = 3412 ∨ K % 19683 = 3415 ∨ K % 19683 = 3433 ∨ K % 19683 = 3568 ∨ K % 19683 = 3658 ∨ K % 19683 = 3673 ∨ K % 19683 = 3685 ∨ K % 19683 = 3844 ∨ K % 19683 = 3919 ∨ K % 19683 = 4060 ∨ K % 19683 = 4225 ∨ K % 19683 = 4414 ∨ K % 19683 = 4456 ∨ K % 19683 = 4468 ∨ K % 19683 = 4483 ∨ K % 19683 = 4567 ∨ K % 19683 = 4618 ∨ K % 19683 = 4888 ∨ K % 19683 = 5113 ∨ K % 19683 = 5131 ∨ K % 19683 = 5212 ∨ K % 19683 = 5224 ∨ K % 19683 = 5347 ∨ K % 19683 = 5350 ∨ K % 19683 = 5545 ∨ K % 19683 = 5620 ∨ K % 19683 = 5626 ∨ K % 19683 = 5755 ∨ K % 19683 = 5761 ∨ K % 19683 = 5845 ∨ K % 19683 = 5860 ∨ K % 19683 = 5872 ∨ K % 19683 = 6115 ∨ K % 19683 = 6274 ∨ K % 19683 = 6427 ∨ K % 19683 = 6490 ∨ K % 19683 = 6562 ∨ K % 19683 = 6565 ∨ K % 19683 = 6601 ∨ K % 19683 = 6655 ∨ K % 19683 = 6670 ∨ K % 19683 = 6727 ∨ K % 19683 = 6754 ∨ K % 19683 = 6805 ∨ K % 19683 = 6844 ∨ K % 19683 = 6886 ∨ K % 19683 = 7057 ∨ K % 19683 = 7075 ∨ K % 19683 = 7294 ∨ K % 19683 = 7300 ∨ K % 19683 = 7399 ∨ K % 19683 = 7411 ∨ K % 19683 = 7489 ∨ K % 19683 = 7534 ∨ K % 19683 = 7570 ∨ K % 19683 = 7654 ∨ K % 19683 = 7705 ∨ K % 19683 = 7726 ∨ K % 19683 = 7732 ∨ K % 19683 = 7789 ∨ K % 19683 = 7813 ∨ K % 19683 = 7948 ∨ K % 19683 = 8101 ∨ K % 19683 = 8218 ∨ K % 19683 = 8293 ∨ K % 19683 = 8302 ∨ K % 19683 = 8434 ∨ K % 19683 = 8461 ∨ K % 19683 = 8518 ∨ K % 19683 = 8599 ∨ K % 19683 = 8614 ∨ K % 19683 = 8677 ∨ K % 19683 = 8749 ∨ K % 19683 = 8752 ∨ K % 19683 = 8830 ∨ K % 19683 = 8914 ∨ K % 19683 = 8995 ∨ K % 19683 = 9031 ∨ K % 19683 = 9073 ∨ K % 19683 = 9244 ∨ K % 19683 = 9328 ∨ K % 19683 = 9481 ∨ K % 19683 = 9505 ∨ K % 19683 = 9676 ∨ K % 19683 = 9757 ∨ K % 19683 = 9841 ∨ K % 19683 = 9892 ∨ K % 19683 = 9913 ∨ K % 19683 = 9976 ∨ K % 19683 = 9994 ∨ K % 19683 = 10129 ∨ K % 19683 = 10219 ∨ K % 19683 = 10288 ∨ K % 19683 = 10405 ∨ K % 19683 = 10480 ∨ K % 19683 = 10621 ∨ K % 19683 = 10705 ∨ K % 19683 = 10723 ∨ K % 19683 = 10786 ∨ K % 19683 = 10858 ∨ K % 19683 = 10948 ∨ K % 19683 = 10975 ∨ K % 19683 = 11017 ∨ K % 19683 = 11029 ∨ K % 19683 = 11044 ∨ K % 19683 = 11056 ∨ K % 19683 = 11128 ∨ K % 19683 = 11179 ∨ K % 19683 = 11182 ∨ K % 19683 = 11458 ∨ K % 19683 = 11515 ∨ K % 19683 = 11692 ∨ K % 19683 = 11758 ∨ K % 19683 = 11857 ∨ K % 19683 = 12106 ∨ K % 19683 = 12178 ∨ K % 19683 = 12181 ∨ K % 19683 = 12187 ∨ K % 19683 = 12316 ∨ K % 19683 = 12322 ∨ K % 19683 = 12403 ∨ K % 19683 = 12406 ∨ K % 19683 = 12559 ∨ K % 19683 = 12718 ∨ K % 19683 = 12910 ∨ K % 19683 = 13045 ∨ K % 19683 = 13135 ∨ K % 19683 = 13162 ∨ K % 19683 = 13216 ∨ K % 19683 = 13231 ∨ K % 19683 = 13243 ∨ K % 19683 = 13315 ∨ K % 19683 = 13366 ∨ K % 19683 = 13402 ∨ K % 19683 = 13405 ∨ K % 19683 = 13447 ∨ K % 19683 = 13486 ∨ K % 19683 = 13558 ∨ K % 19683 = 13645 ∨ K % 19683 = 13717 ∨ K % 19683 = 13852 ∨ K % 19683 = 13855 ∨ K % 19683 = 13945 ∨ K % 19683 = 14044 ∨ K % 19683 = 14050 ∨ K % 19683 = 14125 ∨ K % 19683 = 14131 ∨ K % 19683 = 14266 ∨ K % 19683 = 14293 ∨ K % 19683 = 14347 ∨ K % 19683 = 14365 ∨ K % 19683 = 14374 ∨ K % 19683 = 14509 ∨ K % 19683 = 14590 ∨ K % 19683 = 14662 ∨ K % 19683 = 14746 ∨ K % 19683 = 14905 ∨ K % 19683 = 15079 ∨ K % 19683 = 15556 ∨ K % 19683 = 15589 ∨ K % 19683 = 15592 ∨ K % 19683 = 15634 ∨ K % 19683 = 15673 ∨ K % 19683 = 15745 ∨ K % 19683 = 15889 ∨ K % 19683 = 15904 ∨ K % 19683 = 16039 ∨ K % 19683 = 16042 ∨ K % 19683 = 16237 ∨ K % 19683 = 16285 ∨ K % 19683 = 16312 ∨ K % 19683 = 16318 ∨ K % 19683 = 16453 ∨ K % 19683 = 16534 ∨ K % 19683 = 16795 ∨ K % 19683 = 16807 ∨ K % 19683 = 16849 ∨ K % 19683 = 17266 ∨ K % 19683 = 17284 ∨ K % 19683 = 17419 ∨ K % 19683 = 17509 ∨ K % 19683 = 17617 ∨ K % 19683 = 17743 ∨ K % 19683 = 18010 ∨ K % 19683 = 18019 ∨ K % 19683 = 18076 ∨ K % 19683 = 18235 ∨ K % 19683 = 18319 ∨ K % 19683 = 18334 ∨ K % 19683 = 18346 ∨ K % 19683 = 18418 ∨ K % 19683 = 18469 ∨ K % 19683 = 18472 ∨ K % 19683 = 18739 ∨ K % 19683 = 18964 ∨ K % 19683 = 18982 ∨ K % 19683 = 18994 ∨ K % 19683 = 19120 ∨ K % 19683 = 19237 ∨ K % 19683 = 19279 ∨ K % 19683 = 19396 ∨ K % 19683 = 19471 ∨ K % 19683 = 19549 ∨ K % 19683 = 19606 ∨ K % 19683 = 19612 := by
  have h6561 := cantorian_dust_mod_6561 K hd hc
  have hrow := hc 9 (by omega)
  have hd0 : K % 19683 ≠ 40 :=
    fun h => absurd (dust_fire_row_nine K (Or.inl h)) hrow
  have hd1 : K % 19683 ≠ 94 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr h)) hrow
  have hd2 : K % 19683 ≠ 109 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr h)) hrow
  have hd3 : K % 19683 ≠ 193 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr h)) hrow
  have hd4 : K % 19683 ≠ 244 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd5 : K % 19683 ≠ 283 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd6 : K % 19683 ≠ 325 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd7 : K % 19683 ≠ 733 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd8 : K % 19683 ≠ 928 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd9 : K % 19683 ≠ 1009 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd10 : K % 19683 ≠ 1144 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd11 : K % 19683 ≠ 1171 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd12 : K % 19683 ≠ 1252 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd13 : K % 19683 ≠ 1387 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd14 : K % 19683 ≠ 1540 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd15 : K % 19683 ≠ 1957 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd16 : K % 19683 ≠ 2434 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd17 : K % 19683 ≠ 2470 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd18 : K % 19683 ≠ 2512 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd19 : K % 19683 ≠ 2767 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd20 : K % 19683 ≠ 2920 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd21 : K % 19683 ≠ 3115 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd22 : K % 19683 ≠ 3196 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd23 : K % 19683 ≠ 3331 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd24 : K % 19683 ≠ 3727 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd25 : K % 19683 ≠ 4144 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd26 : K % 19683 ≠ 4162 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd27 : K % 19683 ≠ 4297 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd28 : K % 19683 ≠ 4387 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd29 : K % 19683 ≠ 4495 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd30 : K % 19683 ≠ 4621 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd31 : K % 19683 ≠ 4897 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd32 : K % 19683 ≠ 4954 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd33 : K % 19683 ≠ 5197 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd34 : K % 19683 ≠ 5296 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd35 : K % 19683 ≠ 5617 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd36 : K % 19683 ≠ 5842 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd37 : K % 19683 ≠ 5998 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd38 : K % 19683 ≠ 6157 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd39 : K % 19683 ≠ 6349 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd40 : K % 19683 ≠ 6484 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd41 : K % 19683 ≠ 6574 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd42 : K % 19683 ≠ 6682 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd43 : K % 19683 ≠ 6841 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd44 : K % 19683 ≠ 6925 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd45 : K % 19683 ≠ 6997 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd46 : K % 19683 ≠ 7084 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd47 : K % 19683 ≠ 7156 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd48 : K % 19683 ≠ 7291 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd49 : K % 19683 ≠ 7384 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd50 : K % 19683 ≠ 7483 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd51 : K % 19683 ≠ 7564 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd52 : K % 19683 ≠ 7786 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd53 : K % 19683 ≠ 7804 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd54 : K % 19683 ≠ 8029 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd55 : K % 19683 ≠ 8185 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd56 : K % 19683 ≠ 8344 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd57 : K % 19683 ≠ 9028 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd58 : K % 19683 ≠ 9112 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd59 : K % 19683 ≠ 9184 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd60 : K % 19683 ≠ 9343 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd61 : K % 19683 ≠ 9478 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd62 : K % 19683 ≠ 9724 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd63 : K % 19683 ≠ 9751 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd64 : K % 19683 ≠ 9973 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd65 : K % 19683 ≠ 10234 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd66 : K % 19683 ≠ 10246 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd67 : K % 19683 ≠ 11449 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd68 : K % 19683 ≠ 11674 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd69 : K % 19683 ≠ 11773 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd70 : K % 19683 ≠ 11785 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd71 : K % 19683 ≠ 11908 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd72 : K % 19683 ≠ 11911 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd73 : K % 19683 ≠ 12421 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd74 : K % 19683 ≠ 12433 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd75 : K % 19683 ≠ 12676 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd76 : K % 19683 ≠ 12835 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd77 : K % 19683 ≠ 12988 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd78 : K % 19683 ≠ 13051 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd79 : K % 19683 ≠ 13123 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd80 : K % 19683 ≠ 13126 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd81 : K % 19683 ≠ 13288 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd82 : K % 19683 ≠ 13618 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd83 : K % 19683 ≠ 13636 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd84 : K % 19683 ≠ 13861 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd85 : K % 19683 ≠ 13960 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd86 : K % 19683 ≠ 13972 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd87 : K % 19683 ≠ 14095 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd88 : K % 19683 ≠ 14215 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd89 : K % 19683 ≠ 14287 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd90 : K % 19683 ≠ 14350 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd91 : K % 19683 ≠ 14779 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd92 : K % 19683 ≠ 14854 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd93 : K % 19683 ≠ 14863 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd94 : K % 19683 ≠ 14995 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd95 : K % 19683 ≠ 15022 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd96 : K % 19683 ≠ 15160 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd97 : K % 19683 ≠ 15175 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd98 : K % 19683 ≠ 15238 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd99 : K % 19683 ≠ 15310 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd100 : K % 19683 ≠ 15313 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd101 : K % 19683 ≠ 15391 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd102 : K % 19683 ≠ 15475 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd103 : K % 19683 ≠ 15805 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd104 : K % 19683 ≠ 16066 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd105 : K % 19683 ≠ 16402 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd106 : K % 19683 ≠ 16474 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd107 : K % 19683 ≠ 16537 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd108 : K % 19683 ≠ 16555 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd109 : K % 19683 ≠ 16690 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd110 : K % 19683 ≠ 16780 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd111 : K % 19683 ≠ 16966 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd112 : K % 19683 ≠ 17041 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd113 : K % 19683 ≠ 17182 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd114 : K % 19683 ≠ 17347 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd115 : K % 19683 ≠ 17536 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd116 : K % 19683 ≠ 17578 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd117 : K % 19683 ≠ 17590 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd118 : K % 19683 ≠ 17605 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd119 : K % 19683 ≠ 17689 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd120 : K % 19683 ≠ 17740 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd121 : K % 19683 ≠ 18253 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd122 : K % 19683 ≠ 18667 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd123 : K % 19683 ≠ 18742 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd124 : K % 19683 ≠ 18748 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd125 : K % 19683 ≠ 18877 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd126 : K % 19683 ≠ 18883 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  have hd127 : K % 19683 ≠ 18967 :=
    fun h => absurd (dust_fire_row_nine K (Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr Or.inr h)) hrow
  rcases h6561 with p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38 | p39 | p40 | p41 | p42 | p43 | p44 | p45 | p46 | p47 | p48 | p49 | p50 | p51 | p52 | p53 | p54 | p55 | p56 | p57 | p58 | p59 | p60 | p61 | p62 | p63 | p64 | p65 | p66 | p67 | p68 | p69 | p70 | p71 | p72 | p73 | p74 | p75 | p76 | p77 | p78 | p79 | p80 | p81 | p82 | p83 | p84 | p85 | p86 | p87 | p88 | p89 | p90 | p91 | p92 | p93 | p94 | p95 | p96 | p97 | p98 | p99 | p100 | p101 | p102 | p103 | p104 | p105 | p106 | p107 | p108 | p109 | p110 | p111 | p112 | p113 | p114 | p115 | p116 | p117 | p118 | p119 | p120 | p121 | p122 | p123 | p124 | p125 | p126 | p127
  all_goals omega

/-! ## §7 The receipts -/

#print axioms one_add_pow_six_term
#print axioms wt_quintic_mod59049
#print axioms wt_row_nine_read
#print axioms fire_of_mod19683
#print axioms dust_fire_row_nine
#print axioms no22_of_cascade_eight
#print axioms cantorian_dust_mod_19683
