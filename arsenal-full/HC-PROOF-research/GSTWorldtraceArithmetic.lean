import Mathlib
import GSTTowerFire
import GSTTheActConstruction
import GSTFourPowerDirectResidue

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTheActConstruction (feedback_fire_of_class cantorian_dust_mod_729)
open GSTFourPowerDirectResidue (digit3_eq_of_mod_next)

namespace GSTWorldtraceArithmetic

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-!
# THE WORLDTRACE ARITHMETIC — the boss's transformation, landed

The stuck gap (GAP-A2, the c_infinity blade survivor tree) TRANSFORMED
into worldtrace arithmetic and attacked there.  The transformation:

    4^(1+3m) = 4 * 64^m = 4 * (1+63)^m = 4 * SUM_i C(m,i) * 63^i

Every dust power is a BINOMIAL SUM in the exponent's half-scale — and
every deep row becomes an EXPLICIT POLYNOMIAL in m with 3-adic
coefficients 4*7^i sitting at row-blocks 2i:

  * row five  = the QUADRATIC blade `4 + 252m + 15876*C(m,2)` mod 729
  * row seven = the CUBIC blade `4 + 252m + 15876*C(m,2) + 1000188*C(m,3)`
    mod 6561

Machine receipts BEFORE landing (this session, exact big-int / modular,
`/tmp/wt_receipts.py`):

  * R1 32/32 — the level-6 dead classes mod 2187 all fire at row seven
    (modular 4^rho mod 3^8 arithmetic); survivors double 32 -> 64 exactly.
  * R2 the quadratic blade's kill set CONTAINS the entire green row-five
    table {85, 91, 112, 118, 163, 175, 190, 202} — the polynomial
    reproduces the machine's green cascade.
  * R4 the cubic identity holds 0 failures on 0 <= m < 6561 step 7, and
    row-seven polynomial reads match direct computation 2187/2187.
  * R5 (level seven, this session, `/tmp/wt_level7.py`): recursion
    re-verified against the green tables (s5/d6/s6 exact); quartic AND
    quintic blades 0 failures on all 0 <= m < 2186; 64 dead classes
    mod 6561 fire at row eight; survivors double 64 -> 128 exactly
    (192 = 64*3 children partition checked).

Sections:

  * SS1 THE BINOMIAL LADDER — `one_add_pow_three_term`,
    `one_add_pow_four_term` (the two-term `GSTTowerFire` engine extended).
  * SS2 THE TRANSFORMATION — `wt_rebase`, `wt_quad_mod729` (the
    quadratic blade), `wt_cubic_mod6561` (the cubic blade).
  * SS3 THE READS — `wt_row_five_read`, `wt_row_seven_read`: the dust
    power's deep rows ARE the polynomial blades, plus the polynomial
    kill demo (`wt_quad_fire_demo`: the quadratic kills K = 85 at row
    five without ever computing 4^85).
  * SS4 THE SIXTH CASCADE LEVEL — `fire_of_mod2187`, `dust_fire_row_seven`
    (32 dead classes), `no22_of_cascade_six`, `cantorian_dust_mod_2187`
    (the 64-survivor map).
  * SS5 THE SEVENTH CASCADE LEVEL — `fire_of_mod6561`, `dust_fire_row_eight`
    (64 dead classes), `no22_of_cascade_seven`, `cantarian_dust_mod_6561`
    (the 128-survivor map), plus the quartic blade `wt_quartic_mod19683`,
    the row-eight read, and the quartic kill demo (K = 82 killed at row
    eight without computing 4^82).
  * SS6 THE PAIR-READ FIRE — GAP-E1's first family: the uniform
    pair_read_formula (row-(j+4) of 4^(T+3^(j+1)*u) = row-two of
    4^T*u*c (j+1), via prefaced_digit + the binomial ladder) and
    pair_read_fire (every 4 + 3^(j+1)*u with j >= 4, u in {{1,4,7}}
    fires at row j+4 through c_mod81: trit two of 19*u).
-/

/-! ## §1 The binomial ladder -/

/-- **Choose-one, by induction** (self-contained: only
`Nat.choose_succ_succ` and `Nat.choose_zero_right`). -/
theorem wt_choose_one (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h : Nat.choose (k+1) 1 = Nat.choose k 0 + Nat.choose k 1 :=
      Nat.choose_succ_succ k 0
    rw [h, Nat.choose_zero_right, ih]
    omega

/-- **The three-term binomial ladder.** `(1+x)^j` with the first three
orders explicit — the term structure the worldtrace window reads. -/
theorem one_add_pow_three_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x + x*x*x*R := by
  induction j with
  | zero =>
    have h0 : Nat.choose 0 2 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h0]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    rw [Nat.pow_succ, hR, hc]
    refine ⟨Nat.choose j 2 + R + x*R, ?_⟩
    ring

/-- **The four-term binomial ladder.**  One order deeper: the cubic
window's engine. -/
theorem one_add_pow_four_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    rw [Nat.pow_succ, hR, hc2, hc3]
    refine ⟨Nat.choose j 3 + R + x*R, ?_⟩
    ring

/-- **The five-term binomial ladder.**  Two orders deeper: the quartic
window's engine. -/
theorem one_add_pow_five_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x
      + x*x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    have h04 : Nat.choose 0 4 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03, h04]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    have hc4 : Nat.choose (j+1) 4 = Nat.choose j 3 + Nat.choose j 4 :=
      Nat.choose_succ_succ j 3
    rw [Nat.pow_succ, hR, hc2, hc3, hc4]
    refine ⟨Nat.choose j 4 + R + x*R, ?_⟩
    ring

/-! ## §2 The transformation — the dust as a binomial sum -/

/-- **THE REBASE.**  Every dust power is a power of sixty-four:
`4^(1+3m) = 4 * 64^m` — and 64 = 1 + 63 opens the binomial world. -/
theorem wt_rebase (m : Nat) : 4^(1+3*m) = 4 * 64^m := by
  have h43 : (4:Nat)^3 = 64 := by decide
  rw [Nat.pow_add, Nat.pow_mul, h43, Nat.pow_one]

/-- **THE QUADRATIC BLADE.**  Row-window congruence of the dust power:
`4^(1+3m)` is the quadratic `4 + 252m + 15876*C(m,2)` mod 729 — the
order-two worldtrace.  (63^3 = 250047 = 729*343 dies mod 729.) -/
theorem wt_quad_mod729 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729] := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*R) % 729
     = (4 + 252*m + 15876*Nat.choose m 2) % 729
  have hd : 729 ∣ 1000188*R := by
    refine ⟨1372*R, ?_⟩
    ring
  have hz : 1000188*R % 729 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- **THE CUBIC BLADE.**  One window deeper: `4^(1+3m)` is the cubic
`4 + 252m + 15876*C(m,2) + 1000188*C(m,3)` mod 6561 — the order-three
worldtrace.  (63^4 = 3^8 * 7^4 dies mod 3^8 = 6561.) -/
theorem wt_cubic_mod6561 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561] := by
  obtain ⟨R, hR⟩ := one_add_pow_four_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + 63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R) % 6561
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) % 6561
  have hd : 6561 ∣ 63011844*R := by
    refine ⟨9604*R, ?_⟩
    ring
  have hz : 63011844*R % 6561 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- **THE QUARTIC BLADE.**  Two windows deeper: `4^(1+3m)` is the quartic
`4 + 252m + 15876*C(m,2) + 1000188*C(m,3) + 63011844*C(m,4)` mod 19683 —
the order-four worldtrace.  (63^5 = 3^10 * 7^5 dies mod 3^9 = 19683.) -/
theorem wt_quartic_mod19683 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683] := by
  obtain ⟨R, hR⟩ := one_add_pow_five_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + Nat.choose m 4 * 63 * 63 * 63 * 63
        + 63*63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*R) % 19683
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4) % 19683
  have hd : 19683 ∣ 3969746172*R := by
    refine ⟨201684*R, ?_⟩
    ring
  have hz : 3969746172*R % 19683 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-! ## §3 The reads — the deep rows ARE the polynomials -/

/-- **ROW FIVE IS THE QUADRATIC.**  For EVERY m: the fifth row of the
dust power `4^(1+3m)` is the fifth row of the quadratic blade — the
worldtrace read, exact. -/
theorem wt_row_five_read (m : Nat) :
    digit3 (4^(1+3*m)) 5 = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5 := by
  have h729 : (3:Nat)^(5+1) = 729 := by decide
  have h := wt_quad_mod729 m
  rw [← h729] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **ROW SEVEN IS THE CUBIC.**  For EVERY m: the seventh row of the
dust power is the seventh row of the cubic blade. -/
theorem wt_row_seven_read (m : Nat) :
    digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7 := by
  have h6561 : (3:Nat)^(7+1) = 6561 := by decide
  have h := wt_cubic_mod6561 m
  rw [← h6561] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **ROW EIGHT IS THE QUARTIC.**  For EVERY m: the eighth row of the
dust power is the eighth row of the quartic blade — the worldtrace
read, exact. -/
theorem wt_row_eight_read (m : Nat) :
    digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8 := by
  have h19683 : (3:Nat)^(8+1) = 19683 := by decide
  have h := wt_quartic_mod19683 m
  rw [← h19683] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **THE QUARTIC KILL DEMO.**  The quartic blade kills K = 82
(m = 27) at row eight WITHOUT EVER COMPUTING `4^82`: the worldtrace
quartic reads digit two at row eight.  The transformed problem,
solved in transformed coordinates, one storey deeper. -/
theorem wt_quartic_fire_demo : digit3 (4^(1+3*27)) 8 = 2 := by
  rw [wt_row_eight_read]
  decide

/-- **THE POLYNOMIAL KILL DEMO.**  The quadratic blade kills K = 85
(m = 28) at row five WITHOUT EVER COMPUTING `4^85`: the worldtrace
quadratic `4 + 252*28 + 15876*C(28,2) ≡ 499 mod 729` reads digit two
at row five.  The transformed problem, solved in transformed
coordinates. -/
theorem wt_quad_fire_demo : digit3 (4^(1+3*28)) 5 = 2 := by
  rw [wt_row_five_read]
  decide

/-! ## §4 The sixth cascade level — the compression continues -/

/-- **THE UNIFORM KILL, LEVEL-SIX FORM.**  `K ≡ r + 729*t mod 2187`
fires at row seven when the noise receipt holds.  All arithmetic
literal. -/
theorem fire_of_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2 := by
  have h2187 : (3:Nat)^(6+1) = 2187 := by decide
  have h729 : (3:Nat)^6 = 729 := by decide
  have hK : K % 3^(6+1) = r + 3^6 * t := by
    rw [h2187, h729]
    exact hclass
  have hr' : r < 3^6 := by
    rw [h729]
    exact hr
  exact feedback_fire_of_class 6 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL SIX (row seven).**  Every exponent in one of the
thirty-two dead classes mod 2187 fires its digit two at row seven.
Generated from the worldtrace noise receipts (`noise_6(r) = digit3 (4^r) 7`,
dead child `t = (2 - noise) % 3`, dead class `r + 729*t`) — the sixth
storey of the feedback tree, each node keeping exactly two alive
children (`unique_dead_child`). -/
theorem dust_fire_row_seven (K : Nat)
    (hK : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    digit3 (4^K) 7 = 2 := by
  rcases hK with h10 | h28 | h199 | h274 | h415 | h442 | h499 | h517 | h652 | h658 | h742 | h769 | h811 | h895 | h1012 | h1054 | h1309 | h1324 | h1459 | h1462 | h1552 | h1567 | h1579 | h1651 | h1702 | h1705 | h1738 | h1822 | h1894 | h1954 | h1972 | h1981
  · exact fire_of_mod2187 K 10 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 28 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 199 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 274 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 415 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 442 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 499 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 517 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 652 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 658 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 13 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 40 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 82 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 166 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 283 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 325 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 580 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 595 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 4 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 94 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 109 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 121 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 193 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 244 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 247 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 280 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 364 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 436 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 496 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 514 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 523 2 (by decide) (by decide) (by decide) (by omega)
/-- **THE DUST PINNED AT LEVEL SIX — THE MAP DOUBLES AGAIN.**  A Cantorian
dust exponent (`K ≡ 1 mod 3`) lives in one of SIXTY-FOUR surviving
residues mod 2187.  The structural law, third stroke: `2, 4, 8, 16,
32, 64` — the alive set doubles level by level without exception,
every node keeping exactly two children by the blade's one-of-three. -/
theorem cantorian_dust_mod_2187 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116 := by
  have h729 := cantorian_dust_mod_729 K hd hc
  have hrow := hc 7 (by omega)
  have hd0 : K % 2187 ≠ 10 :=
    fun h => absurd (dust_fire_row_seven K (Or.inl h)) hrow
  have hd1 : K % 2187 ≠ 28 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inl h))) hrow
  have hd2 : K % 2187 ≠ 199 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hd3 : K % 2187 ≠ 274 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hd4 : K % 2187 ≠ 415 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hd5 : K % 2187 ≠ 442 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hd6 : K % 2187 ≠ 499 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hd7 : K % 2187 ≠ 517 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hd8 : K % 2187 ≠ 652 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hd9 : K % 2187 ≠ 658 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hd10 : K % 2187 ≠ 742 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hd11 : K % 2187 ≠ 769 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hd12 : K % 2187 ≠ 811 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hd13 : K % 2187 ≠ 895 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hd14 : K % 2187 ≠ 1012 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hd15 : K % 2187 ≠ 1054 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow
  have hd16 : K % 2187 ≠ 1309 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow
  have hd17 : K % 2187 ≠ 1324 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow
  have hd18 : K % 2187 ≠ 1459 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow
  have hd19 : K % 2187 ≠ 1462 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow
  have hd20 : K % 2187 ≠ 1552 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow
  have hd21 : K % 2187 ≠ 1567 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow
  have hd22 : K % 2187 ≠ 1579 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow
  have hd23 : K % 2187 ≠ 1651 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow
  have hd24 : K % 2187 ≠ 1702 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow
  have hd25 : K % 2187 ≠ 1705 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow
  have hd26 : K % 2187 ≠ 1738 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow
  have hd27 : K % 2187 ≠ 1822 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow
  have hd28 : K % 2187 ≠ 1894 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow
  have hd29 : K % 2187 ≠ 1954 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow
  have hd30 : K % 2187 ≠ 1972 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow
  have hd31 : K % 2187 ≠ 1981 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))) hrow
  rcases h729 with h1 | h4 | h10 | h13 | h28 | h40 | h82 | h94 | h109 | h121 | h166 | h193 | h199 | h244 | h247 | h274 | h280 | h283 | h325 | h364 | h415 | h436 | h442 | h496 | h499 | h514 | h517 | h523 | h580 | h595 | h652 | h658 <;> omega

/-- **THE CASCADE KILL, LEVEL SIX.**  The thirty-two new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_six (K : Nat)
    (h : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 7 (dust_fire_row_seven K h)

/-! ## §5 The seventh cascade level — the map doubles to 128 -/

/-- **THE UNIFORM KILL, LEVEL-SEVEN FORM.**  `K ≡ r + 2187*t mod 6561`
fires at row eight when the noise receipt holds.  All arithmetic
literal. -/
theorem fire_of_mod6561 (K r t : Nat)
    (hr : r < 2187) (ht : t < 3)
    (hnoise : (digit3 (4^r) 8 + t) % 3 = 2)
    (hclass : K % 6561 = r + 2187 * t) :
    digit3 (4^K) 8 = 2 := by
  have h6561 : (3:Nat)^(7+1) = 6561 := by decide
  have h2187 : (3:Nat)^7 = 2187 := by decide
  have hK : K % 3^(7+1) = r + 3^7 * t := by
    rw [h6561, h2187]
    exact hclass
  have hr' : r < 3^7 := by
    rw [h2187]
    exact hr
  exact feedback_fire_of_class 7 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL SEVEN (row eight).**  Every exponent in one of the
sixty-four dead classes mod 6561 fires its digit two at row eight.
Generated from the worldtrace noise receipts (`noise_7(r) = digit3 (4^r) 8`,
dead child `t = (2 - noise) % 3`, dead class `r + 2187*t`) — the seventh
storey of the feedback tree, each node keeping exactly two alive
children (`unique_dead_child`). -/
theorem dust_fire_row_eight (K : Nat)
    (hK : K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412) :
    digit3 (4^K) 8 = 2 := by
  rcases hK with h82 | h247 | h580 | h757 | h976 | h1246 | h1381 | h1471 | h1486 | h1498 | h1975 | h2110 | h2200 | h2227 | h2281 | h2296 | h2308 | h2380 | h2431 | h2701 | h2710 | h2926 | h3010 | h3025 | h3037 | h3109 | h3160 | h3358 | h3430 | h3439 | h3574 | h3655 | h3811 | h3928 | h3970 | h4087 | h4240 | h4303 | h4375 | h4378 | h4540 | h4654 | h4657 | h4699 | h4738 | h4810 | h4870 | h4969 | h5104 | h5107 | h5302 | h5377 | h5383 | h5467 | h5518 | h5539 | h5599 | h5602 | h5914 | h6031 | h6106 | h6247 | h6331 | h6412
  · exact fire_of_mod6561 K 82 0 (by decide) (by decide) (by rw [show (82:Nat) = 1 + 3*27 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 247 0 (by decide) (by decide) (by rw [show (247:Nat) = 1 + 3*82 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 580 0 (by decide) (by decide) (by rw [show (580:Nat) = 1 + 3*193 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 757 0 (by decide) (by decide) (by rw [show (757:Nat) = 1 + 3*252 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 976 0 (by decide) (by decide) (by rw [show (976:Nat) = 1 + 3*325 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1246 0 (by decide) (by decide) (by rw [show (1246:Nat) = 1 + 3*415 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1381 0 (by decide) (by decide) (by rw [show (1381:Nat) = 1 + 3*460 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1471 0 (by decide) (by decide) (by rw [show (1471:Nat) = 1 + 3*490 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1486 0 (by decide) (by decide) (by rw [show (1486:Nat) = 1 + 3*495 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1498 0 (by decide) (by decide) (by rw [show (1498:Nat) = 1 + 3*499 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1975 0 (by decide) (by decide) (by rw [show (1975:Nat) = 1 + 3*658 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2110 0 (by decide) (by decide) (by rw [show (2110:Nat) = 1 + 3*703 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 13 1 (by decide) (by decide) (by rw [show (13:Nat) = 1 + 3*4 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 40 1 (by decide) (by decide) (by rw [show (40:Nat) = 1 + 3*13 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 94 1 (by decide) (by decide) (by rw [show (94:Nat) = 1 + 3*31 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 109 1 (by decide) (by decide) (by rw [show (109:Nat) = 1 + 3*36 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 121 1 (by decide) (by decide) (by rw [show (121:Nat) = 1 + 3*40 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 193 1 (by decide) (by decide) (by rw [show (193:Nat) = 1 + 3*64 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 244 1 (by decide) (by decide) (by rw [show (244:Nat) = 1 + 3*81 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 514 1 (by decide) (by decide) (by rw [show (514:Nat) = 1 + 3*171 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 523 1 (by decide) (by decide) (by rw [show (523:Nat) = 1 + 3*174 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 739 1 (by decide) (by decide) (by rw [show (739:Nat) = 1 + 3*246 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 823 1 (by decide) (by decide) (by rw [show (823:Nat) = 1 + 3*274 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 838 1 (by decide) (by decide) (by rw [show (838:Nat) = 1 + 3*279 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 850 1 (by decide) (by decide) (by rw [show (850:Nat) = 1 + 3*283 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 922 1 (by decide) (by decide) (by rw [show (922:Nat) = 1 + 3*307 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 973 1 (by decide) (by decide) (by rw [show (973:Nat) = 1 + 3*324 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1171 1 (by decide) (by decide) (by rw [show (1171:Nat) = 1 + 3*390 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1243 1 (by decide) (by decide) (by rw [show (1243:Nat) = 1 + 3*414 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1252 1 (by decide) (by decide) (by rw [show (1252:Nat) = 1 + 3*417 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1387 1 (by decide) (by decide) (by rw [show (1387:Nat) = 1 + 3*462 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1468 1 (by decide) (by decide) (by rw [show (1468:Nat) = 1 + 3*489 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1624 1 (by decide) (by decide) (by rw [show (1624:Nat) = 1 + 3*541 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1741 1 (by decide) (by decide) (by rw [show (1741:Nat) = 1 + 3*580 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1783 1 (by decide) (by decide) (by rw [show (1783:Nat) = 1 + 3*594 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1900 1 (by decide) (by decide) (by rw [show (1900:Nat) = 1 + 3*633 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2053 1 (by decide) (by decide) (by rw [show (2053:Nat) = 1 + 3*684 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2116 1 (by decide) (by decide) (by rw [show (2116:Nat) = 1 + 3*705 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1 2 (by decide) (by decide) (by rw [show (1:Nat) = 1 + 3*0 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 4 2 (by decide) (by decide) (by rw [show (4:Nat) = 1 + 3*1 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 166 2 (by decide) (by decide) (by rw [show (166:Nat) = 1 + 3*55 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 280 2 (by decide) (by decide) (by rw [show (280:Nat) = 1 + 3*93 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 283 2 (by decide) (by decide) (by rw [show (283:Nat) = 1 + 3*94 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 325 2 (by decide) (by decide) (by rw [show (325:Nat) = 1 + 3*108 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 364 2 (by decide) (by decide) (by rw [show (364:Nat) = 1 + 3*121 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 436 2 (by decide) (by decide) (by rw [show (436:Nat) = 1 + 3*145 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 496 2 (by decide) (by decide) (by rw [show (496:Nat) = 1 + 3*165 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 595 2 (by decide) (by decide) (by rw [show (595:Nat) = 1 + 3*198 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 730 2 (by decide) (by decide) (by rw [show (730:Nat) = 1 + 3*243 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 733 2 (by decide) (by decide) (by rw [show (733:Nat) = 1 + 3*244 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 928 2 (by decide) (by decide) (by rw [show (928:Nat) = 1 + 3*309 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1003 2 (by decide) (by decide) (by rw [show (1003:Nat) = 1 + 3*334 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1009 2 (by decide) (by decide) (by rw [show (1009:Nat) = 1 + 3*336 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1093 2 (by decide) (by decide) (by rw [show (1093:Nat) = 1 + 3*364 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1144 2 (by decide) (by decide) (by rw [show (1144:Nat) = 1 + 3*381 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1165 2 (by decide) (by decide) (by rw [show (1165:Nat) = 1 + 3*388 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1225 2 (by decide) (by decide) (by rw [show (1225:Nat) = 1 + 3*408 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1228 2 (by decide) (by decide) (by rw [show (1228:Nat) = 1 + 3*409 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1540 2 (by decide) (by decide) (by rw [show (1540:Nat) = 1 + 3*513 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1657 2 (by decide) (by decide) (by rw [show (1657:Nat) = 1 + 3*552 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1732 2 (by decide) (by decide) (by rw [show (1732:Nat) = 1 + 3*577 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1873 2 (by decide) (by decide) (by rw [show (1873:Nat) = 1 + 3*624 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1957 2 (by decide) (by decide) (by rw [show (1957:Nat) = 1 + 3*652 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2038 2 (by decide) (by decide) (by rw [show (2038:Nat) = 1 + 3*679 from by decide, wt_row_eight_read]; decide) (by omega)

/-- **THE DUST PINNED AT LEVEL SEVEN — THE MAP DOUBLES TO 128.**  A
Cantorian dust exponent (`K ≡ 1 mod 3`) lives in one of ONE HUNDRED
TWENTY-EIGHT surviving residues mod 6561.  The structural law, fourth
stroke: `2, 4, 8, 16, 32, 64, 128` — the alive set doubles level by
level without exception, every node keeping exactly two children by
the blade's one-of-three. -/
theorem cantarian_dust_mod_6561 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 6561 = 1 ∨ K % 6561 = 4 ∨ K % 6561 = 13 ∨ K % 6561 = 40 ∨ K % 6561 = 94 ∨ K % 6561 = 109 ∨ K % 6561 = 121 ∨ K % 6561 = 166 ∨ K % 6561 = 193 ∨ K % 6561 = 244 ∨ K % 6561 = 280 ∨ K % 6561 = 283 ∨ K % 6561 = 325 ∨ K % 6561 = 364 ∨ K % 6561 = 436 ∨ K % 6561 = 496 ∨ K % 6561 = 514 ∨ K % 6561 = 523 ∨ K % 6561 = 595 ∨ K % 6561 = 730 ∨ K % 6561 = 733 ∨ K % 6561 = 739 ∨ K % 6561 = 823 ∨ K % 6561 = 838 ∨ K % 6561 = 850 ∨ K % 6561 = 922 ∨ K % 6561 = 928 ∨ K % 6561 = 973 ∨ K % 6561 = 1003 ∨ K % 6561 = 1009 ∨ K % 6561 = 1093 ∨ K % 6561 = 1144 ∨ K % 6561 = 1165 ∨ K % 6561 = 1171 ∨ K % 6561 = 1225 ∨ K % 6561 = 1228 ∨ K % 6561 = 1243 ∨ K % 6561 = 1252 ∨ K % 6561 = 1387 ∨ K % 6561 = 1468 ∨ K % 6561 = 1540 ∨ K % 6561 = 1624 ∨ K % 6561 = 1657 ∨ K % 6561 = 1732 ∨ K % 6561 = 1741 ∨ K % 6561 = 1783 ∨ K % 6561 = 1873 ∨ K % 6561 = 1900 ∨ K % 6561 = 1957 ∨ K % 6561 = 2038 ∨ K % 6561 = 2053 ∨ K % 6561 = 2116 ∨ K % 6561 = 2188 ∨ K % 6561 = 2191 ∨ K % 6561 = 2269 ∨ K % 6561 = 2353 ∨ K % 6561 = 2434 ∨ K % 6561 = 2467 ∨ K % 6561 = 2470 ∨ K % 6561 = 2512 ∨ K % 6561 = 2551 ∨ K % 6561 = 2623 ∨ K % 6561 = 2683 ∨ K % 6561 = 2767 ∨ K % 6561 = 2782 ∨ K % 6561 = 2917 ∨ K % 6561 = 2920 ∨ K % 6561 = 2944 ∨ K % 6561 = 3115 ∨ K % 6561 = 3163 ∨ K % 6561 = 3190 ∨ K % 6561 = 3196 ∨ K % 6561 = 3280 ∨ K % 6561 = 3331 ∨ K % 6561 = 3352 ∨ K % 6561 = 3412 ∨ K % 6561 = 3415 ∨ K % 6561 = 3433 ∨ K % 6561 = 3568 ∨ K % 6561 = 3658 ∨ K % 6561 = 3673 ∨ K % 6561 = 3685 ∨ K % 6561 = 3727 ∨ K % 6561 = 3844 ∨ K % 6561 = 3919 ∨ K % 6561 = 4060 ∨ K % 6561 = 4144 ∨ K % 6561 = 4162 ∨ K % 6561 = 4225 ∨ K % 6561 = 4297 ∨ K % 6561 = 4387 ∨ K % 6561 = 4414 ∨ K % 6561 = 4456 ∨ K % 6561 = 4468 ∨ K % 6561 = 4483 ∨ K % 6561 = 4495 ∨ K % 6561 = 4567 ∨ K % 6561 = 4618 ∨ K % 6561 = 4621 ∨ K % 6561 = 4888 ∨ K % 6561 = 4897 ∨ K % 6561 = 4954 ∨ K % 6561 = 5113 ∨ K % 6561 = 5131 ∨ K % 6561 = 5197 ∨ K % 6561 = 5212 ∨ K % 6561 = 5224 ∨ K % 6561 = 5296 ∨ K % 6561 = 5347 ∨ K % 6561 = 5350 ∨ K % 6561 = 5545 ∨ K % 6561 = 5617 ∨ K % 6561 = 5620 ∨ K % 6561 = 5626 ∨ K % 6561 = 5755 ∨ K % 6561 = 5761 ∨ K % 6561 = 5842 ∨ K % 6561 = 5845 ∨ K % 6561 = 5860 ∨ K % 6561 = 5872 ∨ K % 6561 = 5998 ∨ K % 6561 = 6115 ∨ K % 6561 = 6157 ∨ K % 6561 = 6274 ∨ K % 6561 = 6349 ∨ K % 6561 = 6427 ∨ K % 6561 = 6484 ∨ K % 6561 = 6490 := by
  have h2187 := cantorian_dust_mod_2187 K hd hc
  have hrow := hc 8 (by omega)
  have hd0 : K % 6561 ≠ 82 :=
    fun h => absurd (dust_fire_row_eight K (Or.inl h)) hrow
  have hd1 : K % 6561 ≠ 247 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inl h))) hrow
  have hd2 : K % 6561 ≠ 580 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hd3 : K % 6561 ≠ 757 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hd4 : K % 6561 ≠ 976 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hd5 : K % 6561 ≠ 1246 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hd6 : K % 6561 ≠ 1381 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hd7 : K % 6561 ≠ 1471 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hd8 : K % 6561 ≠ 1486 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hd9 : K % 6561 ≠ 1498 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hd10 : K % 6561 ≠ 1975 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hd11 : K % 6561 ≠ 2110 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hd12 : K % 6561 ≠ 2200 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hd13 : K % 6561 ≠ 2227 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hd14 : K % 6561 ≠ 2281 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hd15 : K % 6561 ≠ 2296 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow
  have hd16 : K % 6561 ≠ 2308 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow
  have hd17 : K % 6561 ≠ 2380 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow
  have hd18 : K % 6561 ≠ 2431 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow
  have hd19 : K % 6561 ≠ 2701 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow
  have hd20 : K % 6561 ≠ 2710 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow
  have hd21 : K % 6561 ≠ 2926 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow
  have hd22 : K % 6561 ≠ 3010 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow
  have hd23 : K % 6561 ≠ 3025 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow
  have hd24 : K % 6561 ≠ 3037 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow
  have hd25 : K % 6561 ≠ 3109 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow
  have hd26 : K % 6561 ≠ 3160 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow
  have hd27 : K % 6561 ≠ 3358 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow
  have hd28 : K % 6561 ≠ 3430 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow
  have hd29 : K % 6561 ≠ 3439 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow
  have hd30 : K % 6561 ≠ 3574 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow
  have hd31 : K % 6561 ≠ 3655 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))) hrow
  have hd32 : K % 6561 ≠ 3811 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))) hrow
  have hd33 : K % 6561 ≠ 3928 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))) hrow
  have hd34 : K % 6561 ≠ 3970 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))) hrow
  have hd35 : K % 6561 ≠ 4087 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))) hrow
  have hd36 : K % 6561 ≠ 4240 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))) hrow
  have hd37 : K % 6561 ≠ 4303 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))) hrow
  have hd38 : K % 6561 ≠ 4375 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))) hrow
  have hd39 : K % 6561 ≠ 4378 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))) hrow
  have hd40 : K % 6561 ≠ 4540 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))) hrow
  have hd41 : K % 6561 ≠ 4654 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd42 : K % 6561 ≠ 4657 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd43 : K % 6561 ≠ 4699 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd44 : K % 6561 ≠ 4738 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd45 : K % 6561 ≠ 4810 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd46 : K % 6561 ≠ 4870 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd47 : K % 6561 ≠ 4969 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd48 : K % 6561 ≠ 5104 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd49 : K % 6561 ≠ 5107 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd50 : K % 6561 ≠ 5302 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd51 : K % 6561 ≠ 5377 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd52 : K % 6561 ≠ 5383 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd53 : K % 6561 ≠ 5467 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd54 : K % 6561 ≠ 5518 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd55 : K % 6561 ≠ 5539 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd56 : K % 6561 ≠ 5599 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd57 : K % 6561 ≠ 5602 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd58 : K % 6561 ≠ 5914 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd59 : K % 6561 ≠ 6031 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd60 : K % 6561 ≠ 6106 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd61 : K % 6561 ≠ 6247 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd62 : K % 6561 ≠ 6331 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd63 : K % 6561 ≠ 6412 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  rcases h2187 with h1 | h4 | h13 | h40 | h82 | h94 | h109 | h121 | h166 | h193 | h244 | h247 | h280 | h283 | h325 | h364 | h436 | h496 | h514 | h523 | h580 | h595 | h730 | h733 | h739 | h757 | h823 | h838 | h850 | h922 | h928 | h973 | h976 | h1003 | h1009 | h1093 | h1144 | h1165 | h1171 | h1225 | h1228 | h1243 | h1246 | h1252 | h1381 | h1387 | h1468 | h1471 | h1486 | h1498 | h1540 | h1624 | h1657 | h1732 | h1741 | h1783 | h1873 | h1900 | h1957 | h1975 | h2038 | h2053 | h2110 | h2116 <;> omega

/-- **THE CASCADE KILL, LEVEL SEVEN.**  The sixty-four new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_seven (K : Nat)
    (h : K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 8 (dust_fire_row_eight K h)

/-! ## Section 6 The pair-read fire — GAP-E1's first family -/

/-- **THE PAIR-READ FORMULA.**  The two-support tower factorization,
read through the green `prefaced_digit`:  for `1 ≤ j` and any trunk
`T` with `4^T < 3^(j+2)`, the row-`(j+4)` digit of `4^(T + 3^(j+1)*u)`
is the row-two digit of the worldtrace product `4^T * u * c (j+1)`.
The first brick of GAP-E1: the multi-support carry read, exact,
machine-verified 0 failures on 300 random (T, u, j). -/
theorem pair_read_formula (T u j : Nat) (hj : 1 ≤ j) (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2 := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term (3^(j+2) * GSTTowerFire.c (j+1)) u
  have htow : 4^(3^(j+1)) = 1 + 3^(j+2) * GSTTowerFire.c (j+1) :=
    GSTTowerFire.four_pow_three_pow_eq (j+1)
  have key : 4^(T + 3^(j+1)*u)
      = 3^(j+2) * (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)))
        + 4^T := by
    rw [Nat.pow_add, Nat.pow_mul, htow, hR]
    ring
  rw [key]
  have hp : digit3 (3^(j+2) * (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) + 4^T) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) 2 :=
    GSTTowerFire.prefaced_digit _ (4^T) (j+1) 2 hT
  rw [hp]
  refine digit3_eq_of_mod_next _ _ 2 ?_
  show (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) % 27
     = (4^T * u * GSTTowerFire.c (j+1)) % 27
  have h27eq : 3^(j+2) = 27 * 3^(j-1) := by
    have hsum : j + 2 = (j - 1) + 3 := by omega
    rw [hsum, Nat.pow_add]
    ring
  have hd2 : 27 ∣ 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)) := by
    refine ⟨3^(j-1) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)), ?_⟩
    rw [h27eq]
    ring
  have hz : 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)) % 27 = 0 := Nat.mod_eq_zero_of_dvd hd2
  omega

/-- **THE PAIR-READ FIRE.**  Every exponent `K = 4 + 3^(j+1)*u` with
`j ≤ 4` and `u = 1 ∨ u = 4 ∨ u = 7` fires its digit two at row `j + 4` —
the pair term `3^(j+2) * (256 * u * c (j+1))` read through the green
`c_mod81` (`c = 16 mod 27`): the digit is trit two of `19*u`, which is
two exactly for `u` in {1, 4, 7}.  GAP-E1's first infinite family:
one theorem, the exponents 247, 733, 976, 1705, 2191, 2920, ... — the
class-4 trunk with a one-trit branch `u = 1 mod 3`, a family NO finite
cascade level ever reaches (these exponents ride the class-4 trunk,
and class 4 survives every fixed level).  Machine-verified: j = 4..12
all fire. -/
theorem pair_read_fire (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2 := by
  have h6 : (3:Nat)^6 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h256 : (4:Nat)^4 = 256 := by decide
  have h729 : (3:Nat)^6 = 729 := by decide
  have hT : (4:Nat)^4 < 3^(j+2) := by omega
  have hc : GSTTowerFire.c (j+1) % 27 = 16 := by
    have h81 := GSTTowerFire.c_mod81 (j+1) (by omega)
    have hrr := Nat.mod_mod_of_dvd (GSTTowerFire.c (j+1)) (by decide : (27:Nat) ∣ 81)
    rw [← hrr, h81]
  have hform := pair_read_formula 4 u j (by omega) hT
  rw [hform, h256]
  rcases hu with rfl | rfl | rfl
  · have hmod : (256 * 1 * GSTTowerFire.c (j+1)) % 27 = 19 % 27 := by
      rw [Nat.mul_one, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)
  · have hmod : (256 * 4 * GSTTowerFire.c (j+1)) % 27 = 76 % 27 := by
      rw [show (256:Nat) * 4 = 1024 from by decide, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)
  · have hmod : (256 * 7 * GSTTowerFire.c (j+1)) % 27 = 133 % 27 := by
      rw [show (256:Nat) * 7 = 1792 from by decide, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)

/-- **THE PAIR-READ KILL.**  The family dies outright through the repo's
own kill chain. -/
theorem no22_of_pair_read (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    noTernaryTwo (4^(4 + 3^(j+1)*u)) = false :=
  no22_of_digit_two _ (j+4) (pair_read_fire u j hj hu)

/-- **THE PAIR-READ RECEIPT.**  The GAP-E1 brick assembled: the uniform
read formula, the infinite fire family, and the kill chain. -/
theorem the_pair_read_receipt :
    (∀ T u j : Nat, 1 ≤ j → 4^T < 3^(j+2) →
      digit3 (4^(T + 3^(j+1)*u)) (j+4)
        = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2) ∧
    (∀ u j : Nat, 4 ≤ j → (u = 1 ∨ u = 4 ∨ u = 7) →
      digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2) ∧
    (∀ u j : Nat, 4 ≤ j → (u = 1 ∨ u = 4 ∨ u = 7) →
      noTernaryTwo (4^(4 + 3^(j+1)*u)) = false) :=
  ⟨pair_read_formula, pair_read_fire, no22_of_pair_read⟩

/-! ## Section 7 The general trunk-uniform fire — any trunk, any branch -/

/-- **THE ROW-TWO READ FROM THE KILL ZONE.**  A number whose mod-27
residue lands at or above eighteen reads digit two at row two — the
kill zone of the worldtrace pair-read. -/
theorem digit3_row_two_of_residue (x : Nat) (hx : 18 ≤ x % 27) :
    digit3 x 2 = 2 := by
  have hlt : x % 27 < 27 := Nat.mod_lt _ (by decide : 0 < 27)
  show x / 9 % 3 = 2
  omega

/-- **THE PAIR-READ RESIDUE.**  The worldtrace product's mod-27 residue
is computable without the tower:  `c (j+1)` is `16 mod 27` (green
`c_mod81`), so the read `4^T * u * c (j+1)` reduces to `4^T * u * 16`.
Machine-verified 0 failures on 400 random triples. -/
theorem pair_residue_mod27 (T u j : Nat) (hj : 2 ≤ j) :
    (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27 := by
  have hc : GSTTowerFire.c (j+1) % 27 = 16 := by
    have h81 := GSTTowerFire.c_mod81 (j+1) (by omega)
    have hrr := Nat.mod_mod_of_dvd (GSTTowerFire.c (j+1)) (by decide : (27:Nat) ∣ 81)
    rw [← hrr, h81]
  have h16 : (16:Nat) % 27 = 16 := by decide
  have hl := Nat.mul_mod (4^T * u) (GSTTowerFire.c (j+1)) 27
  have hr := Nat.mul_mod (4^T * u) 16 27
  rw [hl, hr, hc, h16]

/-- **THE GENERAL TRUNK-UNIFORM FIRE.**  ANY trunk `T`, ANY branch `u`:
whenever the mod-27 residue `(4^T * u * 16) % 27` lands in the kill
zone (`18 ≤ residue`), the exponent `T + 3^(j+1)*u` fires its digit
two at row `j+4`.  The kill condition is a mod-27 computation on the
trunk residue and the branch — the Cantor automaton's transition,
uniform across the entire dust tree.  Machine-verified 0 failures on
120 valid random triples. -/
theorem pair_read_fire_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2 := by
  have hform := pair_read_formula T u j (by omega) hT
  rw [hform]
  exact digit3_row_two_of_residue _ (by
    rw [pair_residue_mod27 T u j (by omega)]
    exact hkill)

/-- **THE GENERAL PAIR-READ KILL.**  The family dies outright through
the repo's own kill chain. -/
theorem no22_of_pair_read_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    noTernaryTwo (4^(T + 3^(j+1)*u)) = false :=
  no22_of_digit_two _ (j+4) (pair_read_fire_general T u j hj hT hkill)

/-- **SECOND FAMILY — the trunk-13 dust class.**  Class 13 (a level-two
dust survivor) with a single deep branch:  fires at row `j+4` for
every `j ≥ 15`.  The trunk residue `4^13 mod 27 = 13` gives kill
residue `13 * 16 mod 27 = 19`, inside the kill zone. -/
theorem pair_read_fire_demo_two (j : Nat) (hj : 15 ≤ j) :
    digit3 (4^(13 + 3^(j+1))) (j+4) = 2 := by
  have h17 : (3:Nat)^17 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4 : (4:Nat)^13 < (3:Nat)^17 := by decide
  have hgen := pair_read_fire_general 13 1 j (by omega) (by omega) (by decide)
  rw [Nat.mul_one] at hgen
  exact hgen

/-- **THIRD FAMILY — the trunk-10 class with branch two.**  Class 10
(a level-two dust survivor) with branch `u = 2`:  fires at row `j+4`
for every `j ≥ 11`.  Kill residue `4 * 2 * 16 mod 27 = 20`. -/
theorem pair_read_fire_demo_three (j : Nat) (hj : 11 ≤ j) :
    digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2 := by
  have h13 : (3:Nat)^13 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4 : (4:Nat)^10 < (3:Nat)^13 := by decide
  exact pair_read_fire_general 10 2 j (by omega) (by omega) (by decide)

/-- **THE GENERAL FIRE RECEIPT.**  The GAP-E1 engine assembled: the
residue transfer, the row-two kill-zone read, the general trunk-uniform
fire (any trunk, any branch), the kill chain, and two new infinite
families (trunk 13 single-branch; trunk 10 with branch two). -/
theorem the_general_fire_receipt :
    (∀ T u j : Nat, 2 ≤ j →
      (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27) ∧
    (∀ x : Nat, 18 ≤ x % 27 → digit3 x 2 = 2) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
      digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
      noTernaryTwo (4^(T + 3^(j+1)*u)) = false) ∧
    (∀ j : Nat, 15 ≤ j → digit3 (4^(13 + 3^(j+1))) (j+4) = 2) ∧
    (∀ j : Nat, 11 ≤ j → digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2) :=
  ⟨pair_residue_mod27, digit3_row_two_of_residue, pair_read_fire_general,
    no22_of_pair_read_general, pair_read_fire_demo_two, pair_read_fire_demo_three⟩

/-! ## Section 8 The top-split and the addition window — the descent engine -/

/-- **THE EXACT TOP SPLIT.**  For an exponent `K` whose top trit sits at
position `H` (`K < 3^(H+1)`), the power splits as the trunk power, the
branch term, and a tail dead below row `2H+2`.  The deep rows of `4^K`
are a pure base-3 addition of the trunk's digits and the shifted
digits of `X = t * c(H) * 4^trunk`.  Machine-verified: the
addition-window law holds 600/600 on random `(H, trunk, t)`. -/
theorem top_split (K H : Nat) (hK : K < 3^(H+1)) :
    ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)
        + 3^(H+1) * Y) := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term (3^(H+1) * GSTTowerFire.c H) (K / 3^H)
  have hsplit : K % 3^H + 3^H * (K / 3^H) = K := Nat.mod_add_div K (3^H)
  have hexp : 4^K = 4^(K % 3^H) * (1 + 3^(H+1) * GSTTowerFire.c H)^(K / 3^H) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.pow_add, Nat.pow_mul, GSTTowerFire.four_pow_three_pow_eq H]
  refine ⟨Nat.choose (K / 3^H) 2 * GSTTowerFire.c H * GSTTowerFire.c H * 4^(K % 3^H)
      + 3^(H+1) * (GSTTowerFire.c H * GSTTowerFire.c H * GSTTowerFire.c H * R * 4^(K % 3^H)), ?_⟩
  rw [hexp, hR]
  ring

/-- **THE ADDITION WINDOW.**  Below row `2H+2`, the digits of `4^K` read
the two-term sum `4^trunk + 3^(H+1) * X` — the dead tail of the top
split is invisible.  The descent engine's foundation. -/
theorem window_congr (K H r : Nat) (hK : K < 3^(H+1)) (hr : r + 1 ≤ 2*H+2) :
    digit3 (4^K) r = digit3 (4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r := by
  obtain ⟨Y, hY⟩ := top_split K H hK
  refine digit3_eq_of_mod_next _ _ r ?_
  rw [hY, Nat.mul_add]
  have hpow : 3^(H+1) * 3^(H+1) = 3^(2*H+2) := by
    have h := Nat.pow_add 3 (H+1) (H+1)
    rw [show (H+1)+(H+1) = 2*H+2 from by omega] at h
    exact h.symm
  have hdvd : 3^(r+1) ∣ 3^(H+1) * (3^(H+1) * Y) := by
    rw [← Nat.mul_assoc, hpow]
    exact (Nat.pow_dvd_pow 3 (by omega)).mul_right Y
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, ← Nat.add_assoc]
  exact Nat.add_mul_mod_self_left _ _ _

/-- **THE ROW-(H+2) WINDOW LAW.**  The digit at row `H+2` of `4^K` is
the trunk's own digit at that row, plus the first trit of the branch
factor `X = t * c(H) * 4^trunk`, plus the carry from row `H+1` — a pure
base-3 addition read.  Machine-verified 800/800. -/
theorem window_row_two (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1)) :
    digit3 (4^K) (H+2)
      = (digit3 (4^(K % 3^H)) (H+2)
          + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
          + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3 := by
  have htpow : 3^(H+2) = 3^(H+1) * 3 := Nat.pow_succ 3 (H+1)
  have ht : K / 3^H < 3 := by
    rw [Nat.pow_succ 3 H] at hK
    by_contra hc
    have hd := Nat.mod_add_div K (3^H)
    have hle : 3^H * 3 ≤ 3^H * (K / 3^H) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hx3 : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) % 3 = K / 3^H := by
    have hc : GSTTowerFire.c H % 3 = 1 := GSTTowerFire.c_mod3 H
    have hA3 : (4^(K % 3^H)) % 3 = 1 := GSTClimbInfiniteFamily.pow4_mod3 (K % 3^H)
    have ht3 : (K / 3^H) % 3 = K / 3^H := Nat.mod_eq_of_lt ht
    have hpair : ((K / 3^H) * GSTTowerFire.c H) % 3 = (K / 3^H) % 3 := by
      rw [Nat.mul_mod, hc, Nat.mul_one]
      omega
    rw [Nat.mul_mod, hpair, hA3, Nat.mul_one, ht3, ht3]
  rw [window_congr K H (H+2) hK (by omega)]
  set A := 4^(K % 3^H) with hAdef
  set X := (K / 3^H) * GSTTowerFire.c H * A with hXdef
  have hp1 : 0 < 3^(H+1) := Nat.pow_pos (by decide)
  have hr1lt : A % 3^(H+2) % 3^(H+1) < 3^(H+1) :=
    Nat.mod_lt _ hp1
  unfold digit3
  have hdiv : (A + 3^(H+1) * X) / 3^(H+2)
      = A / 3^(H+2) + X / 3 + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3 := by
    have hAsplit := Nat.div_add_mod A (3^(H+2))
    have hDsplit := Nat.div_add_mod (A % 3^(H+2)) (3^(H+1))
    have hXsplit := Nat.div_add_mod X 3
    rw [hx3] at hXsplit
    have hq3split := Nat.div_add_mod (A % 3^(H+2) / 3^(H+1) + K / 3^H) 3
    have hkey : A + 3^(H+1) * X
        = 3^(H+2) * (A / 3^(H+2) + X / 3
            + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3)
          + (3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
            + A % 3^(H+2) % 3^(H+1)) := by
      linear_combination
        -(hAsplit + 3^(H+1) * hXsplit + hDsplit + 3^(H+1) * hq3split)
        - (X / 3 + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3) * htpow
    have hslt : 3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
        + A % 3^(H+2) % 3^(H+1) < 3^(H+2) := by
      have h3lt : (A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3 < 3 :=
        Nat.mod_lt _ (by decide)
      have hmul : 3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
          ≤ 3^(H+1) * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [hkey, GSTTowerFire.div_add_lt (H+2) _ _ hslt]
  rw [hdiv]
  have hd1 : A / 3^(H+1) % 3 = A % 3^(H+2) / 3^(H+1) := by
    have hAsplit := Nat.div_add_mod A (3^(H+2))
    have hDsplit := Nat.div_add_mod (A % 3^(H+2)) (3^(H+1))
    have hA2 : A = 3^(H+1) * (3 * (A / 3^(H+2)) + A % 3^(H+2) / 3^(H+1))
        + A % 3^(H+2) % 3^(H+1) := by
      linear_combination -(hAsplit + hDsplit) + (A / 3^(H+2)) * htpow
    have hdiv2 : A / 3^(H+1)
        = 3 * (A / 3^(H+2)) + A % 3^(H+2) / 3^(H+1) := by
      conv_lhs => rw [hA2]
      exact GSTTowerFire.div_add_lt (H+1) _ _ hr1lt
    have hDlt : A % 3^(H+2) / 3^(H+1) < 3 := by
      by_contra hc
      push_neg at hc
      have hle : 3^(H+1) * 3 ≤ 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) :=
        Nat.mul_le_mul_left _ hc
      have h1 : 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) ≤ A % 3^(H+2) := by
        omega
      have h2 : 3^(H+2) ≤ 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) := by
        conv_lhs => rw [htpow]
        exact hle
      omega
    rw [hdiv2]
    rw [Nat.add_comm (3 * (A / 3^(H+2))) (A % 3^(H+2) / 3^(H+1))]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hDlt
  rw [hd1]
  omega

/-- **THE DESCENT ENGINE RECEIPT.**  The top split, the addition window,
and the row-(H+2) law assembled. -/
theorem the_descent_engine_receipt :
    (∀ K H : Nat, K < 3^(H+1) → ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H) + 3^(H+1) * Y)) ∧
    (∀ K H r : Nat, K < 3^(H+1) → r + 1 ≤ 2*H+2 →
      digit3 (4^K) r = digit3 (4^(K % 3^H)
        + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r) ∧
    (∀ K H : Nat, 1 ≤ H → K < 3^(H+1) →
      digit3 (4^K) (H+2)
        = (digit3 (4^(K % 3^H)) (H+2)
            + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
            + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3) :=
  ⟨fun K H hK => top_split K H hK,
    fun K H r hK hr => window_congr K H r hK hr,
    fun K H hH hK => window_row_two K H hH hK⟩

/-! ## Section 9 The dust window laws — the branch term vanishes mod nine -/

/-- **THE PERIOD-NINE LAW.**  `4^r mod 9` depends only on `r mod 3`
(`4^3 = 64 = 1 + 9*7`).  Receipt: 0 failures for r < 100. -/
theorem four_pow_mod9 (r : Nat) : (4:Nat)^r % 9 = 4^(r % 3) % 9 := by
  have hsplit := Nat.div_add_mod r 3
  obtain ⟨W, hW⟩ := one_add_pow_three_term (9 * 7) (r / 3)
  have h64 : (4:Nat)^(3:Nat) = 1 + 9 * 7 := by decide
  have hexp : (4:Nat)^r = (1 + 9 * 7)^(r / 3) * 4^(r % 3) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.pow_add, Nat.pow_mul, h64]
  rw [hexp, hW]
  have hdvd : 9 ∣ (r / 3) * (9 * 7)
      + Nat.choose (r / 3) 2 * (9 * 7) * (9 * 7)
      + (9 * 7) * (9 * 7) * (9 * 7) * W := by
    refine ⟨(r / 3) * 7 + 9 * (Nat.choose (r / 3) 2 * 7 * 7)
      + 9 * 9 * (7 * 7 * 7 * W), ?_⟩
    ring
  obtain ⟨q, hq⟩ := hdvd
  have hfold : (1 + (r / 3) * (9 * 7)
      + Nat.choose (r / 3) 2 * (9 * 7) * (9 * 7)
      + (9 * 7) * (9 * 7) * (9 * 7) * W) * 4^(r % 3)
      = 4^(r % 3) + 9 * (4^(r % 3) * q) := by
    linear_combination 4^(r % 3) * hq
  rw [hfold, Nat.add_mul_mod_self_left]

/-- **THE DUST BRANCH FACTOR.**  For a dust trunk (`trunk mod 3 = 1`)
the branch factor `X = t * c(H) * 4^trunk` satisfies `X mod 9 = t` —
`c(H)` is `7 mod 9`, `4^trunk` is `4 mod 9`, and `7 * 4 = 28 = 1 mod 9`.
Receipt: 0 failures on 300 random (H, trunk, t). -/
theorem dust_branch_mod9 (t trunk H : Nat) (hH : 1 ≤ H) (htr : trunk % 3 = 1)
    (ht : t < 3) :
    (t * GSTTowerFire.c H * 4^trunk) % 9 = t := by
  have hc := GSTTowerFire.c_mod9 H hH
  have h4 := four_pow_mod9 trunk
  rw [htr] at h4
  have h41 : (4:Nat)^(1:Nat) % 9 = 4 := by decide
  rw [h41] at h4
  have h1 := Nat.mul_mod t (GSTTowerFire.c H) 9
  have h2 := Nat.mul_mod (t * GSTTowerFire.c H) (4^trunk) 9
  rw [h2, h1, hc, h4]
  omega

/-- **THE DUST ROW-(H+2) LAW — the branch term vanishes.**  For a dust
exponent (`K mod 3 = 1`) the row-(H+2) digit is JUST the trunk's digit
plus the carry — the branch factor's first trit is zero because
`X mod 9 = t < 3`.  The descent's cleanest rung.  Receipt: 196/196. -/
theorem window_row_two_dust (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1))
    (hdust : K % 3 = 1) :
    digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
      + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3 := by
  have ht : K / 3^H < 3 := by
    rw [Nat.pow_succ 3 H] at hK
    by_contra hc
    have hd := Nat.mod_add_div K (3^H)
    have hle : 3^H * 3 ≤ 3^H * (K / 3^H) := Nat.mul_le_mul_left _ (by omega)
    omega
  have htr : (K % 3^H) % 3 = 1 := by
    have hd3 : (3:Nat) ∣ 3^H := by
      refine ⟨3^(H-1), ?_⟩
      rw [Nat.mul_comm, ← Nat.pow_succ 3 (H-1)]
      congr 1
      omega
    have hrr := Nat.mod_mod_of_dvd K hd3
    omega
  rw [window_row_two K H hH hK]
  have hx9 : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) % 9 = K / 3^H :=
    dust_branch_mod9 (K / 3^H) (K % 3^H) H hH htr ht
  have hterm : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3 = 0 := by
    have hmm := Nat.mod_mod_of_dvd
      ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) (by decide : (3:Nat) ∣ 9)
    have hdm := Nat.div_add_mod
      ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) 9
    omega
  rw [hterm]
  omega

/-- **THE WINDOW REDUCTION.**  The digit at row `H+1+s` of the two-term
sum only sees the first `s+1` trits of the branch factor — reduce
`X mod 3^(s+1)` and the higher trits are invisible.  The consumers'
computational handle: the reduced branch factor is small. -/
theorem window_reduce (A X H s : Nat) :
    digit3 (A + 3^(H+1) * X) (H+1+s)
      = digit3 (A + 3^(H+1) * (X % 3^(s+1))) (H+1+s) := by
  refine digit3_eq_of_mod_next _ _ (H+1+s) ?_
  rw [show (H:Nat)+1+s+1 = H+s+2 from by omega]
  have hX := Nat.div_add_mod X (3^(s+1))
  have hpow : 3^(H+1) * 3^(s+1) = 3^(H+s+2) := by
    have h := Nat.pow_add 3 (H+1) (s+1)
    rw [show (H:Nat)+1+(s+1) = H+s+2 from by omega] at h
    exact h.symm
  have hfold : A + 3^(H+1) * X
      = A + 3^(H+1) * (X % 3^(s+1)) + 3^(H+s+2) * (X / 3^(s+1)) := by
    conv_lhs => rw [← hX]
    rw [Nat.mul_add, ← Nat.mul_assoc, hpow]
    ring
  rw [hfold]
  exact Nat.add_mul_mod_self_left _ _ _

/-- Canonical finite window class seen by a row-H+1+s Worldtrace read. -/
def worldtraceWindowClass (X s : Nat) : Nat :=
  X % 3^(s+1)

/-- The Worldtrace read factors exactly through the finite window class. -/
theorem window_read_factors
    (A X H s : Nat) :
    digit3 (A + 3^(H+1) * X) (H+1+s) =
      digit3
        (A + 3^(H+1) * worldtraceWindowClass X s)
        (H+1+s) := by
  exact window_reduce A X H s

/-- **WINDOW-QUOTIENT INVARIANCE.**
Two branch factors with the same visible window class are indistinguishable
to the row-H+1+s read. -/
theorem window_class_invariant
    (A X Y H s : Nat)
    (hXY : worldtraceWindowClass X s =
      worldtraceWindowClass Y s) :
    digit3 (A + 3^(H+1) * X) (H+1+s) =
      digit3 (A + 3^(H+1) * Y) (H+1+s) := by
  rw [window_read_factors A X H s,
      window_read_factors A Y H s,
      hXY]

/-- Congruence modulo the visible window modulus is sufficient for exact read
equality. -/
theorem window_mod_congr_invariant
    (A X Y H s : Nat)
    (hXY : X % 3^(s+1) = Y % 3^(s+1)) :
    digit3 (A + 3^(H+1) * X) (H+1+s) =
      digit3 (A + 3^(H+1) * Y) (H+1+s) := by
  exact window_class_invariant A X Y H s hXY

/-- The finite window projection is idempotent. -/
theorem worldtraceWindowClass_idempotent
    (X s : Nat) :
    worldtraceWindowClass (worldtraceWindowClass X s) s =
      worldtraceWindowClass X s := by
  unfold worldtraceWindowClass
  rw [Nat.mod_mod]

/-! ## Worldtrace window filtration -/

/-- **COARSE-AFTER-FINE ABSORPTION.**  Projecting first to a deeper visible
window and then to a shallower one is exactly the shallow projection. -/
theorem worldtraceWindowClass_nested
    (X s t : Nat) (hst : s ≤ t) :
    worldtraceWindowClass (worldtraceWindowClass X t) s =
      worldtraceWindowClass X s := by
  unfold worldtraceWindowClass
  have hdvd : 3^(s+1) ∣ 3^(t+1) :=
    Nat.pow_dvd_pow 3 (by omega)
  exact Nat.mod_mod_of_dvd X hdvd

/-- **FINE-AFTER-COARSE STABILITY.**  Once information has been truncated to
a shallow window, asking for any deeper window leaves it unchanged. -/
theorem worldtraceWindowClass_coarse_stable
    (X s t : Nat) (hst : s ≤ t) :
    worldtraceWindowClass (worldtraceWindowClass X s) t =
      worldtraceWindowClass X s := by
  unfold worldtraceWindowClass
  apply Nat.mod_eq_of_lt
  have hmod : X % 3^(s+1) < 3^(s+1) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hpow : 3^(s+1) ≤ 3^(t+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  exact Nat.lt_of_lt_of_le hmod hpow

/-- Equality at a deeper Worldtrace window implies equality at every coarser
visible window.  Finite read equivalence therefore forms a nested filtration. -/
theorem worldtraceWindowClass_eq_descends
    (X Y s t : Nat) (hst : s ≤ t)
    (hXY : worldtraceWindowClass X t =
      worldtraceWindowClass Y t) :
    worldtraceWindowClass X s =
      worldtraceWindowClass Y s := by
  calc
    worldtraceWindowClass X s =
        worldtraceWindowClass (worldtraceWindowClass X t) s :=
      (worldtraceWindowClass_nested X s t hst).symm
    _ = worldtraceWindowClass (worldtraceWindowClass Y t) s := by rw [hXY]
    _ = worldtraceWindowClass Y s :=
      worldtraceWindowClass_nested Y s t hst

/-- **WORLDTRACE FILTRATION CROWN.**  The visible quotient windows are
idempotent, nested projectors with exact absorption in both orders. -/
theorem worldtrace_window_filtration_crown :
    (∀ X s,
      worldtraceWindowClass (worldtraceWindowClass X s) s =
        worldtraceWindowClass X s)
    ∧
    (∀ X s t, s ≤ t →
      worldtraceWindowClass (worldtraceWindowClass X t) s =
        worldtraceWindowClass X s)
    ∧
    (∀ X s t, s ≤ t →
      worldtraceWindowClass (worldtraceWindowClass X s) t =
        worldtraceWindowClass X s) := by
  exact ⟨worldtraceWindowClass_idempotent,
    worldtraceWindowClass_nested,
    worldtraceWindowClass_coarse_stable⟩

/-- Quotient-window crown: every row read factors through one finite
idempotent projection. -/
theorem worldtrace_window_quotient_crown :
    (∀ A X H s,
      digit3 (A + 3^(H+1) * X) (H+1+s) =
        digit3
          (A + 3^(H+1) * worldtraceWindowClass X s)
          (H+1+s))
    ∧
    (∀ X s,
      worldtraceWindowClass (worldtraceWindowClass X s) s =
        worldtraceWindowClass X s) := by
  exact ⟨window_read_factors, worldtraceWindowClass_idempotent⟩

/-- **THE DUST WINDOW RECEIPT.**  The period law, the branch vanishing,
the clean row-(H+2) law, and the reduction handle. -/
theorem the_dust_window_receipt :
    (∀ r : Nat, (4:Nat)^r % 9 = 4^(r % 3) % 9) ∧
    (∀ t trunk H : Nat, 1 ≤ H → trunk % 3 = 1 → t < 3 →
      (t * GSTTowerFire.c H * 4^trunk) % 9 = t) ∧
    (∀ K H : Nat, 1 ≤ H → K < 3^(H+1) → K % 3 = 1 →
      digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
        + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3) ∧
    (∀ A X H s : Nat,
      digit3 (A + 3^(H+1) * X) (H+1+s)
        = digit3 (A + 3^(H+1) * (X % 3^(s+1))) (H+1+s)) :=
  ⟨four_pow_mod9, dust_branch_mod9, window_row_two_dust, window_reduce⟩

/-- **THE LEVEL-SIX RECEIPT.**  The worldtrace transformation assembled:
the binomial ladder, the quadratic and cubic blades, the polynomial
reads, the polynomial kill demo, the uniform engine, the thirty-two
fires, the kill chain, and the doubled survivor map. -/
theorem the_worldtrace_receipt :
    (∀ m : Nat, 4^(1+3*m) = 4 * 64^m) ∧
    (∀ m : Nat, ∃ R : Nat, (1+63)^m
      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561]) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 5
      = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7) ∧
    (digit3 (4^(1+3*28)) 5 = 2) ∧
    (∀ K r t : Nat, r < 729 → t < 3 →
      (digit3 (4^r) 7 + t) % 3 = 2 → K % 2187 = r + 729 * t →
      digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116) :=
  ⟨wt_rebase,
    fun m => one_add_pow_three_term 63 m,
    wt_quad_mod729, wt_cubic_mod6561,
    wt_row_five_read, wt_row_seven_read,
    wt_quad_fire_demo, fire_of_mod2187,
    dust_fire_row_seven, no22_of_cascade_six, cantorian_dust_mod_2187⟩

/-- **THE LEVEL-SEVEN RECEIPT.**  The worldtrace transformation, one
storey deeper: the five-term ladder, the quartic blade, the row-eight
read, the quartic kill demo, the uniform engine at level seven, the
sixty-four fires, the kill chain, and the re-doubled survivor map
(64 -> 128). -/
theorem the_worldtrace_receipt_seven :
    (∀ m : Nat, ∃ R : Nat, (1+63)^m
      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + Nat.choose m 3 * 63 * 63 * 63
        + Nat.choose m 4 * 63 * 63 * 63 * 63 + 63*63*63*63*63*R) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683]) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8) ∧
    (digit3 (4^(1+3*27)) 8 = 2) ∧
    (∀ K r t : Nat, r < 2187 → t < 3 →
      (digit3 (4^r) 8 + t) % 3 = 2 → K % 6561 = r + 2187 * t →
      digit3 (4^K) 8 = 2) ∧
    (∀ K : Nat, K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412 → digit3 (4^K) 8 = 2) ∧
    (∀ K : Nat, K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 6561 = 1 ∨ K % 6561 = 4 ∨ K % 6561 = 13 ∨ K % 6561 = 40 ∨ K % 6561 = 94 ∨ K % 6561 = 109 ∨ K % 6561 = 121 ∨ K % 6561 = 166 ∨ K % 6561 = 193 ∨ K % 6561 = 244 ∨ K % 6561 = 280 ∨ K % 6561 = 283 ∨ K % 6561 = 325 ∨ K % 6561 = 364 ∨ K % 6561 = 436 ∨ K % 6561 = 496 ∨ K % 6561 = 514 ∨ K % 6561 = 523 ∨ K % 6561 = 595 ∨ K % 6561 = 730 ∨ K % 6561 = 733 ∨ K % 6561 = 739 ∨ K % 6561 = 823 ∨ K % 6561 = 838 ∨ K % 6561 = 850 ∨ K % 6561 = 922 ∨ K % 6561 = 928 ∨ K % 6561 = 973 ∨ K % 6561 = 1003 ∨ K % 6561 = 1009 ∨ K % 6561 = 1093 ∨ K % 6561 = 1144 ∨ K % 6561 = 1165 ∨ K % 6561 = 1171 ∨ K % 6561 = 1225 ∨ K % 6561 = 1228 ∨ K % 6561 = 1243 ∨ K % 6561 = 1252 ∨ K % 6561 = 1387 ∨ K % 6561 = 1468 ∨ K % 6561 = 1540 ∨ K % 6561 = 1624 ∨ K % 6561 = 1657 ∨ K % 6561 = 1732 ∨ K % 6561 = 1741 ∨ K % 6561 = 1783 ∨ K % 6561 = 1873 ∨ K % 6561 = 1900 ∨ K % 6561 = 1957 ∨ K % 6561 = 2038 ∨ K % 6561 = 2053 ∨ K % 6561 = 2116 ∨ K % 6561 = 2188 ∨ K % 6561 = 2191 ∨ K % 6561 = 2269 ∨ K % 6561 = 2353 ∨ K % 6561 = 2434 ∨ K % 6561 = 2467 ∨ K % 6561 = 2470 ∨ K % 6561 = 2512 ∨ K % 6561 = 2551 ∨ K % 6561 = 2623 ∨ K % 6561 = 2683 ∨ K % 6561 = 2767 ∨ K % 6561 = 2782 ∨ K % 6561 = 2917 ∨ K % 6561 = 2920 ∨ K % 6561 = 2944 ∨ K % 6561 = 3115 ∨ K % 6561 = 3163 ∨ K % 6561 = 3190 ∨ K % 6561 = 3196 ∨ K % 6561 = 3280 ∨ K % 6561 = 3331 ∨ K % 6561 = 3352 ∨ K % 6561 = 3412 ∨ K % 6561 = 3415 ∨ K % 6561 = 3433 ∨ K % 6561 = 3568 ∨ K % 6561 = 3658 ∨ K % 6561 = 3673 ∨ K % 6561 = 3685 ∨ K % 6561 = 3727 ∨ K % 6561 = 3844 ∨ K % 6561 = 3919 ∨ K % 6561 = 4060 ∨ K % 6561 = 4144 ∨ K % 6561 = 4162 ∨ K % 6561 = 4225 ∨ K % 6561 = 4297 ∨ K % 6561 = 4387 ∨ K % 6561 = 4414 ∨ K % 6561 = 4456 ∨ K % 6561 = 4468 ∨ K % 6561 = 4483 ∨ K % 6561 = 4495 ∨ K % 6561 = 4567 ∨ K % 6561 = 4618 ∨ K % 6561 = 4621 ∨ K % 6561 = 4888 ∨ K % 6561 = 4897 ∨ K % 6561 = 4954 ∨ K % 6561 = 5113 ∨ K % 6561 = 5131 ∨ K % 6561 = 5197 ∨ K % 6561 = 5212 ∨ K % 6561 = 5224 ∨ K % 6561 = 5296 ∨ K % 6561 = 5347 ∨ K % 6561 = 5350 ∨ K % 6561 = 5545 ∨ K % 6561 = 5617 ∨ K % 6561 = 5620 ∨ K % 6561 = 5626 ∨ K % 6561 = 5755 ∨ K % 6561 = 5761 ∨ K % 6561 = 5842 ∨ K % 6561 = 5845 ∨ K % 6561 = 5860 ∨ K % 6561 = 5872 ∨ K % 6561 = 5998 ∨ K % 6561 = 6115 ∨ K % 6561 = 6157 ∨ K % 6561 = 6274 ∨ K % 6561 = 6349 ∨ K % 6561 = 6427 ∨ K % 6561 = 6484 ∨ K % 6561 = 6490) :=
  ⟨fun m => one_add_pow_five_term 63 m,
    wt_quartic_mod19683, wt_row_eight_read, wt_quartic_fire_demo,
    fire_of_mod6561, dust_fire_row_eight, no22_of_cascade_seven,
    cantarian_dust_mod_6561⟩

#print axioms wt_choose_one
#print axioms one_add_pow_three_term
#print axioms one_add_pow_four_term
#print axioms wt_rebase
#print axioms wt_quad_mod729
#print axioms wt_cubic_mod6561
#print axioms wt_row_five_read
#print axioms wt_row_seven_read
#print axioms wt_quad_fire_demo
#print axioms fire_of_mod2187
#print axioms dust_fire_row_seven
#print axioms no22_of_cascade_six
#print axioms cantorian_dust_mod_2187
#print axioms the_worldtrace_receipt
#print axioms one_add_pow_five_term
#print axioms wt_quartic_mod19683
#print axioms wt_row_eight_read
#print axioms wt_quartic_fire_demo
#print axioms fire_of_mod6561
#print axioms dust_fire_row_eight
#print axioms no22_of_cascade_seven
#print axioms cantarian_dust_mod_6561
#print axioms the_worldtrace_receipt_seven

#print axioms pair_read_formula
#print axioms pair_read_fire
#print axioms no22_of_pair_read
#print axioms the_pair_read_receipt
#print axioms pair_residue_mod27
#print axioms digit3_row_two_of_residue
#print axioms pair_read_fire_general
#print axioms no22_of_pair_read_general
#print axioms pair_read_fire_demo_two
#print axioms pair_read_fire_demo_three
#print axioms the_general_fire_receipt
#print axioms top_split
#print axioms window_congr
#print axioms window_row_two
#print axioms the_descent_engine_receipt
#print axioms four_pow_mod9
#print axioms dust_branch_mod9
#print axioms window_row_two_dust
#print axioms window_reduce
#print axioms window_read_factors
#print axioms window_class_invariant
#print axioms worldtraceWindowClass_idempotent
#print axioms worldtrace_window_quotient_crown
#print axioms worldtraceWindowClass_nested
#print axioms worldtraceWindowClass_coarse_stable
#print axioms worldtraceWindowClass_eq_descends
#print axioms worldtrace_window_filtration_crown
#print axioms the_dust_window_receipt

end GSTWorldtraceArithmetic
