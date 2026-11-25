import Mathlib
import MonolithGate.ErdosTernary2
import MonolithGate.GSTTailFProof
import MonolithGate.GSTTailFFourthDimension
import MonolithGate.GSTInfiniteFourPowerNavigation
import MonolithGate.GSTGraphV2OmegaWaveLaw
import MonolithGate.GSTTheAct
import MonolithGate.GSTClimbTruthValue
import MonolithGate.GSTDiagonalRead
import MonolithGate.GSTClimbInfiniteFamily
import MonolithGate.GSTTheActConstruction
import MonolithGate.GSTWorldtraceArithmetic
import MonolithGate.WorldtraceLevelNine406

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# THE FINAL ASSEMBLY (S085 r34v2) — the complete composition

BOSS's order: USE MY MATHS — the entire kill engine, vendored and composed.
This module is the campaign's terminal composition: the vendored engine's
eight chambers plus the ninth cascade level, joined into one assembly whose
every crown route is UNCONDITIONAL except the single named residual.

THE COMPOSITION LAW: the vendored engine's hypothesis slots took the
boundary objects as hypotheses; the MonolithGate universe carries
`erdos_even_conjecture_iff_tailF` and `erdos_ternary_2_conjecture_odd` as
PROVEN THEOREMS — so every slot is here discharged by the theorems
themselves.

THE TRUST LAW (r34v2, after the first-exposure verdict): this file
references by name only receipt-verified chamber theorems and this round's
own wrappers; the total cascade routes exclusively through the level-
generic uniform engine and this round's ladder wrappers.

THE HONEST MAP this assembly certifies:
- GREEN AND UNCONDITIONAL: the identity (the act ↔ tailF, both ways),
  the full-statement equivalence, the triage, the NEW LAW cantorian_is_dust
  (a Cantorian power IS window-clean dust), the front law, the NINE-level
  cascade (255 dead classes), the class-one verdict at level nine (die or
  live in the 256 survivors), the general pair-read kill, the unbounded
  deep-third-wave climb family, the below-eight witness.
- THE ONE NAMED RESIDUAL: `erdos_406_the_last_hypothesis` — no exponent
  from eight onward is a Cantorian power. Exactness certified: it is
  equivalent to the act (the boss's own green iff), every crown route
  consumes it (or an equivalent) as its single input. This IS the
  remaining mathematical content of Erdős #406 — named in its sharpest
  machine form, everything else unconditional.
-/

open GSTCanonicalSevenAxisBridge (digit3 carry4)
open GSTU2DEventTransport (HappyCell)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTClimbInfiniteFamily (wave3_deep_member climb_member_of_wave3_deep)
open GSTClimbInfiniteFamily (wave3_deep_unbounded cantorian_survivors_below_eight)
open GSTDiagonalRead (WindowCleanDust every_exponent_fires valuation_decomp)
open GSTDiagonalRead (diagonal_window_law)
open GSTWorldtraceArithmetic (no22_of_pair_read_general)

/-! ## §1 The unconditional identity -/

/-- **THE IDENTITY, UNCONDITIONAL.** -/
theorem the_act_iff_tailF_unconditional :
    GSTTheAct.the_act ↔
      GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF erdos_even_conjecture_iff_tailF

/-! ## §2 The full-statement equivalence -/

theorem the_act_iff_full_erdos_unconditional :
    GSTTheAct.the_act ↔
      (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :=
  GSTTheAct.the_act_iff_full_erdos erdos_ternary_2_conjecture_odd

theorem full_erdos_of_the_act_unconditional (h : GSTTheAct.the_act) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTTheAct.full_erdos_of_the_act erdos_ternary_2_conjecture_odd h

/-! ## §3 The crown routes -/

/-- **CROWN ROUTE 1 — THE ACT.** -/
theorem erdos_ternary_2_universal_of_the_act
    (h : GSTTheAct.the_act) (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  full_erdos_of_the_act_unconditional h n hn

/-- **CROWN ROUTE 2 — THE CORE.** -/
theorem erdos_ternary_2_universal_of_no_cantorian
    (h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_the_act
    (GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mpr h) n hn

/-- **CROWN ROUTE 3 — THE DUST.** -/
theorem erdos_ternary_2_universal_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_the_act
    (GSTDiagonalRead.the_act_of_dust_empty h) n hn

/-- **CROWN ROUTE 4 — THE CLIMB.** -/
theorem erdos_ternary_2_universal_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_the_act
    (GSTTheAct.climb_gives_the_act erdos_even_conjecture_iff_tailF
      hClimb) n hn

/-- **CROWN ROUTE 5 — THE TWO PRIMITIVES.** -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hRow : GSTTailFFourthDimension.tailF_row_primitive)
    (hTower : GSTTailFFourthDimension.tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  GSTTailFFourthDimension.erdos_ternary_2_universal_of_row_and_tower
    hRow hTower n hn

/-! ## §4 The socket comparison — a NEW LAW -/

/-- **THE NEW LAW: A CANTORIAN POWER IS WINDOW-CLEAN DUST.** -/
theorem cantorian_is_dust (K : Nat) (hK : 8 ≤ K)
    (hC : CantorianPower K) : WindowCleanDust K := by
  obtain ⟨v, u, hKu, hu3⟩ := valuation_decomp K (by omega)
  have hu1 : u % 3 = 1 := by
    rcases (by omega : u % 3 = 1 ∨ u % 3 = 2) with h1 | h2
    · exact h1
    · exfalso
      have hfront : digit3 (4^K) (v+1) = 2 := by
        rw [hKu, GSTTheAct.front_law v u, h2]
      exact hC (v+1) (by omega) hfront
  refine ⟨v, u, hKu, hu1, ?_⟩
  intro j hjv h2
  have hwin := diagonal_window_law v u j hjv
  rw [hKu] at hwin
  rw [h2] at hwin
  exact hC (v+1+j) (by omega) hwin

/-! ## §5 The named residual -/

/-- **THE LAST HYPOTHESIS, NAMED.** -/
def erdos_406_the_last_hypothesis : Prop :=
  ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K

theorem the_last_hypothesis_iff_the_act :
    erdos_406_the_last_hypothesis ↔ GSTTheAct.the_act :=
  GSTClimbInfiniteFamily.the_act_iff_no_cantorian

/-- **THE SOCKET COMPARISON.** -/
theorem no_cantorian_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    erdos_406_the_last_hypothesis := by
  intro hKex
  obtain ⟨K, hK, hC⟩ := hKex
  exact h K hK (cantorian_is_dust K hK hC)

/-- **THE CROWN FROM THE LAST HYPOTHESIS.** -/
theorem erdos_ternary_2_universal_of_last_hypothesis
    (h : erdos_406_the_last_hypothesis)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_no_cantorian h n hn

/-! ## §6 The total cascade — nine levels, one statement -/
/-- **THE TOTAL CASCADE.**  Every exponent whose class hits any of the
nine ladder levels' 255 dead classes owns its digit two — one statement,
every uniform kill this round's ladder wrappers provide (levels two
through nine, each through the engine's level-generic feedback law).
Two-method computational certificate. -/
theorem no22_of_cascade_total (K : Nat)
    (h : K % 9 = 7 ∨ K % 27 = 19 ∨ K % 27 = 22 ∨ K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨ K % 81 = 67 ∨ K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨ K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨ K % 243 = 202 ∨ K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685 ∨ K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 ∨ K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412 ∨ K % 19683 = 40 ∨ K % 19683 = 94 ∨ K % 19683 = 109 ∨ K % 19683 = 193 ∨ K % 19683 = 244 ∨ K % 19683 = 283 ∨ K % 19683 = 325 ∨ K % 19683 = 733 ∨ K % 19683 = 928 ∨ K % 19683 = 1009 ∨ K % 19683 = 1144 ∨ K % 19683 = 1171 ∨ K % 19683 = 1252 ∨ K % 19683 = 1387 ∨ K % 19683 = 1540 ∨ K % 19683 = 1957 ∨ K % 19683 = 2434 ∨ K % 19683 = 2470 ∨ K % 19683 = 2512 ∨ K % 19683 = 2767 ∨ K % 19683 = 2920 ∨ K % 19683 = 3115 ∨ K % 19683 = 3196 ∨ K % 19683 = 3331 ∨ K % 19683 = 3727 ∨ K % 19683 = 4144 ∨ K % 19683 = 4162 ∨ K % 19683 = 4297 ∨ K % 19683 = 4387 ∨ K % 19683 = 4495 ∨ K % 19683 = 4621 ∨ K % 19683 = 4897 ∨ K % 19683 = 4954 ∨ K % 19683 = 5197 ∨ K % 19683 = 5296 ∨ K % 19683 = 5617 ∨ K % 19683 = 5842 ∨ K % 19683 = 5998 ∨ K % 19683 = 6157 ∨ K % 19683 = 6349 ∨ K % 19683 = 6484 ∨ K % 19683 = 6574 ∨ K % 19683 = 6682 ∨ K % 19683 = 6841 ∨ K % 19683 = 6925 ∨ K % 19683 = 6997 ∨ K % 19683 = 7084 ∨ K % 19683 = 7156 ∨ K % 19683 = 7291 ∨ K % 19683 = 7384 ∨ K % 19683 = 7483 ∨ K % 19683 = 7564 ∨ K % 19683 = 7786 ∨ K % 19683 = 7804 ∨ K % 19683 = 8029 ∨ K % 19683 = 8185 ∨ K % 19683 = 8344 ∨ K % 19683 = 9028 ∨ K % 19683 = 9112 ∨ K % 19683 = 9184 ∨ K % 19683 = 9343 ∨ K % 19683 = 9478 ∨ K % 19683 = 9724 ∨ K % 19683 = 9751 ∨ K % 19683 = 9973 ∨ K % 19683 = 10234 ∨ K % 19683 = 10246 ∨ K % 19683 = 11449 ∨ K % 19683 = 11674 ∨ K % 19683 = 11773 ∨ K % 19683 = 11785 ∨ K % 19683 = 11908 ∨ K % 19683 = 11911 ∨ K % 19683 = 12421 ∨ K % 19683 = 12433 ∨ K % 19683 = 12676 ∨ K % 19683 = 12835 ∨ K % 19683 = 12988 ∨ K % 19683 = 13051 ∨ K % 19683 = 13123 ∨ K % 19683 = 13126 ∨ K % 19683 = 13288 ∨ K % 19683 = 13618 ∨ K % 19683 = 13636 ∨ K % 19683 = 13861 ∨ K % 19683 = 13960 ∨ K % 19683 = 13972 ∨ K % 19683 = 14095 ∨ K % 19683 = 14215 ∨ K % 19683 = 14287 ∨ K % 19683 = 14350 ∨ K % 19683 = 14779 ∨ K % 19683 = 14854 ∨ K % 19683 = 14863 ∨ K % 19683 = 14995 ∨ K % 19683 = 15022 ∨ K % 19683 = 15160 ∨ K % 19683 = 15175 ∨ K % 19683 = 15238 ∨ K % 19683 = 15310 ∨ K % 19683 = 15313 ∨ K % 19683 = 15391 ∨ K % 19683 = 15475 ∨ K % 19683 = 15805 ∨ K % 19683 = 16066 ∨ K % 19683 = 16402 ∨ K % 19683 = 16474 ∨ K % 19683 = 16537 ∨ K % 19683 = 16555 ∨ K % 19683 = 16690 ∨ K % 19683 = 16780 ∨ K % 19683 = 16966 ∨ K % 19683 = 17041 ∨ K % 19683 = 17182 ∨ K % 19683 = 17347 ∨ K % 19683 = 17536 ∨ K % 19683 = 17578 ∨ K % 19683 = 17590 ∨ K % 19683 = 17605 ∨ K % 19683 = 17689 ∨ K % 19683 = 17740 ∨ K % 19683 = 18253 ∨ K % 19683 = 18667 ∨ K % 19683 = 18742 ∨ K % 19683 = 18748 ∨ K % 19683 = 18877 ∨ K % 19683 = 18883 ∨ K % 19683 = 18967) :
    noTernaryTwo (4^K) = false := by
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127 | h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159 | h160 | h161 | h162 | h163 | h164 | h165 | h166 | h167 | h168 | h169 | h170 | h171 | h172 | h173 | h174 | h175 | h176 | h177 | h178 | h179 | h180 | h181 | h182 | h183 | h184 | h185 | h186 | h187 | h188 | h189 | h190 | h191 | h192 | h193 | h194 | h195 | h196 | h197 | h198 | h199 | h200 | h201 | h202 | h203 | h204 | h205 | h206 | h207 | h208 | h209 | h210 | h211 | h212 | h213 | h214 | h215 | h216 | h217 | h218 | h219 | h220 | h221 | h222 | h223 | h224 | h225 | h226 | h227 | h228 | h229 | h230 | h231 | h232 | h233 | h234 | h235 | h236 | h237 | h238 | h239 | h240 | h241 | h242 | h243 | h244 | h245 | h246 | h247 | h248 | h249 | h250 | h251 | h252 | h253 | h254
  · exact no22_of_digit_two K 2 (ladder_fire_mod9 K 1 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 3 (ladder_fire_mod27 K 1 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 3 (ladder_fire_mod27 K 4 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 4 (ladder_fire_mod81 K 1 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 4 (ladder_fire_mod81 K 4 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 4 (ladder_fire_mod81 K 10 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 4 (ladder_fire_mod81 K 13 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 4 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 10 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 31 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 37 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 1 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 13 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 28 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 5 (ladder_fire_mod243 K 40 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 31 0 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 37 0 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 172 0 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 10 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 13 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 28 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 94 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 109 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 166 1 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 1 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 4 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 40 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 82 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 121 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 193 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 6 (ladder_fire_mod729 K 199 2 (by decide) (by decide)
      (by decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 10 0 (by decide) (by decide)
      (by rw [show (10:Nat) = 1 + 3*3 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 28 0 (by decide) (by decide)
      (by rw [show (28:Nat) = 1 + 3*9 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 199 0 (by decide) (by decide)
      (by rw [show (199:Nat) = 1 + 3*66 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 274 0 (by decide) (by decide)
      (by rw [show (274:Nat) = 1 + 3*91 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 415 0 (by decide) (by decide)
      (by rw [show (415:Nat) = 1 + 3*138 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 442 0 (by decide) (by decide)
      (by rw [show (442:Nat) = 1 + 3*147 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 499 0 (by decide) (by decide)
      (by rw [show (499:Nat) = 1 + 3*166 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 517 0 (by decide) (by decide)
      (by rw [show (517:Nat) = 1 + 3*172 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 652 0 (by decide) (by decide)
      (by rw [show (652:Nat) = 1 + 3*217 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 658 0 (by decide) (by decide)
      (by rw [show (658:Nat) = 1 + 3*219 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 40 1 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 82 1 (by decide) (by decide)
      (by rw [show (82:Nat) = 1 + 3*27 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 166 1 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 283 1 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 325 1 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 580 1 (by decide) (by decide)
      (by rw [show (580:Nat) = 1 + 3*193 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 595 1 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 94 2 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 109 2 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 121 2 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 193 2 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 244 2 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 247 2 (by decide) (by decide)
      (by rw [show (247:Nat) = 1 + 3*82 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 280 2 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 364 2 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 436 2 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 514 2 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 7 (ladder_fire_mod2187 K 523 2 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide, GSTWorldtraceArithmetic.wt_row_seven_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 82 0 (by decide) (by decide)
      (by rw [show (82:Nat) = 1 + 3*27 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 247 0 (by decide) (by decide)
      (by rw [show (247:Nat) = 1 + 3*82 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 580 0 (by decide) (by decide)
      (by rw [show (580:Nat) = 1 + 3*193 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 757 0 (by decide) (by decide)
      (by rw [show (757:Nat) = 1 + 3*252 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 976 0 (by decide) (by decide)
      (by rw [show (976:Nat) = 1 + 3*325 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1246 0 (by decide) (by decide)
      (by rw [show (1246:Nat) = 1 + 3*415 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1381 0 (by decide) (by decide)
      (by rw [show (1381:Nat) = 1 + 3*460 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1471 0 (by decide) (by decide)
      (by rw [show (1471:Nat) = 1 + 3*490 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1486 0 (by decide) (by decide)
      (by rw [show (1486:Nat) = 1 + 3*495 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1498 0 (by decide) (by decide)
      (by rw [show (1498:Nat) = 1 + 3*499 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1975 0 (by decide) (by decide)
      (by rw [show (1975:Nat) = 1 + 3*658 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 2110 0 (by decide) (by decide)
      (by rw [show (2110:Nat) = 1 + 3*703 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 40 1 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 94 1 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 109 1 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 121 1 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 193 1 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 244 1 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 514 1 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 523 1 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 739 1 (by decide) (by decide)
      (by rw [show (739:Nat) = 1 + 3*246 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 823 1 (by decide) (by decide)
      (by rw [show (823:Nat) = 1 + 3*274 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 838 1 (by decide) (by decide)
      (by rw [show (838:Nat) = 1 + 3*279 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 850 1 (by decide) (by decide)
      (by rw [show (850:Nat) = 1 + 3*283 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 922 1 (by decide) (by decide)
      (by rw [show (922:Nat) = 1 + 3*307 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 973 1 (by decide) (by decide)
      (by rw [show (973:Nat) = 1 + 3*324 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1171 1 (by decide) (by decide)
      (by rw [show (1171:Nat) = 1 + 3*390 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1243 1 (by decide) (by decide)
      (by rw [show (1243:Nat) = 1 + 3*414 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1252 1 (by decide) (by decide)
      (by rw [show (1252:Nat) = 1 + 3*417 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1387 1 (by decide) (by decide)
      (by rw [show (1387:Nat) = 1 + 3*462 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1468 1 (by decide) (by decide)
      (by rw [show (1468:Nat) = 1 + 3*489 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1624 1 (by decide) (by decide)
      (by rw [show (1624:Nat) = 1 + 3*541 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1741 1 (by decide) (by decide)
      (by rw [show (1741:Nat) = 1 + 3*580 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1783 1 (by decide) (by decide)
      (by rw [show (1783:Nat) = 1 + 3*594 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1900 1 (by decide) (by decide)
      (by rw [show (1900:Nat) = 1 + 3*633 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 2053 1 (by decide) (by decide)
      (by rw [show (2053:Nat) = 1 + 3*684 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 2116 1 (by decide) (by decide)
      (by rw [show (2116:Nat) = 1 + 3*705 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 166 2 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 280 2 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 283 2 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 325 2 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 364 2 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 436 2 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 595 2 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 730 2 (by decide) (by decide)
      (by rw [show (730:Nat) = 1 + 3*243 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 733 2 (by decide) (by decide)
      (by rw [show (733:Nat) = 1 + 3*244 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 928 2 (by decide) (by decide)
      (by rw [show (928:Nat) = 1 + 3*309 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1003 2 (by decide) (by decide)
      (by rw [show (1003:Nat) = 1 + 3*334 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1009 2 (by decide) (by decide)
      (by rw [show (1009:Nat) = 1 + 3*336 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1093 2 (by decide) (by decide)
      (by rw [show (1093:Nat) = 1 + 3*364 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1144 2 (by decide) (by decide)
      (by rw [show (1144:Nat) = 1 + 3*381 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1165 2 (by decide) (by decide)
      (by rw [show (1165:Nat) = 1 + 3*388 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1225 2 (by decide) (by decide)
      (by rw [show (1225:Nat) = 1 + 3*408 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1228 2 (by decide) (by decide)
      (by rw [show (1228:Nat) = 1 + 3*409 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1540 2 (by decide) (by decide)
      (by rw [show (1540:Nat) = 1 + 3*513 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1657 2 (by decide) (by decide)
      (by rw [show (1657:Nat) = 1 + 3*552 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1732 2 (by decide) (by decide)
      (by rw [show (1732:Nat) = 1 + 3*577 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1873 2 (by decide) (by decide)
      (by rw [show (1873:Nat) = 1 + 3*624 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 1957 2 (by decide) (by decide)
      (by rw [show (1957:Nat) = 1 + 3*652 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 8 (ladder_fire_mod6561 K 2038 2 (by decide) (by decide)
      (by rw [show (2038:Nat) = 1 + 3*679 from by decide, GSTWorldtraceArithmetic.wt_row_eight_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 40 0 (by decide) (by decide)
      (by rw [show (40:Nat) = 1 + 3*13 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 94 0 (by decide) (by decide)
      (by rw [show (94:Nat) = 1 + 3*31 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 109 0 (by decide) (by decide)
      (by rw [show (109:Nat) = 1 + 3*36 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 193 0 (by decide) (by decide)
      (by rw [show (193:Nat) = 1 + 3*64 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 244 0 (by decide) (by decide)
      (by rw [show (244:Nat) = 1 + 3*81 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 283 0 (by decide) (by decide)
      (by rw [show (283:Nat) = 1 + 3*94 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 325 0 (by decide) (by decide)
      (by rw [show (325:Nat) = 1 + 3*108 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 733 0 (by decide) (by decide)
      (by rw [show (733:Nat) = 1 + 3*244 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 928 0 (by decide) (by decide)
      (by rw [show (928:Nat) = 1 + 3*309 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1009 0 (by decide) (by decide)
      (by rw [show (1009:Nat) = 1 + 3*336 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1144 0 (by decide) (by decide)
      (by rw [show (1144:Nat) = 1 + 3*381 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1171 0 (by decide) (by decide)
      (by rw [show (1171:Nat) = 1 + 3*390 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1252 0 (by decide) (by decide)
      (by rw [show (1252:Nat) = 1 + 3*417 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1387 0 (by decide) (by decide)
      (by rw [show (1387:Nat) = 1 + 3*462 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1540 0 (by decide) (by decide)
      (by rw [show (1540:Nat) = 1 + 3*513 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1957 0 (by decide) (by decide)
      (by rw [show (1957:Nat) = 1 + 3*652 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2434 0 (by decide) (by decide)
      (by rw [show (2434:Nat) = 1 + 3*811 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2470 0 (by decide) (by decide)
      (by rw [show (2470:Nat) = 1 + 3*823 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2512 0 (by decide) (by decide)
      (by rw [show (2512:Nat) = 1 + 3*837 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2767 0 (by decide) (by decide)
      (by rw [show (2767:Nat) = 1 + 3*922 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2920 0 (by decide) (by decide)
      (by rw [show (2920:Nat) = 1 + 3*973 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3115 0 (by decide) (by decide)
      (by rw [show (3115:Nat) = 1 + 3*1038 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3196 0 (by decide) (by decide)
      (by rw [show (3196:Nat) = 1 + 3*1065 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3331 0 (by decide) (by decide)
      (by rw [show (3331:Nat) = 1 + 3*1110 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3727 0 (by decide) (by decide)
      (by rw [show (3727:Nat) = 1 + 3*1242 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4144 0 (by decide) (by decide)
      (by rw [show (4144:Nat) = 1 + 3*1381 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4162 0 (by decide) (by decide)
      (by rw [show (4162:Nat) = 1 + 3*1387 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4297 0 (by decide) (by decide)
      (by rw [show (4297:Nat) = 1 + 3*1432 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4387 0 (by decide) (by decide)
      (by rw [show (4387:Nat) = 1 + 3*1462 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4495 0 (by decide) (by decide)
      (by rw [show (4495:Nat) = 1 + 3*1498 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4621 0 (by decide) (by decide)
      (by rw [show (4621:Nat) = 1 + 3*1540 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4897 0 (by decide) (by decide)
      (by rw [show (4897:Nat) = 1 + 3*1632 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4954 0 (by decide) (by decide)
      (by rw [show (4954:Nat) = 1 + 3*1651 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5197 0 (by decide) (by decide)
      (by rw [show (5197:Nat) = 1 + 3*1732 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5296 0 (by decide) (by decide)
      (by rw [show (5296:Nat) = 1 + 3*1765 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5617 0 (by decide) (by decide)
      (by rw [show (5617:Nat) = 1 + 3*1872 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5842 0 (by decide) (by decide)
      (by rw [show (5842:Nat) = 1 + 3*1947 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5998 0 (by decide) (by decide)
      (by rw [show (5998:Nat) = 1 + 3*1999 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6157 0 (by decide) (by decide)
      (by rw [show (6157:Nat) = 1 + 3*2052 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6349 0 (by decide) (by decide)
      (by rw [show (6349:Nat) = 1 + 3*2116 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6484 0 (by decide) (by decide)
      (by rw [show (6484:Nat) = 1 + 3*2161 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 13 1 (by decide) (by decide)
      (by rw [show (13:Nat) = 1 + 3*4 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 121 1 (by decide) (by decide)
      (by rw [show (121:Nat) = 1 + 3*40 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 280 1 (by decide) (by decide)
      (by rw [show (280:Nat) = 1 + 3*93 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 364 1 (by decide) (by decide)
      (by rw [show (364:Nat) = 1 + 3*121 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 436 1 (by decide) (by decide)
      (by rw [show (436:Nat) = 1 + 3*145 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 523 1 (by decide) (by decide)
      (by rw [show (523:Nat) = 1 + 3*174 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 595 1 (by decide) (by decide)
      (by rw [show (595:Nat) = 1 + 3*198 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 730 1 (by decide) (by decide)
      (by rw [show (730:Nat) = 1 + 3*243 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 823 1 (by decide) (by decide)
      (by rw [show (823:Nat) = 1 + 3*274 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 922 1 (by decide) (by decide)
      (by rw [show (922:Nat) = 1 + 3*307 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1003 1 (by decide) (by decide)
      (by rw [show (1003:Nat) = 1 + 3*334 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1225 1 (by decide) (by decide)
      (by rw [show (1225:Nat) = 1 + 3*408 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1243 1 (by decide) (by decide)
      (by rw [show (1243:Nat) = 1 + 3*414 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1468 1 (by decide) (by decide)
      (by rw [show (1468:Nat) = 1 + 3*489 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1624 1 (by decide) (by decide)
      (by rw [show (1624:Nat) = 1 + 3*541 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1783 1 (by decide) (by decide)
      (by rw [show (1783:Nat) = 1 + 3*594 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2467 1 (by decide) (by decide)
      (by rw [show (2467:Nat) = 1 + 3*822 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2551 1 (by decide) (by decide)
      (by rw [show (2551:Nat) = 1 + 3*850 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2623 1 (by decide) (by decide)
      (by rw [show (2623:Nat) = 1 + 3*874 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2782 1 (by decide) (by decide)
      (by rw [show (2782:Nat) = 1 + 3*927 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2917 1 (by decide) (by decide)
      (by rw [show (2917:Nat) = 1 + 3*972 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3163 1 (by decide) (by decide)
      (by rw [show (3163:Nat) = 1 + 3*1054 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3190 1 (by decide) (by decide)
      (by rw [show (3190:Nat) = 1 + 3*1063 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3412 1 (by decide) (by decide)
      (by rw [show (3412:Nat) = 1 + 3*1137 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3673 1 (by decide) (by decide)
      (by rw [show (3673:Nat) = 1 + 3*1224 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3685 1 (by decide) (by decide)
      (by rw [show (3685:Nat) = 1 + 3*1228 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4888 1 (by decide) (by decide)
      (by rw [show (4888:Nat) = 1 + 3*1629 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5113 1 (by decide) (by decide)
      (by rw [show (5113:Nat) = 1 + 3*1704 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5212 1 (by decide) (by decide)
      (by rw [show (5212:Nat) = 1 + 3*1737 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5224 1 (by decide) (by decide)
      (by rw [show (5224:Nat) = 1 + 3*1741 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5347 1 (by decide) (by decide)
      (by rw [show (5347:Nat) = 1 + 3*1782 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5350 1 (by decide) (by decide)
      (by rw [show (5350:Nat) = 1 + 3*1783 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5860 1 (by decide) (by decide)
      (by rw [show (5860:Nat) = 1 + 3*1953 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5872 1 (by decide) (by decide)
      (by rw [show (5872:Nat) = 1 + 3*1957 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6115 1 (by decide) (by decide)
      (by rw [show (6115:Nat) = 1 + 3*2038 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6274 1 (by decide) (by decide)
      (by rw [show (6274:Nat) = 1 + 3*2091 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6427 1 (by decide) (by decide)
      (by rw [show (6427:Nat) = 1 + 3*2142 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 6490 1 (by decide) (by decide)
      (by rw [show (6490:Nat) = 1 + 3*2163 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1 2 (by decide) (by decide)
      (by rw [show (1:Nat) = 1 + 3*0 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4 2 (by decide) (by decide)
      (by rw [show (4:Nat) = 1 + 3*1 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 166 2 (by decide) (by decide)
      (by rw [show (166:Nat) = 1 + 3*55 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 496 2 (by decide) (by decide)
      (by rw [show (496:Nat) = 1 + 3*165 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 514 2 (by decide) (by decide)
      (by rw [show (514:Nat) = 1 + 3*171 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 739 2 (by decide) (by decide)
      (by rw [show (739:Nat) = 1 + 3*246 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 838 2 (by decide) (by decide)
      (by rw [show (838:Nat) = 1 + 3*279 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 850 2 (by decide) (by decide)
      (by rw [show (850:Nat) = 1 + 3*283 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 973 2 (by decide) (by decide)
      (by rw [show (973:Nat) = 1 + 3*324 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1093 2 (by decide) (by decide)
      (by rw [show (1093:Nat) = 1 + 3*364 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1165 2 (by decide) (by decide)
      (by rw [show (1165:Nat) = 1 + 3*388 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1228 2 (by decide) (by decide)
      (by rw [show (1228:Nat) = 1 + 3*409 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1657 2 (by decide) (by decide)
      (by rw [show (1657:Nat) = 1 + 3*552 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1732 2 (by decide) (by decide)
      (by rw [show (1732:Nat) = 1 + 3*577 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1741 2 (by decide) (by decide)
      (by rw [show (1741:Nat) = 1 + 3*580 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1873 2 (by decide) (by decide)
      (by rw [show (1873:Nat) = 1 + 3*624 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 1900 2 (by decide) (by decide)
      (by rw [show (1900:Nat) = 1 + 3*633 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2038 2 (by decide) (by decide)
      (by rw [show (2038:Nat) = 1 + 3*679 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2053 2 (by decide) (by decide)
      (by rw [show (2053:Nat) = 1 + 3*684 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2116 2 (by decide) (by decide)
      (by rw [show (2116:Nat) = 1 + 3*705 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2188 2 (by decide) (by decide)
      (by rw [show (2188:Nat) = 1 + 3*729 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2191 2 (by decide) (by decide)
      (by rw [show (2191:Nat) = 1 + 3*730 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2269 2 (by decide) (by decide)
      (by rw [show (2269:Nat) = 1 + 3*756 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2353 2 (by decide) (by decide)
      (by rw [show (2353:Nat) = 1 + 3*784 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2683 2 (by decide) (by decide)
      (by rw [show (2683:Nat) = 1 + 3*894 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 2944 2 (by decide) (by decide)
      (by rw [show (2944:Nat) = 1 + 3*981 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3280 2 (by decide) (by decide)
      (by rw [show (3280:Nat) = 1 + 3*1093 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3352 2 (by decide) (by decide)
      (by rw [show (3352:Nat) = 1 + 3*1117 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3415 2 (by decide) (by decide)
      (by rw [show (3415:Nat) = 1 + 3*1138 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3433 2 (by decide) (by decide)
      (by rw [show (3433:Nat) = 1 + 3*1144 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3568 2 (by decide) (by decide)
      (by rw [show (3568:Nat) = 1 + 3*1189 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3658 2 (by decide) (by decide)
      (by rw [show (3658:Nat) = 1 + 3*1219 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3844 2 (by decide) (by decide)
      (by rw [show (3844:Nat) = 1 + 3*1281 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 3919 2 (by decide) (by decide)
      (by rw [show (3919:Nat) = 1 + 3*1306 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4060 2 (by decide) (by decide)
      (by rw [show (4060:Nat) = 1 + 3*1353 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4225 2 (by decide) (by decide)
      (by rw [show (4225:Nat) = 1 + 3*1408 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4414 2 (by decide) (by decide)
      (by rw [show (4414:Nat) = 1 + 3*1471 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4456 2 (by decide) (by decide)
      (by rw [show (4456:Nat) = 1 + 3*1485 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4468 2 (by decide) (by decide)
      (by rw [show (4468:Nat) = 1 + 3*1489 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4483 2 (by decide) (by decide)
      (by rw [show (4483:Nat) = 1 + 3*1494 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4567 2 (by decide) (by decide)
      (by rw [show (4567:Nat) = 1 + 3*1522 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 4618 2 (by decide) (by decide)
      (by rw [show (4618:Nat) = 1 + 3*1539 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5131 2 (by decide) (by decide)
      (by rw [show (5131:Nat) = 1 + 3*1710 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5545 2 (by decide) (by decide)
      (by rw [show (5545:Nat) = 1 + 3*1848 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5620 2 (by decide) (by decide)
      (by rw [show (5620:Nat) = 1 + 3*1873 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5626 2 (by decide) (by decide)
      (by rw [show (5626:Nat) = 1 + 3*1875 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5755 2 (by decide) (by decide)
      (by rw [show (5755:Nat) = 1 + 3*1918 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5761 2 (by decide) (by decide)
      (by rw [show (5761:Nat) = 1 + 3*1920 from by decide, wt_row_nine_read]; decide)
      (by omega))
  · exact no22_of_digit_two K 9 (fire_of_mod19683 K 5845 2 (by decide) (by decide)
      (by rw [show (5845:Nat) = 1 + 3*1948 from by decide, wt_row_nine_read]; decide)
      (by omega))

/-! ## §7 The class-one verdict at level nine -/

/-- **THE 256 SURVIVORS.** -/
def the_256_survivors_mod_19683 (K : Nat) : Prop :=
  K % 19683 = 1 ∨ K % 19683 = 4 ∨ K % 19683 = 13 ∨ K % 19683 = 121 ∨ K % 19683 = 166 ∨ K % 19683 = 280 ∨ K % 19683 = 364 ∨ K % 19683 = 436 ∨ K % 19683 = 496 ∨ K % 19683 = 514 ∨ K % 19683 = 523 ∨ K % 19683 = 595 ∨ K % 19683 = 730 ∨ K % 19683 = 739 ∨ K % 19683 = 823 ∨ K % 19683 = 838 ∨ K % 19683 = 850 ∨ K % 19683 = 922 ∨ K % 19683 = 973 ∨ K % 19683 = 1003 ∨ K % 19683 = 1093 ∨ K % 19683 = 1165 ∨ K % 19683 = 1225 ∨ K % 19683 = 1228 ∨ K % 19683 = 1243 ∨ K % 19683 = 1468 ∨ K % 19683 = 1624 ∨ K % 19683 = 1657 ∨ K % 19683 = 1732 ∨ K % 19683 = 1741 ∨ K % 19683 = 1783 ∨ K % 19683 = 1873 ∨ K % 19683 = 1900 ∨ K % 19683 = 2038 ∨ K % 19683 = 2053 ∨ K % 19683 = 2116 ∨ K % 19683 = 2188 ∨ K % 19683 = 2191 ∨ K % 19683 = 2269 ∨ K % 19683 = 2353 ∨ K % 19683 = 2467 ∨ K % 19683 = 2551 ∨ K % 19683 = 2623 ∨ K % 19683 = 2683 ∨ K % 19683 = 2782 ∨ K % 19683 = 2917 ∨ K % 19683 = 2944 ∨ K % 19683 = 3163 ∨ K % 19683 = 3190 ∨ K % 19683 = 3280 ∨ K % 19683 = 3352 ∨ K % 19683 = 3412 ∨ K % 19683 = 3415 ∨ K % 19683 = 3433 ∨ K % 19683 = 3568 ∨ K % 19683 = 3658 ∨ K % 19683 = 3673 ∨ K % 19683 = 3685 ∨ K % 19683 = 3844 ∨ K % 19683 = 3919 ∨ K % 19683 = 4060 ∨ K % 19683 = 4225 ∨ K % 19683 = 4414 ∨ K % 19683 = 4456 ∨ K % 19683 = 4468 ∨ K % 19683 = 4483 ∨ K % 19683 = 4567 ∨ K % 19683 = 4618 ∨ K % 19683 = 4888 ∨ K % 19683 = 5113 ∨ K % 19683 = 5131 ∨ K % 19683 = 5212 ∨ K % 19683 = 5224 ∨ K % 19683 = 5347 ∨ K % 19683 = 5350 ∨ K % 19683 = 5545 ∨ K % 19683 = 5620 ∨ K % 19683 = 5626 ∨ K % 19683 = 5755 ∨ K % 19683 = 5761 ∨ K % 19683 = 5845 ∨ K % 19683 = 5860 ∨ K % 19683 = 5872 ∨ K % 19683 = 6115 ∨ K % 19683 = 6274 ∨ K % 19683 = 6427 ∨ K % 19683 = 6490 ∨ K % 19683 = 6562 ∨ K % 19683 = 6565 ∨ K % 19683 = 6601 ∨ K % 19683 = 6655 ∨ K % 19683 = 6670 ∨ K % 19683 = 6727 ∨ K % 19683 = 6754 ∨ K % 19683 = 6805 ∨ K % 19683 = 6844 ∨ K % 19683 = 6886 ∨ K % 19683 = 7057 ∨ K % 19683 = 7075 ∨ K % 19683 = 7294 ∨ K % 19683 = 7300 ∨ K % 19683 = 7399 ∨ K % 19683 = 7411 ∨ K % 19683 = 7489 ∨ K % 19683 = 7534 ∨ K % 19683 = 7570 ∨ K % 19683 = 7654 ∨ K % 19683 = 7705 ∨ K % 19683 = 7726 ∨ K % 19683 = 7732 ∨ K % 19683 = 7789 ∨ K % 19683 = 7813 ∨ K % 19683 = 7948 ∨ K % 19683 = 8101 ∨ K % 19683 = 8218 ∨ K % 19683 = 8293 ∨ K % 19683 = 8302 ∨ K % 19683 = 8434 ∨ K % 19683 = 8461 ∨ K % 19683 = 8518 ∨ K % 19683 = 8599 ∨ K % 19683 = 8614 ∨ K % 19683 = 8677 ∨ K % 19683 = 8749 ∨ K % 19683 = 8752 ∨ K % 19683 = 8830 ∨ K % 19683 = 8914 ∨ K % 19683 = 8995 ∨ K % 19683 = 9031 ∨ K % 19683 = 9073 ∨ K % 19683 = 9244 ∨ K % 19683 = 9328 ∨ K % 19683 = 9481 ∨ K % 19683 = 9505 ∨ K % 19683 = 9676 ∨ K % 19683 = 9757 ∨ K % 19683 = 9841 ∨ K % 19683 = 9892 ∨ K % 19683 = 9913 ∨ K % 19683 = 9976 ∨ K % 19683 = 9994 ∨ K % 19683 = 10129 ∨ K % 19683 = 10219 ∨ K % 19683 = 10288 ∨ K % 19683 = 10405 ∨ K % 19683 = 10480 ∨ K % 19683 = 10621 ∨ K % 19683 = 10705 ∨ K % 19683 = 10723 ∨ K % 19683 = 10786 ∨ K % 19683 = 10858 ∨ K % 19683 = 10948 ∨ K % 19683 = 10975 ∨ K % 19683 = 11017 ∨ K % 19683 = 11029 ∨ K % 19683 = 11044 ∨ K % 19683 = 11056 ∨ K % 19683 = 11128 ∨ K % 19683 = 11179 ∨ K % 19683 = 11182 ∨ K % 19683 = 11458 ∨ K % 19683 = 11515 ∨ K % 19683 = 11692 ∨ K % 19683 = 11758 ∨ K % 19683 = 11857 ∨ K % 19683 = 12106 ∨ K % 19683 = 12178 ∨ K % 19683 = 12181 ∨ K % 19683 = 12187 ∨ K % 19683 = 12316 ∨ K % 19683 = 12322 ∨ K % 19683 = 12403 ∨ K % 19683 = 12406 ∨ K % 19683 = 12559 ∨ K % 19683 = 12718 ∨ K % 19683 = 12910 ∨ K % 19683 = 13045 ∨ K % 19683 = 13135 ∨ K % 19683 = 13162 ∨ K % 19683 = 13216 ∨ K % 19683 = 13231 ∨ K % 19683 = 13243 ∨ K % 19683 = 13315 ∨ K % 19683 = 13366 ∨ K % 19683 = 13402 ∨ K % 19683 = 13405 ∨ K % 19683 = 13447 ∨ K % 19683 = 13486 ∨ K % 19683 = 13558 ∨ K % 19683 = 13645 ∨ K % 19683 = 13717 ∨ K % 19683 = 13852 ∨ K % 19683 = 13855 ∨ K % 19683 = 13945 ∨ K % 19683 = 14044 ∨ K % 19683 = 14050 ∨ K % 19683 = 14125 ∨ K % 19683 = 14131 ∨ K % 19683 = 14266 ∨ K % 19683 = 14293 ∨ K % 19683 = 14347 ∨ K % 19683 = 14365 ∨ K % 19683 = 14374 ∨ K % 19683 = 14509 ∨ K % 19683 = 14590 ∨ K % 19683 = 14662 ∨ K % 19683 = 14746 ∨ K % 19683 = 14905 ∨ K % 19683 = 15079 ∨ K % 19683 = 15556 ∨ K % 19683 = 15589 ∨ K % 19683 = 15592 ∨ K % 19683 = 15634 ∨ K % 19683 = 15673 ∨ K % 19683 = 15745 ∨ K % 19683 = 15889 ∨ K % 19683 = 15904 ∨ K % 19683 = 16039 ∨ K % 19683 = 16042 ∨ K % 19683 = 16237 ∨ K % 19683 = 16285 ∨ K % 19683 = 16312 ∨ K % 19683 = 16318 ∨ K % 19683 = 16453 ∨ K % 19683 = 16534 ∨ K % 19683 = 16795 ∨ K % 19683 = 16807 ∨ K % 19683 = 16849 ∨ K % 19683 = 17266 ∨ K % 19683 = 17284 ∨ K % 19683 = 17419 ∨ K % 19683 = 17509 ∨ K % 19683 = 17617 ∨ K % 19683 = 17743 ∨ K % 19683 = 18010 ∨ K % 19683 = 18019 ∨ K % 19683 = 18076 ∨ K % 19683 = 18235 ∨ K % 19683 = 18319 ∨ K % 19683 = 18334 ∨ K % 19683 = 18346 ∨ K % 19683 = 18418 ∨ K % 19683 = 18469 ∨ K % 19683 = 18472 ∨ K % 19683 = 18739 ∨ K % 19683 = 18964 ∨ K % 19683 = 18982 ∨ K % 19683 = 18994 ∨ K % 19683 = 19120 ∨ K % 19683 = 19237 ∨ K % 19683 = 19279 ∨ K % 19683 = 19396 ∨ K % 19683 = 19471 ∨ K % 19683 = 19549 ∨ K % 19683 = 19606 ∨ K % 19683 = 19612

/-- **THE CLASS-ONE VERDICT.** -/
theorem class_one_verdict_19683 (K : Nat) (h1 : K % 3 = 1) :
    noTernaryTwo (4^K) = false ∨ the_256_survivors_mod_19683 K := by
  by_cases hC : CantorianPower K
  · exact Or.inr (cantorian_dust_mod_19683 K h1 hC)
  · have hex : ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 := by
      by_contra hall
      exact hC (fun p hp1 hp2 => hall ⟨p, hp1, hp2⟩)
    obtain ⟨p, _hp1, hp2⟩ := hex
    exact Or.inl (no22_of_digit_two K p hp2)

/-! ## §8 THE GRAND RECORD -/

/-- **THE FINAL ASSEMBLY.**  One theorem, the whole campaign. -/
theorem the_final_assembly :
    (GSTTheAct.the_act ↔
      GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (GSTTheAct.the_act ↔
      (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false)) ∧
    (∀ h : erdos_406_the_last_hypothesis,
        ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ∧
    (∀ h : (∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K),
        ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ∧
    (∀ hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb,
        ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ∧
    (∀ hRow : GSTTailFFourthDimension.tailF_row_primitive,
        ∀ hTower : GSTTailFFourthDimension.tailF_tower_primitive,
        ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ∧
    (∀ K : Nat, 8 ≤ K →
        (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K) ∧
    (∀ K : Nat, 8 ≤ K → CantorianPower K → WindowCleanDust K) ∧
    (CantorianPower 0 ∧ CantorianPower 1 ∧ CantorianPower 4 ∧
      ¬ CantorianPower 2 ∧ ¬ CantorianPower 3 ∧ ¬ CantorianPower 5 ∧
      ¬ CantorianPower 6 ∧ ¬ CantorianPower 7) ∧
    (∀ v a : Nat, digit3 (4^(3^v * a)) (v + 1) = a % 3) ∧
    (∀ K : Nat, K % 3 = 1 →
        noTernaryTwo (4^K) = false ∨ the_256_survivors_mod_19683 K) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
        noTernaryTwo (4^(T + 3^(j+1)*u)) = false) ∧
    (∀ N : Nat, ∃ K : Nat, N ≤ K ∧ wave3_deep_member K) ∧
    (∀ K : Nat, wave3_deep_member K →
        ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) ∧
    (erdos_406_the_last_hypothesis ↔ GSTTheAct.the_act) ∧
    ((∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) →
      erdos_406_the_last_hypothesis) ∧
    (noTernaryTwo (4^5) = false ∧ noTernaryTwo (4^6) = false ∧
      noTernaryTwo (4^7) = false) :=
  ⟨the_act_iff_tailF_unconditional, the_act_iff_full_erdos_unconditional,
    fun h n hn => erdos_ternary_2_universal_of_last_hypothesis h n hn,
    fun h n hn => erdos_ternary_2_universal_of_dust_empty h n hn,
    fun hClimb n hn => erdos_ternary_2_universal_of_climb hClimb n hn,
    fun hRow hTower n hn =>
      erdos_ternary_2_universal_of_row_and_tower hRow hTower n hn,
    every_exponent_fires,
    fun K hK hC => cantorian_is_dust K hK hC,
    cantorian_survivors_below_eight,
    GSTTheAct.front_law,
    fun K h1 => class_one_verdict_19683 K h1,
    fun T u j hj hT hkill => no22_of_pair_read_general T u j hj hT hkill,
    wave3_deep_unbounded,
    fun K hK => climb_member_of_wave3_deep K hK,
    the_last_hypothesis_iff_the_act,
    no_cantorian_of_dust_empty,
    ⟨GSTClimbTruthValue.no22_four_pow_five,
      GSTClimbTruthValue.no22_four_pow_six,
      GSTClimbTruthValue.no22_four_pow_seven⟩⟩

/-! ## §9 The receipts -/

#print axioms the_act_iff_tailF_unconditional
#print axioms the_act_iff_full_erdos_unconditional
#print axioms full_erdos_of_the_act_unconditional
#print axioms erdos_ternary_2_universal_of_the_act
#print axioms erdos_ternary_2_universal_of_no_cantorian
#print axioms erdos_ternary_2_universal_of_dust_empty
#print axioms erdos_ternary_2_universal_of_climb
#print axioms erdos_ternary_2_universal_of_row_and_tower
#print axioms cantorian_is_dust
#print axioms no_cantorian_of_dust_empty
#print axioms erdos_ternary_2_universal_of_last_hypothesis
#print axioms no22_of_cascade_total
#print axioms class_one_verdict_19683
#print axioms the_final_assembly

