/-
# ERDŐS #413 — THE OMEGA-CHAMPION WINDOW LAW + THE CERTIFIED CENSUS KERNEL

Problem (Erdős, corpus statement 413): let ω(n) be the number of distinct
primes dividing n.  Are there infinitely many n such that, for all m < n,

    m + ω(m) ≤ n ?

Can one show there is an ε > 0 with infinitely many n where
m + ε·ω(m) ≤ n for all m < n?

Call n a CHAMPION iff ∀ 1 ≤ m < n : m + ω(m) ≤ n.  This kernel proves the
complete structural reduction of the champion test — the WINDOW LAW — and
certifies the champion board n ≤ 30 by decide, with the census to 20000
carried by the python mirror (`census413.py`, receipt
`census413_output.txt`, triple-method agreement on all 20000 rows).

## THE WINDOW LAW (this file, §4)

    n champion  ⟺  ∀ j ∈ [1, n−1] : ω(n − j) ≤ j        (substitute m = n − j).

The substitution/subtraction bijection m ↦ n − j is pure arithmetic: the
law holds for EVERY g : Nat → Nat (`E413.window_law_gen`), i.e. it is an
ω-independent fact.  Row j = 1 forces ω(n−1) ≤ 1 — n − 1 is a prime power
(the j=1 step, `E413.champion_j1_step`); row j = 2 forces ω(n−2) ≤ 2; etc.

## THE TRIVIAL TAIL (this file, §3)

    2 ^ ω(m) ≤ m      (product of the distinct primes of m divides m).

Hence 2 ^ j ≥ n > n − j forces ω(n − j) < j: every window row with
j ≥ J is VACUOUS once 2 ^ J ≥ n.  So the champion test is a FINITE window
(`E413.finite_window`):  n champion ⟺ ω(n−j) ≤ j for 1 ≤ j ≤ min(J, n−1).
For the board n ≤ 30: 2 ^ 5 = 32 ≥ 31, so FIVE rows suffice
(`E413.finite_window_board`, `E413.champion_via_bounded_window`).

## THE CERTIFIED BOARD (this file, §6, decide; python mirror, §6 of census413.py)

    champions ≤ 30 = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 17, 18,
                       20, 24, 26, 28, 30]                      (18 champions)

certified THREE ways per n ∈ [1, 30]: the direct champion row (max-scan
semantics: all m ∈ [1, n−1] satisfy m + ω(m) ≤ n), the full window row
(ω(n−j) ≤ j for all j ∈ [1, n−1]), and the FIVE-ROW bounded window —
the three agree on every row (`e413_board_dual`, `e413_board_bounded`)
and carve the exact list (`e413_board_exact`).  The census to 20000 (426
champions) is banked in census413_output.txt; the funnel law there: rows
1..1 : 2330 candidates → 1..2 : 480 → 1..3 : 427 → 1..4 : 426 = champions.

## HONEST SCOPE

The infinitude question (both the ε = 1 and the ε > 0 forms) stays OPEN.
The kill delivered here is the window law + the finite-window reduction +
the certified census, labeled exactly as such.

Core Lean 4 only.  No imports.  No Mathlib.  No `sorry`.  No custom axioms.
Fuel-indexed definitions follow the SubsetKernelLaw v2 blueprint
(structural on fuel — no well-founded recursion, no termination proofs).
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace E413

-- ===========================================================================
-- §1  THE ω MACHINERY (fuel-indexed scan: count distinct prime factors by
--     scanning candidate divisors upward, stripping ALL powers of each hit)
-- ===========================================================================

/-- Strip every factor of d out of r (fuel-bounded; fuel `f` divisions).
`stripF f d r` divides r by d until d ∤ r; returns r if fuel runs dry. -/
def stripF : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | f + 1, d, r => if r % d = 0 then stripF f d (r / d) else r

/-- The distinct-prime-factor scan: candidate d marches upward; when d
divides the remaining r, d is counted ONCE and all its powers are
stripped (so no composite can ever be counted — its proper factor was
already stripped), and r shrinks.  Guards: r ≤ 1 (cofactor exhausted),
d > r (safety valve). -/
def omegaScan : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, c => c
  | f + 1, d, r, c =>
    if r ≤ 1 then c
    else if d > r then c
    else if r % d = 0 then omegaScan f (d + 1) (stripF (r + 1) d r) (c + 1)
    else omegaScan f (d + 1) r c

/-- ω(n) = the number of distinct primes dividing n (ω 0 = ω 1 = 0).
Fuel n + 2 covers the worst case (d marching 2 → n). -/
def omega (n : Nat) : Nat := omegaScan (n + 2) 2 n 0

/-- ω sanity anchors (python mirror: len(sympy.primefactors m)). -/
theorem omega_1 : omega 1 = 0 := by decide
theorem omega_2 : omega 2 = 1 := by decide
theorem omega_30 : omega 30 = 3 := by decide
theorem omega_210 : omega 210 = 4 := by decide
theorem omega_2310 : omega 2310 = 5 := by decide
theorem omega_30030 : omega 30030 = 6 := by decide

-- ===========================================================================
-- §2  THE STRIP LEMMAS (fuel induction; core Nat arithmetic only)
-- ===========================================================================

/-- decide p = true from p (the local sibling of `of_decide_eq_true`). -/
private theorem decideTrue {p : Prop} [inst : Decidable p] (hp : p) :
    decide p = true := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd hp hnp

/-- a ≤ a * r for r ≥ 1 (a·1 ≤ a·r). -/
private theorem le_mul_self (a r : Nat) (hr : 1 ≤ r) : a ≤ a * r := by
  have h := Nat.mul_le_mul_left a hr
  rw [Nat.mul_one] at h
  exact h

/-- r / d ≤ r for d ≥ 1 (from d·(r/d) + r%d = r; atom arithmetic). -/
private theorem div_le_of_pos (r d : Nat) (hd : 1 ≤ d) : r / d ≤ r := by
  have hdm : d * (r / d) + r % d = r := Nat.div_add_mod r d
  have h1 : 1 * (r / d) ≤ d * (r / d) := Nat.mul_le_mul_right (r / d) hd
  rw [Nat.one_mul] at h1
  omega

/-- Stripping never inflates: stripF f d r ≤ r (fuel induction). -/
theorem stripF_le : ∀ (f d r : Nat), 1 ≤ d → stripF f d r ≤ r
  | 0, _, _, _ => Nat.le_refl _
  | f + 1, d, r, hd => by
    simp only [stripF]
    by_cases hmod : r % d = 0
    · rw [if_pos hmod]
      have ih := stripF_le f d (r / d) hd
      have hge : r / d ≤ r := div_le_of_pos r d hd
      omega
    · rw [if_neg hmod]
      exact Nat.le_refl r

/-- Stripping preserves positivity (fuel induction). -/
theorem stripF_ge1 : ∀ (f d r : Nat), 1 ≤ d → 1 ≤ r → 1 ≤ stripF f d r
  | 0, _, _, _, hr => hr
  | f + 1, d, r, hd, hr => by
    simp only [stripF]
    by_cases hmod : r % d = 0
    · rw [if_pos hmod]
      have ih : 1 ≤ r / d → 1 ≤ stripF f d (r / d) := stripF_ge1 f d (r / d) hd
      have hdm : d * (r / d) + r % d = r := Nat.div_add_mod r d
      rw [hmod] at hdm
      by_cases hz : r / d = 0
      · rw [hz] at hdm
        omega
      · have hp : 1 ≤ r / d := by omega
        exact ih hp
    · rw [if_neg hmod]
      exact hr

/-- One counted factor at least halves the cofactor: d ∣ r, d ≥ 2 ⇒
2 · stripF (f+1) d r ≤ r (strip removes at least one factor of d). -/
theorem stripF_half (f d r : Nat) (hd : 2 ≤ d) (hmod : r % d = 0) :
    2 * stripF (f + 1) d r ≤ r := by
  have hstep : stripF (f + 1) d r = stripF f d (r / d) := by
    simp only [stripF]
    rw [if_pos hmod]
  rw [hstep]
  have hle := stripF_le f d (r / d) hd
  have h2 : 2 * (r / d) ≤ r := by
    have hdm : d * (r / d) + r % d = r := Nat.div_add_mod r d
    rw [hmod] at hdm
    have hprod : 2 * (r / d) ≤ d * (r / d) := Nat.mul_le_mul_right (r / d) hd
    omega
  omega

-- ===========================================================================
-- §3  THE TRIVIAL TAIL:  2 ^ ω(n) ≤ n  →  the window is finite
-- ===========================================================================

/-- THE SCAN BOUND (fuel induction, the invariant 2^count · cofactor ≤ n):
at every call with d ≥ 2 and r ≥ 1, 2 ^ (final count) ≤ 2 ^ c * r. -/
theorem omegaScan_bound : ∀ (f d r c : Nat), 2 ≤ d → 1 ≤ r →
    2 ^ omegaScan f d r c ≤ 2 ^ c * r
  | 0, d, r, c, _, hr => by
    have h0 : omegaScan 0 d r c = c := rfl
    rw [h0]
    exact le_mul_self (2 ^ c) r hr
  | f + 1, d, r, c, hd, hr => by
    simp only [omegaScan]
    by_cases hr1 : r ≤ 1
    · rw [if_pos hr1]
      exact le_mul_self (2 ^ c) r hr
    · rw [if_neg hr1]
      by_cases hdr : d > r
      · rw [if_pos hdr]
        exact le_mul_self (2 ^ c) r hr
      · rw [if_neg hdr]
        by_cases hmod : r % d = 0
        · rw [if_pos hmod]
          have IH := omegaScan_bound f (d + 1) (stripF (r + 1) d r) (c + 1)
            (by omega : 2 ≤ d + 1) (stripF_ge1 (r + 1) d r hd hr)
          have hhalf : 2 * stripF (r + 1) d r ≤ r := stripF_half r d r hd hmod
          have hchain : 2 ^ (c + 1) * stripF (r + 1) d r ≤ 2 ^ c * r := by
            rw [Nat.pow_succ, Nat.mul_assoc]
            exact Nat.mul_le_mul_left (2 ^ c) hhalf
          exact Nat.le_trans IH hchain
        · rw [if_neg hmod]
          exact omegaScan_bound f (d + 1) r c (by omega) hr

/-- THE TRIVIAL TAIL LAW: 2 ^ ω(n) ≤ n for every n ≥ 1.
(The product of the ω(n) distinct primes of n divides n and is ≥ 2^ω(n);
here the law rides the scan invariant 2^count · cofactor ≤ n.) -/
theorem omega_pow2_le (n : Nat) (hn : 1 ≤ n) : 2 ^ omega n ≤ n := by
  have IH := omegaScan_bound (n + 2) 2 n 0 (by omega) hn
  rw [Nat.pow_zero, Nat.one_mul] at IH
  exact IH

private theorem one_le_pow2 (a : Nat) : 1 ≤ 2 ^ a := by
  induction a with
  | zero => rw [Nat.pow_zero]; exact Nat.le_refl 1
  | succ a ih => rw [Nat.pow_succ]; omega

private theorem pow2_mono : ∀ (b a : Nat), a ≤ b → 2 ^ a ≤ 2 ^ b
  | 0, a, h => by
    have ha : a = 0 := by omega
    rw [ha]
    exact Nat.le_refl (2 ^ 0)
  | b + 1, a, h => by
    by_cases hae : a = b + 1
    · rw [hae]
      exact Nat.le_refl (2 ^ (b + 1))
    · have hle : a ≤ b := by omega
      have h1 : 2 ^ a ≤ 2 ^ b := pow2_mono b a hle
      have h2 : 2 ^ b ≤ 2 ^ (b + 1) := by
        rw [Nat.pow_succ]
        have hp := one_le_pow2 b
        omega
      exact Nat.le_trans h1 h2

private theorem pow2_le_imp (x j : Nat) (h : 2 ^ x ≤ 2 ^ j) : x ≤ j := by
  by_cases hle : x ≤ j
  · exact hle
  · have hlt2 : j + 1 ≤ x := by omega
    have h1 : 2 ^ (j + 1) ≤ 2 ^ x := pow2_mono x (j + 1) hlt2
    have h2 : 2 ^ j < 2 ^ (j + 1) := by
      rw [Nat.pow_succ]
      have hp := one_le_pow2 j
      omega
    omega

/-- THE FINITE WINDOW: if n ≤ 2 ^ J then the champion window is bounded by
J — every row j > J is vacuous (2 ^ j ≥ 2 ^ J ≥ n > n − j forces
ω(n−j) < j).  The champion test is a finite J-row window. -/
theorem finite_window (n J : Nat) (hJ : n ≤ 2 ^ J) :
    (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) ↔
    (∀ j, 1 ≤ j → j ≤ J → j ≤ n - 1 → omega (n - j) ≤ j) := by
  constructor
  · intro h j hj1 _ hjn1
    exact h j hj1 hjn1
  · intro h j hj1 hjn1
    by_cases hjJ : j ≤ J
    · exact h j hj1 hjJ hjn1
    · have htail : 2 ^ omega (n - j) ≤ n - j :=
        omega_pow2_le (n - j) (by omega : 1 ≤ n - j)
      have hmono : 2 ^ J ≤ 2 ^ j := pow2_mono j J (by omega : J ≤ j)
      have hlt : 2 ^ omega (n - j) < 2 ^ j := by omega
      exact pow2_le_imp (omega (n - j)) j (Nat.le_of_lt hlt)

/-- THE BOARD CUT: n ≤ 30 ≤ 2 ^ 5 — five window rows suffice. -/
theorem finite_window_board (n : Nat) (hn : n ≤ 30) :
    (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) ↔
    (∀ j, 1 ≤ j → j ≤ 5 → j ≤ n - 1 → omega (n - j) ≤ j) := by
  refine finite_window n 5 ?_
  have h32 : (2 : Nat) ^ 5 = 32 := by decide
  omega

-- ===========================================================================
-- §4  THE WINDOW LAW (the mathematical core — pure arithmetic, ω-free)
-- ===========================================================================

/-- THE WINDOW LAW, GENERAL FORM: for EVERY g : Nat → Nat,
(∀ 1 ≤ m < n, m + g m ≤ n) ↔ (∀ 1 ≤ j ≤ n−1, g (n − j) ≤ j).
The bijection is m = n − j (substitution forward, subtraction backward). -/
theorem window_law_gen (g : Nat → Nat) (n : Nat) :
    (∀ m, 1 ≤ m → m < n → m + g m ≤ n) ↔
    (∀ j, 1 ≤ j → j ≤ n - 1 → g (n - j) ≤ j) := by
  constructor
  · intro h j hj1 hj2
    have hm1 : 1 ≤ n - j := by omega
    have hm2 : n - j < n := by omega
    have h3 := h (n - j) hm1 hm2
    omega
  · intro h m hm1 hm2
    have hj1 : 1 ≤ n - m := by omega
    have hj2 : n - m ≤ n - 1 := by omega
    have h3 := h (n - m) hj1 hj2
    rw [show n - (n - m) = m from by omega] at h3
    omega

/-- THE WINDOW LAW: n is a champion (all m < n satisfy m + ω(m) ≤ n)
if and only if every window row holds: ω(n − j) ≤ j for all 1 ≤ j ≤ n−1. -/
theorem window_law (n : Nat) :
    (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) ↔
    (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) :=
  window_law_gen omega n

/-- THE j = 1 STEP: every champion n ≥ 3 has ω(n − 1) ≤ 1 — n − 1 is a
prime power (the census: 408 primes, 16 proper powers, 0 exceptions). -/
theorem champion_j1_step (n : Nat) (hn : 2 ≤ n) :
    (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) → omega (n - 1) ≤ 1 := by
  intro h
  have hw := (window_law n).mp h
  exact hw 1 (by omega) (by omega)

/-- THE FULL REDUCTION for the board: for n ≤ 30, champion(n) ⟺ the
five-row window (window law + finite window composed). -/
theorem champion_via_bounded_window (n : Nat) (hn : n ≤ 30) :
    (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) ↔
    (∀ j, 1 ≤ j → j ≤ 5 → j ≤ n - 1 → omega (n - j) ≤ j) := by
  rw [window_law]
  exact finite_window_board n hn

-- ===========================================================================
-- §5  THE BOARD ROWS (Bool mirrors of the three tests, bridge theorems)
-- ===========================================================================

/-- Direct champion row: every m ∈ [1, n−1] satisfies m + ω(m) ≤ n. -/
def champRow (n : Nat) : Bool :=
  (List.range (n - 1)).all (fun m => decide (m + 1 + omega (m + 1) ≤ n))

/-- Full window row: ω(n − j) ≤ j for every j ∈ [1, n−1]. -/
def windowRow (n : Nat) : Bool :=
  (List.range (n - 1)).all (fun j => decide (omega (n - (j + 1)) ≤ j + 1))

/-- Bounded window row (J = 5): ω(n − j) ≤ j for j ∈ [1, 5] only. -/
def bWinRow (n : Nat) : Bool :=
  (List.range 5).all (fun k => decide (omega (n - (k + 1)) ≤ k + 1))

theorem champRow_iff (n : Nat) :
    champRow n = true ↔ (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) := by
  constructor
  · intro hb m hm1 hm2
    have hmem : m - 1 ∈ List.range (n - 1) := List.mem_range.mpr (by omega)
    have hcell : decide (m - 1 + 1 + omega (m - 1 + 1) ≤ n) = true :=
      (List.all_eq_true.mp hb) (m - 1) hmem
    rw [show m - 1 + 1 = m from by omega] at hcell
    exact of_decide_eq_true hcell
  · intro h
    refine List.all_eq_true.mpr ?_
    intro k hk
    have hklt : k < n - 1 := List.mem_range.mp hk
    exact decideTrue (h (k + 1) (by omega) (by omega))

theorem windowRow_iff (n : Nat) :
    windowRow n = true ↔ (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) := by
  constructor
  · intro hb j hj1 hj2
    have hmem : j - 1 ∈ List.range (n - 1) := List.mem_range.mpr (by omega)
    have hcell : decide (omega (n - (j - 1 + 1)) ≤ j - 1 + 1) = true :=
      (List.all_eq_true.mp hb) (j - 1) hmem
    rw [show j - 1 + 1 = j from by omega] at hcell
    exact of_decide_eq_true hcell
  · intro h
    refine List.all_eq_true.mpr ?_
    intro k hk
    have hklt : k < n - 1 := List.mem_range.mp hk
    exact decideTrue (h (k + 1) (by omega) (by omega))

theorem bWinRow_iff (n : Nat) :
    bWinRow n = true ↔ (∀ j, 1 ≤ j → j ≤ 5 → omega (n - j) ≤ j) := by
  constructor
  · intro hb j hj1 hj5
    have hmem : j - 1 ∈ List.range 5 := List.mem_range.mpr (by omega)
    have hcell : decide (omega (n - (j - 1 + 1)) ≤ j - 1 + 1) = true :=
      (List.all_eq_true.mp hb) (j - 1) hmem
    rw [show j - 1 + 1 = j from by omega] at hcell
    exact of_decide_eq_true hcell
  · intro h
    refine List.all_eq_true.mpr ?_
    intro k hk
    have hklt : k < 5 := List.mem_range.mp hk
    exact decideTrue (h (k + 1) (by omega) (by omega))

-- ===========================================================================
-- §6  THE CERTIFIED BOARD (n ≤ 30, decide; NO-OOM: bounded scans ≤ 31)
-- ===========================================================================

/-- The certified champion board (python mirror, exact): 18 champions. -/
def champBoard : List Nat :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 17, 18, 20, 24, 26, 28, 30]

/-- The ω table for m ∈ [0, 30] (python mirror, exact). -/
def oTab : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1
  | 8 => 1 | 9 => 1 | 10 => 2 | 11 => 1 | 12 => 2 | 13 => 1 | 14 => 2
  | 15 => 2 | 16 => 1 | 17 => 1 | 18 => 2 | 19 => 1 | 20 => 2 | 21 => 2
  | 22 => 2 | 23 => 1 | 24 => 2 | 25 => 1 | 26 => 2 | 27 => 1 | 28 => 2
  | 29 => 1 | 30 => 3
  | _ => 0

/-- ω TABLE RECEIPT: the kernel's ω equals the true ω on all of [0, 30]. -/
theorem e413_omega_table :
    (List.range 31).all (fun m => omega m == oTab m) = true := by decide

/-- DUAL BOARD: the direct champion row and the full window row agree on
every n ∈ [1, 30] (the window law, decide-certified row by row). -/
theorem e413_board_dual :
    (List.range 30).all (fun k => champRow (k + 1) == windowRow (k + 1)) = true := by
  decide

/-- BOUNDED BOARD: the direct champion row and the FIVE-ROW bounded window
agree on every n ∈ [1, 30] (the trivial tail, decide-certified row by row). -/
theorem e413_board_bounded :
    (List.range 30).all (fun k => champRow (k + 1) == bWinRow (k + 1)) = true := by
  decide

/-- THE CERTIFIED CHAMPION LIST: champions ≤ 30 are exactly the 18 values
of champBoard (1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 17, 18, 20, 24, 26,
28, 30) — and no others. -/
theorem e413_board_exact :
    (List.range 30).all (fun k => champRow (k + 1) == champBoard.contains (k + 1)) = true := by
  decide

/-- The three row-bridges lifted to the exact board list: for every
n ∈ [1, 30], champRow n = true ↔ n is a champion ↔ n ∈ champBoard. -/
theorem e413_board_rows (n : Nat) (hn : n ≤ 30) :
    champRow n = true ↔ (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) := champRow_iff n

theorem e413_board_window_rows (n : Nat) :
    windowRow n = true ↔ (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) :=
  windowRow_iff n

theorem e413_board_bounded_rows (n : Nat) :
    bWinRow n = true ↔ (∀ j, 1 ≤ j → j ≤ 5 → omega (n - j) ≤ j) := bWinRow_iff n

/-- THE MAIN SUMMARY. -/
theorem e413_main :
    (∀ (g : Nat → Nat) (n : Nat),
      (∀ m, 1 ≤ m → m < n → m + g m ≤ n) ↔
      (∀ j, 1 ≤ j → j ≤ n - 1 → g (n - j) ≤ j)) ∧
    (∀ (n : Nat),
      (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) ↔
      (∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j)) ∧
    (∀ n, 1 ≤ n → 2 ^ omega n ≤ n) ∧
    (∀ n J, n ≤ 2 ^ J →
      ((∀ j, 1 ≤ j → j ≤ n - 1 → omega (n - j) ≤ j) ↔
      (∀ j, 1 ≤ j → j ≤ J → j ≤ n - 1 → omega (n - j) ≤ j))) ∧
    (∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) → omega (n - 1) ≤ 1) ∧
    (∀ n, n ≤ 30 →
      (∀ m, 1 ≤ m → m < n → m + omega m ≤ n) ↔
      (∀ j, 1 ≤ j → j ≤ 5 → j ≤ n - 1 → omega (n - j) ≤ j)) ∧
    ((List.range 31).all (fun m => omega m == oTab m) = true) ∧
    ((List.range 30).all (fun k => champRow (k + 1) == windowRow (k + 1)) = true) ∧
    ((List.range 30).all (fun k => champRow (k + 1) == bWinRow (k + 1)) = true) ∧
    ((List.range 30).all
      (fun k => champRow (k + 1) == champBoard.contains (k + 1)) = true) ∧
    (omega 210 = 4 ∧ omega 2310 = 5 ∧ omega 30030 = 6) :=
  ⟨window_law_gen, window_law, omega_pow2_le, finite_window, champion_j1_step,
   champion_via_bounded_window, e413_omega_table, e413_board_dual,
   e413_board_bounded, e413_board_exact, ⟨omega_210, omega_2310, omega_30030⟩⟩

end E413

-- ===========================================================================
-- §7  RECEIPTS
-- ===========================================================================

#eval "E413_OMEGA_CHAMPIONS_GREEN"
#print axioms E413.window_law_gen
#print axioms E413.window_law
#print axioms E413.omega_pow2_le
#print axioms E413.finite_window
#print axioms E413.finite_window_board
#print axioms E413.champion_j1_step
#print axioms E413.champion_via_bounded_window
#print axioms E413.champRow_iff
#print axioms E413.windowRow_iff
#print axioms E413.bWinRow_iff
#print axioms E413.e413_omega_table
#print axioms E413.e413_board_dual
#print axioms E413.e413_board_bounded
#print axioms E413.e413_board_exact
#print axioms E413.e413_main
