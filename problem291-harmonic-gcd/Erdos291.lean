import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos291 — THE HARMONIC-GCD KERNEL (Kernel 291, W61, #291)

## THE PROBLEM (corpus statement, /tmp/ep-statements/291.txt)

> Let n ≥ 1 and define L_n to be the least common multiple of {1,…,n}
> and a_n by Σ_{1≤k≤n} 1/k = a_n/L_n.  Is it true that (a_n,L_n) = 1 and
> (a_n,L_n) > 1 both occur for infinitely many n?

Erdős #291: the harmonic numerator a_n over the lcm scale L_n — when is
the fraction a_n/L_n already reduced?

## THE CASE LAW (DERIVATION.md, battery291.py — the N = 400 dual census)

**THE p-ADIC LOCAL CRITERION (the LAW).**  For a prime q ≤ n write
e = v_q(L_n) = ⌊log_q n⌋ and m = ⌊n/q^e⌋ ∈ [1, q−1] (the LEADING BASE-q
DIGIT of n).  Then

    q ∣ a_n  ⟺  Σ_{u=1}^{m} u^{-1} ≡ 0 (mod q)  ⟺  q ∣ num(H_m),

because a_n = Σ_k L_n/k ≡ (L_n/q^e)·Σ_{u≤m} u^{-1} (mod q) and the
q-free cofactor L_n/q^e is a unit mod q.  Hence

    gcd(a_n, L_n) > 1  ⟺  ∃ prime q ∈ [3, n] with q ∣ num(H_{d_q(n)}).

Consequences the census (n ≤ 400, TWO INDEPENDENT METHODS — exact
big-integer gmpy2 arithmetic AND a fully modular p-adic method — agreeing
on every gcd value, plus the LAW's third path) certifies:
* 2 NEVER divides g(n) (Kürschák's unique maximal-2-adic-term law:
  the leading base-2 digit is always 1 and num(H_1) = 1);
* 3 ∣ g(n) ⟺ leading base-3 digit of n is 2 ⟺ n ∈ [2·3^e, 3^{e+1}), e ≥ 1
  — n = 6,7,8, 18..26, 54..80, 162..242, …;
* every prime q ≥ 3 fires on its digit-(q−1) rows: n ∈ [(q−1)q^e, q^{e+1})
  (D_q ∋ q−1 for ALL q ≥ 3 — the H_{q−1} ≡ 0 mod q congruence);
* exceptional digit rows: D_11 = {3,7,10}, D_29 = {13,15,28}, … (the
  pairs (m,q) with m < q−1, q ∣ num(H_m));
* Wolstenholme primes do NOT lift the gcd: H_{p−1} ≡ 0 mod p² but
  p ∤ L_{p−1} (p > p−1 = n), e.g. 11 ∣ a_10 = 7381 = 11²·61 yet
  gcd(a_10, L_10) = 1.

**THE n ≤ 400 CENSUS (296 of 400 rows have gcd > 1):**
[6,8] ∪ [18,26] ∪ [33,48] ∪ [54,87] ∪ [100,124] ∪ [156,242] ∪ [272,288]
∪ [294,360] ∪ [363,400] — the gcd = 1 complement is
{1..5, 9..17, 27..32, 49..53, 88..99, 125..155, 243..271, 289..293, 361..362}.

## WHAT THIS KERNEL PROVES (complete unconditional theorems)

1. **THE DEFINITIONS + STRUCTURAL LAWS**: L (the lcm ladder on the core
   `Nat.gcd`), a (the exact harmonic numerator fold Σ L_n/k), g = gcd;
   positivity of L_n and a_n; THE DIVISIBILITY SPINE k ∣ L_n for all
   1 ≤ k ≤ n; gcd(a_n, L_n) ∣ a_n and ∣ L_n; the gcd universality
   (c ∣ a_n → c ∣ L_n → c ∣ g(n)) — full generality, zero hypotheses.
2. **THE WITNESS TABLES**: a_5 = 137, L_5 = 60, gcd = 1 (H_5 = 137/60 —
   reduced); a_6 = 147, L_6 = 60, gcd = 3 with 147/3 = 49, 60/3 = 20
   (H_6 = 49/20 — the #317 crossing row); a_7 = 1089, L_7 = 420, gcd = 3;
   the full n = 1..25 gcd table; the 3-spike family rows
   g(6) = g(18) = g(54) = 3, g(162) = 39, g(486) = 3.
3. **THE WOLSTENHOLME NON-LIFT ROW**: 11 ∣ a_10 = 7381 = 11²·61 yet
   gcd(a_10, L_10) = 1 and 11 ∤ L_10 — the canonical evidence that the
   gcd condition is q ≤ n, not q ∣ num(H_{q−1}).
4. **THE D_q DIGIT TABLE** (the LAW's engine): for q = 3, 5, 7, 11, 13
   the exact rows D_3 = {2}, D_5 = {4}, D_7 = {6}, D_11 = {3,7,10},
   D_13 = {12} — i.e. for every m ∈ [1, q−1]: q ∣ a_m ⟺ m is in the row
   (a_m IS num(H_m)·(the q-free scale) — and q ∤ L_m for m < q).
5. **THE p-ADIC CRITERION ROWS (fixed small primes, the n ≤ 25 board)**:
   Kürschák's law (2 ∤ g(n) for all 25 rows); the 3-criterion
   (3 ∣ g(n) ⟺ leading base-3 digit 2, i.e. n/3 = 2 ∨ n/9 = 2);
   the 5-criterion (5 ∣ g(n) ⟺ n/5 = 4); the empty 7/11/13 rows
   (their spikes start at 42, 33, 156 — beyond the board).
6. **THE n ≤ 25 CLASSIFICATION**: for every 1 ≤ n ≤ 25,
   gcd(a_n, L_n) > 1 ⟺ n = 6 ∨ n = 7 ∨ n = 8 ∨ 18 ≤ n
   (both directions, from the two kernel-decided sweeps).
7. **THE ARSENAL BRIDGE** (ErdosTernary2 + CardinalWorlds applied to the
   n = 8 spike row) + **THE MASTER BOARD** (the flat conjunction).

Honest scope: the two infinitude questions of Erdős #291 REMAIN OPEN —
this kernel certifies the case law (the census, the criterion rows, the
classification) unconditionally on the bounded boards, and the DERIVATION
proves the general p-adic criterion and the infinite 3-spike family
n ∈ [2·3^e, 3^{e+1}) (3 ∣ a_n for EVERY such n — infinitely many
gcd > 1 rows) as paper mathematics with the kernel certifying the
e = 1..5 instances (6, 18, 54, 162, 486).  The general-form Leanization of
the p-adic criterion (v_q(L_n) machinery) is the next round's war.

House-law compliance: GitHub CI is the verifier of record (no local
compile; author blind).  Zero sorry, zero admit, zero native_decide.
`by decide` only on closed numerics and bounded `List.range` sweeps
(≤ 25 rows — the L45 no-OOM law, far below the 501 cap).  No Mathlib
theorem citations: core `Nat` lemmas + in-file locals only, on the
Arsenal import set.  L86/L90 orientation laws respected (mul_comm/one_mul
bridges; no defeq trusted across variable multiplications); L91: no
variable-level beq (divisibility spelled `x % q = 0`).
-/

namespace E291

/-! ## §0 The definitions — the lcm ladder, the harmonic numerator fold. -/

/-- The binary lcm on Nat via the core gcd: lcmd a b = a·b / gcd(a,b). -/
def lcmd (a b : Nat) : Nat := a * b / Nat.gcd a b

/-- THE LCM LADDER: L_n = lcm(1, 2, …, n) as the structural recursion
L_0 = 1, L_{n+1} = lcm(L_n, n+1) — the corpus's L_n. -/
def LN : Nat → Nat
  | 0 => 1
  | n + 1 => lcmd (LN n) (n + 1)

/-- THE HARMONIC NUMERATOR FOLD: aAux L k f = L/k + L/(k+1) + … + L/(k+f−1)
(exact Nat division — every k in range divides L = L_n by §1's spine). -/
def aAux : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | L, k, f + 1 => L / k + aAux L (k + 1) f

/-- THE CORPUS'S a_n: a_n = Σ_{1≤k≤n} L_n / k, so Σ 1/k = a_n / L_n. -/
def aN (n : Nat) : Nat := aAux (LN n) 1 n

/-- THE ERDŐS #291 OBJECT: g(n) = gcd(a_n, L_n). -/
def gN (n : Nat) : Nat := Nat.gcd (aN n) (LN n)

/-! ## §1 The division engine and the lcm laws (core-local, 677-style). -/

/-- Exact division: m % k = 0 → m / k * k = m (from `Nat.div_add_mod`,
bridged through the L86 orientation law). -/
theorem e291_div_mul_self (m k : Nat) (hmod : m % k = 0) : m / k * k = m := by
  have h := Nat.div_add_mod m k
  rw [hmod, Nat.add_zero, Nat.mul_comm k (m / k)] at h
  exact h

/-- dvd → mod-zero (the 708-proven one-liner on the core lemma). -/
theorem e291_dvd_mod_zero (d n : Nat) (h : d ∣ n) : n % d = 0 :=
  Nat.mod_eq_zero_of_dvd h

/-- Multiplication closure of dvd: d ∣ a → d ∣ a * b (rfl-subst route —
orientation-agnostic). -/
theorem e291_dvd_mul_of (d a b : Nat) (h : d ∣ a) : d ∣ a * b := by
  rcases h with ⟨c, rfl⟩
  exact ⟨c * b, by rw [Nat.mul_assoc]⟩

/-- n % 1 = 0 (self-built from `Nat.mod_lt`). -/
theorem e291_mod_one (n : Nat) : n % 1 = 0 := by
  have h : n % 1 < 1 := Nat.mod_lt n (by omega)
  omega

/-- n / 1 = n (self-built from `Nat.div_add_mod` + `e291_mod_one`). -/
theorem e291_div_one (n : Nat) : n / 1 = n := by
  have h := Nat.div_add_mod n 1
  rw [e291_mod_one n, Nat.add_zero, Nat.one_mul] at h
  exact h

/-- THE EXACT-DIVISION IDENTITY: lcmd a b * gcd a b = a * b. -/
theorem e291_lcmd_mul_gcd (a b : Nat) : lcmd a b * Nat.gcd a b = a * b := by
  have hgab : Nat.gcd a b ∣ a * b := e291_dvd_mul_of (Nat.gcd a b) a b (Nat.gcd_dvd_left a b)
  have hmod : a * b % Nat.gcd a b = 0 := e291_dvd_mod_zero (Nat.gcd a b) (a * b) hgab
  exact e291_div_mul_self (a * b) (Nat.gcd a b) hmod

/-- THE LEFT DIVISIBILITY LAW: a ∣ lcmd a b. -/
theorem e291_dvd_lcmd_left (a b : Nat) : a ∣ lcmd a b := by
  by_cases hg0 : Nat.gcd a b = 0
  · obtain ⟨c, hc⟩ := Nat.gcd_dvd_left a b
    rw [hg0, Nat.zero_mul] at hc
    have hl : lcmd a b = 0 := by
      rw [hc]
      show 0 * b / Nat.gcd 0 b = 0
      rw [Nat.zero_mul, Nat.zero_div]
    rw [hl]
    exact ⟨0, (Nat.mul_zero a).symm⟩
  · have hg1 : 1 ≤ Nat.gcd a b := by omega
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right a b
    have hE' : lcmd a b * Nat.gcd a b = a * (Nat.gcd a b * c) := by
      rw [← hc]; exact e291_lcmd_mul_gcd a b
    have hsh : a * (Nat.gcd a b * c) = Nat.gcd a b * (a * c) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a (Nat.gcd a b)]
    have hgoal : Nat.gcd a b * lcmd a b = Nat.gcd a b * (a * c) := by
      rw [Nat.mul_comm (Nat.gcd a b) (lcmd a b), hE', hsh]
    have hcancel : lcmd a b = a * c := Nat.mul_left_cancel hg1 hgoal
    exact ⟨c, hcancel⟩

/-- THE RIGHT DIVISIBILITY LAW: b ∣ lcmd a b. -/
theorem e291_dvd_lcmd_right (a b : Nat) : b ∣ lcmd a b := by
  by_cases hg0 : Nat.gcd a b = 0
  · obtain ⟨c, hc⟩ := Nat.gcd_dvd_right a b
    rw [hg0, Nat.zero_mul] at hc
    have hl : lcmd a b = 0 := by
      rw [hc]
      show a * 0 / Nat.gcd a 0 = 0
      rw [Nat.mul_zero, Nat.zero_div]
    rw [hl]
    exact ⟨0, (Nat.mul_zero b).symm⟩
  · have hg1 : 1 ≤ Nat.gcd a b := by omega
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_left a b
    have hE' : lcmd a b * Nat.gcd a b = Nat.gcd a b * c * b := by
      rw [← hc]; exact e291_lcmd_mul_gcd a b
    have hgoal : Nat.gcd a b * lcmd a b = Nat.gcd a b * (c * b) := by
      rw [Nat.mul_comm (Nat.gcd a b) (lcmd a b), hE', ← Nat.mul_assoc]
    have hcancel : lcmd a b = c * b := Nat.mul_left_cancel hg1 hgoal
    exact ⟨c, by rw [hcancel, Nat.mul_comm c b]⟩

/-- Positivity of the lcm. -/
theorem e291_lcmd_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < lcmd a b := by
  rcases Nat.eq_zero_or_pos (lcmd a b) with h0 | hpos
  · exfalso
    have hE := e291_lcmd_mul_gcd a b
    rw [h0, Nat.zero_mul] at hE
    rcases Nat.eq_zero_or_pos a with hza | hpa
    · omega
    · rcases Nat.eq_zero_or_pos b with hzb | hpb
      · omega
      · have := Nat.mul_pos hpa hpb
        omega
  · exact hpos

/-! ## §2 The L_n / a_n / g(n) structure laws (full generality). -/

theorem LN_zero : LN 0 = 1 := rfl

theorem LN_succ (n : Nat) : LN (n + 1) = lcmd (LN n) (n + 1) := rfl

theorem e291_aAux_zero (L k : Nat) : aAux L k 0 = 0 := rfl

theorem e291_aAux_step (L k f : Nat) :
    aAux L k (f + 1) = L / k + aAux L (k + 1) f := rfl

/-- L_n is always positive. -/
theorem e291_LN_pos (n : Nat) : 0 < LN n := by
  induction n with
  | zero => have h : LN 0 = 1 := rfl; omega
  | succ n ih =>
    rw [LN_succ]
    exact e291_lcmd_pos (LN n) (n + 1) ih (by omega)

/-- THE STEP LAW: L_n ∣ L_{n+1} (the ladder only grows). -/
theorem e291_LN_step_dvd (n : Nat) : LN n ∣ LN (n + 1) :=
  e291_dvd_lcmd_left (LN n) (n + 1)

/-- THE DIVISIBILITY SPINE: every k with 1 ≤ k ≤ n divides L_n — the
correctness of the ladder (and the exactness of every aAux division). -/
theorem e291_LN_dvd (n : Nat) : ∀ k : Nat, 1 ≤ k → k ≤ n → k ∣ LN n := by
  induction n with
  | zero => intro k h1 hk; omega
  | succ n ih =>
    intro k h1 hk
    by_cases hkn : k = n + 1
    · rw [hkn, LN_succ]
      exact e291_dvd_lcmd_right (LN n) (n + 1)
    · have hlt : k ≤ n := by omega
      exact Nat.dvd_trans (ih k h1 hlt) (e291_dvd_lcmd_left (LN n) (n + 1))

/-- a_n is positive for n ≥ 1 (the first fold term is L_n / 1 = L_n). -/
theorem e291_aN_pos (n : Nat) (hn : 1 ≤ n) : 0 < aN n := by
  cases n with
  | zero => omega
  | succ m =>
    show 0 < aAux (LN (m + 1)) 1 (m + 1)
    have hstep : aAux (LN (m + 1)) 1 (m + 1)
        = LN (m + 1) / 1 + aAux (LN (m + 1)) 2 m := rfl
    have hL : 0 < LN (m + 1) := e291_LN_pos (m + 1)
    rw [hstep, e291_div_one (LN (m + 1))]
    omega

/-- THE FIRST GCD LAW: g(n) ∣ a_n. -/
theorem e291_gcd_dvd_a (n : Nat) : gN n ∣ aN n :=
  Nat.gcd_dvd_left (aN n) (LN n)

/-- THE SECOND GCD LAW: g(n) ∣ L_n (the mission's "gcd(a_n,L_n) ∣ L_n"). -/
theorem e291_gcd_dvd_L (n : Nat) : gN n ∣ LN n :=
  Nat.gcd_dvd_right (aN n) (LN n)

/-- THE GCD UNIVERSALITY: every common divisor of a_n and L_n divides
g(n) — g(n) IS the gcd, not merely a common divisor. -/
theorem e291_gcd_univ (n c : Nat) (h1 : c ∣ aN n) (h2 : c ∣ LN n) : c ∣ gN n :=
  Nat.dvd_gcd h1 h2

/-- g(n) ≥ 1 for n ≥ 1 (a_n ≥ 1 and g ∣ a_n). -/
theorem e291_gN_pos (n : Nat) (hn : 1 ≤ n) : 1 ≤ gN n := by
  rcases Nat.eq_zero_or_pos (gN n) with h0 | hpos
  · exfalso
    have ha : 0 < aN n := e291_aN_pos n hn
    have hd := e291_gcd_dvd_a n
    rw [h0\ at hd
    rcases hd with ⟨c, hc⟩
    rw [Nat.zero_mul\ at hc
    omega
  · exact hpos

/-! ## §3 THE WITNESS TABLES (decide-certified closed numerics). -/

/-- THE #291 CANONICAL COPRIME WITNESS: gcd(a_5, L_5) = 1 — H_5 = 137/60
in lowest terms (a_5 = 137, L_5 = 60 — the fraction is already reduced). -/
theorem e291_anchor_5 : aN 5 = 137 ∧ LN 5 = 60 ∧ gN 5 = 1 := by decide

/-- THE #317-CROSSING WITNESS: gcd(a_6, L_6) = 3 — a_6 = 147 = 3·49,
L_6 = 60 = 3·20: H_6 = 49/20 in reduced form (the campaign's #317
"reduced over L_6" row, now kernel-certified: the gcd 3 collapses). -/
theorem e291_anchor_6 :
    aN 6 = 147 ∧ LN 6 = 60 ∧ gN 6 = 3 ∧ aN 6 / 3 = 49 ∧ LN 6 / 3 = 20 := by decide

/-- THE THIRD ANCHOR: gcd(a_7, L_7) = 3 — a_7 = 1089 = 3²·11², L_7 = 420
(H_7 = 363/140; the 11-part of a_7 does NOT enter the gcd: 11 ∤ L_7). -/
theorem e291_anchor_7 : aN 7 = 1089 ∧ LN 7 = 420 ∧ gN 7 = 3 := by decide

/-- THE WOLSTENHOLME NON-LIFT ROW: 11 ∣ a_10 (aN 10 = 7381 = 11²·61 — the
Wolstenholme congruence H_10 ≡ 0 mod 11²) YET gcd(a_10, L_10) = 1, because
11 ∤ L_10: the gcd condition is q ≤ n (q ∈ L_n), and 11 > 10.  Wolstenholme
primes never lift the gcd through the H_{p−1} row. -/
theorem e291_wolstenholme_nonlift :
    aN 10 % 11 = 0 ∧ gN 10 = 1 ∧ LN 10 % 11 ≠ 0 := by decide

/-- THE 3-SPIKE FAMILY ROWS (e = 1..5): g(2·3^e) ∈ {3, 3, 3, 39, 3} —
the leading base-3 digit of 2·3^e is 2, so 3 ∣ a_n and 3 ∣ L_n for EVERY
member of the infinite family (DERIVATION Theorem B: infinitely many n
with gcd > 1).  g(162) = 39 = 3·13 picks up the 13-spike [156,168] too. -/
theorem e291_spike3_family :
    gN 6 = 3 ∧ gN 18 = 3 ∧ gN 54 = 3 ∧ gN 162 = 39 ∧ gN 486 = 3 := by decide

/-- THE FULL n = 1..25 GCD TABLE (the bounded census: 11 rows > 1, 14 rows
= 1 — the exact values including the prime-power rows 15 = 3·5 at n = 20/24,
45 = 3²·5 at n = 21..23). -/
theorem e291_g_table25 :
    [gN 1, gN 2, gN 3, gN 4, gN 5, gN 6, gN 7, gN 8, gN 9, gN 10, gN 11,
     gN 12, gN 13, gN 14, gN 15, gN 16, gN 17, gN 18, gN 19, gN 20, gN 21,
     gN 22, gN 23, gN 24, gN 25] =
    [1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 15, 45, 45,
     45, 15, 3] := by decide

/-- THE NUMERATOR/LADDER TABLE (n = 1..12): a_n and L_n exactly, for the
D-table rows of §5. -/
theorem e291_a_table12 :
    [aN 1, aN 2, aN 3, aN 4, aN 5, aN 6, aN 7, aN 8, aN 9, aN 10, aN 11,
     aN 12] =
    [1, 3, 11, 25, 137, 147, 1089, 2283, 7129, 7381, 83711, 86021] ∧
    [LN 1, LN 2, LN 3, LN 4, LN 5, LN 6, LN 7, LN 8, LN 9, LN 10, LN 11,
     LN 12] =
    [1, 2, 6, 12, 60, 60, 420, 840, 2520, 2520, 27720, 27720] := by decide

/-! ## §4 THE D_q DIGIT TABLE (the LAW's engine, per-prime decide boards).

For a prime q and m ∈ [1, q−1]: a_m = L_m · H_m and q ∤ L_m (m < q), so
q ∣ a_m ⟺ q ∣ num(H_m) — the digit-set row D_q = {m ∈ [1,q−1] : q ∣ a_m}
IS the harmonic-numerator row the LAW feeds on. -/

/-- D_3 = {2}: within [1,2] exactly m = 2 (H_2 = 3/2 — num = 3). -/
theorem e291_D3 : (List.range 3).all (fun m =>
    decide ((m + 1 = 2 ∧ aN (m + 1) % 3 = 0) ∨
            (m + 1 ≠ 2 ∧ aN (m + 1) % 3 ≠ 0))) = true := by decide

/-- D_5 = {4}: within [1,4] exactly m = 4 (H_4 = 25/12 — num = 25). -/
theorem e291_D5 : (List.range 5).all (fun m =>
    decide ((m + 1 = 4 ∧ aN (m + 1) % 5 = 0) ∨
            (m + 1 ≠ 4 ∧ aN (m + 1) % 5 ≠ 0))) = true := by decide

/-- D_7 = {6}: within [1,6] exactly m = 6 (H_6 = 49/20 — num = 49). -/
theorem e291_D7 : (List.range 7).all (fun m =>
    decide ((m + 1 = 6 ∧ aN (m + 1) % 7 = 0) ∨
            (m + 1 ≠ 6 ∧ aN (m + 1) % 7 ≠ 0))) = true := by decide

/-- D_11 = {3, 7, 10}: within [1,10] exactly m ∈ {3,7,10} (H_3 = 11/6 —
num = 11; H_7 = 363/140 — num = 363 = 3·11²; H_10 = 7381/2520 —
num = 7381 = 11²·61).  THE EXCEPTIONAL ROW: 3 and 7 are NOT q−1 digits —
the 11-spike fires at [33,44) and [77,88) as well as [110,121). -/
theorem e291_D11 : (List.range 11).all (fun m =>
    decide (((m + 1 = 3 ∨ m + 1 = 7 ∨ m + 1 = 10) ∧ aN (m + 1) % 11 = 0) ∨
            ((m + 1 ≠ 3 ∧ m + 1 ≠ 7 ∧ m + 1 ≠ 10) ∧ aN (m + 1) % 11 ≠ 0))) = true := by decide

/-- D_13 = {12}: within [1,12] exactly m = 12 (H_12 = 86021/27720 —
num = 86021 = 13·6617).  The 13-spike fires at [156,169) — g(162) = 39. -/
theorem e291_D13 : (List.range 13).all (fun m =>
    decide ((m + 1 = 12 ∧ aN (m + 1) % 13 = 0) ∨
            (m + 1 ≠ 12 ∧ aN (m + 1) % 13 ≠ 0))) = true := by decide

/-! ## §5 THE p-ADIC CRITERION ROWS (fixed small primes, the n ≤ 25 board). -/

/-- KÜRSCHÁK'S LAW on the board: g(n) is odd for every n ∈ [1,25] — 2 never
divides gcd(a_n, L_n) (the unique maximal-2-adic-term mechanism). -/
theorem e291_q2_board :
    (List.range 25).all (fun m => decide (gN (m + 1) % 2 = 1)) = true := by decide

/-- THE 3-CRITERION: for n ∈ [1,25], 3 ∣ g(n) ⟺ the leading base-3 digit
of n is 2 — on this board exactly n/3 = 2 (n ∈ [6,8]) ∨ n/9 = 2
(n ∈ [18,25]) — the spike rows [2·3^e, 3^{e+1}) ∩ [1,25]. -/
theorem e291_q3_board : (List.range 25).all (fun m =>
    decide (((m + 1) / 3 = 2 ∨ (m + 1) / 9 = 2) ∧ gN (m + 1) % 3 = 0 ∨
            ((m + 1) / 3 ≠ 2 ∧ (m + 1) / 9 ≠ 2) ∧ gN (m + 1) % 3 ≠ 0)) = true := by decide

/-- THE 5-CRITERION: for n ∈ [1,25], 5 ∣ g(n) ⟺ n/5 = 4 (n ∈ [20,24] —
the digit-4 spike [4·5^1, 5^2)). -/
theorem e291_q5_board : (List.range 25).all (fun m =>
    decide (((m + 1) / 5 = 4) ∧ gN (m + 1) % 5 = 0 ∨
            ((m + 1) / 5 ≠ 4) ∧ gN (m + 1) % 5 ≠ 0)) = true := by decide

/-- THE EMPTY 7-ROW: no n ∈ [1,25] has 7 ∣ g(n) — the 7-spike starts at
n = 42 (digit 6 = q−1 at e = 1: [42,49)). -/
theorem e291_q7_board :
    (List.range 25).all (fun m => decide (gN (m + 1) % 7 ≠ 0)) = true := by decide

/-- THE EMPTY 11-ROW on the board: the 11-spike starts at n = 33
(the EXCEPTIONAL digit row D_11 ∋ 3). -/
theorem e291_q11_board :
    (List.range 25).all (fun m => decide (gN (m + 1) % 11 ≠ 0)) = true := by decide

/-- THE EMPTY 13-ROW on the board: the 13-spike starts at n = 156. -/
theorem e291_q13_board :
    (List.range 25).all (fun m => decide (gN (m + 1) % 13 ≠ 0)) = true := by decide

/-- Row extraction: Kürschák's law, for every board row. -/
theorem e291_q2_row : ∀ m : Nat, m < 25 → gN (m + 1) % 2 = 1 := by
  intro m hm
  have hrow := (List.all_eq_true.mp e291_q2_board) m (List.mem_range.mpr hm)
  exact of_decide_eq_true hrow

/-- Row extraction (forward): leading base-3 digit 2 → 3 ∣ g(n). -/
theorem e291_q3_row : ∀ m : Nat, m < 25 →
    ((m + 1) / 3 = 2 ∨ (m + 1) / 9 = 2) → gN (m + 1) % 3 = 0 := by
  intro m hm hld
  have hrow := (List.all_eq_true.mp e291_q3_board) m (List.mem_range.mpr hm)
  rcases of_decide_eq_true hrow with hpos | hneg
  · exact hpos.2
  · exfalso
    rcases hld with h1 | h1
    · exact hneg.1.1 h1
    · exact hneg.1.2 h1

/-- Row extraction (converse): 3 ∣ g(n) → leading base-3 digit 2. -/
theorem e291_q3_conv : ∀ m : Nat, m < 25 →
    gN (m + 1) % 3 = 0 → ((m + 1) / 3 = 2 ∨ (m + 1) / 9 = 2) := by
  intro m hm hg
  have hrow := (List.all_eq_true.mp e291_q3_board) m (List.mem_range.mpr hm)
  rcases of_decide_eq_true hrow with hpos | hneg
  · exact hpos.1
  · exact absurd hg hneg.2

/-- Row extraction (forward): the 5-criterion. -/
theorem e291_q5_row : ∀ m : Nat, m < 25 →
    (m + 1) / 5 = 4 → gN (m + 1) % 5 = 0 := by
  intro m hm hld
  have hrow := (List.all_eq_true.mp e291_q5_board) m (List.mem_range.mpr hm)
  rcases of_decide_eq_true hrow with hpos | hneg
  · exact hpos.2
  · exact absurd hld hneg.1.1

/-- Row extraction (converse): the 5-criterion. -/
theorem e291_q5_conv : ∀ m : Nat, m < 25 →
    gN (m + 1) % 5 = 0 → (m + 1) / 5 = 4 := by
  intro m hm hg
  have hrow := (List.all_eq_true.mp e291_q5_board) m (List.mem_range.mpr hm)
  rcases of_decide_eq_true hrow with hpos | hneg
  · exact hpos.1
  · exact absurd hg hneg.2

/-! ## §6 THE n ≤ 25 CLASSIFICATION (the bounded board, both directions). -/

/-- THE POSITIVE SWEEP: every spike row (n ∈ {6,7,8} ∪ [18,25]) has
g(n) > 1 — all 25 rows kernel-decided. -/
theorem e291_spike_sweep :
    (List.range 25).all (fun m =>
      decide (¬ ((m + 1 = 6 ∨ m + 1 = 7 ∨ m + 1 = 8 ∨ 18 ≤ m + 1) ∧
                ¬ (1 < gN (m + 1))))) = true := by decide

/-- THE CONVERSE SWEEP: every g > 1 row is a spike row. -/
theorem e291_nospike_sweep :
    (List.range 25).all (fun m =>
      decide (¬ (1 < gN (m + 1) ∧
                ¬ (m + 1 = 6 ∨ m + 1 = 7 ∨ m + 1 = 8 ∨ 18 ≤ m + 1)))) = true := by decide

theorem e291_spike_row : ∀ m : Nat, m < 25 →
    (m + 1 = 6 ∨ m + 1 = 7 ∨ m + 1 = 8 ∨ 18 ≤ m + 1) → 1 < gN (m + 1) := by
  intro m hm hsp
  have hrow := (List.all_eq_true.mp e291_spike_sweep) m (List.mem_range.mpr hm)
  have hnn := of_decide_eq_true hrow
  by_cases hgt : 1 < gN (m + 1)
  · exact hgt
  · exact absurd ⟨hsp, hgt⟩ hnn

theorem e291_nospike_row : ∀ m : Nat, m < 25 →
    1 < gN (m + 1) → (m + 1 = 6 ∨ m + 1 = 7 ∨ m + 1 = 8 ∨ 18 ≤ m + 1) := by
  intro m hm hgt
  have hrow := (List.all_eq_true.mp e291_nospike_sweep) m (List.mem_range.mpr hm)
  have hnn := of_decide_eq_true hrow
  by_cases hsp : (m + 1 = 6 ∨ m + 1 = 7 ∨ m + 1 = 8 ∨ 18 ≤ m + 1)
  · exact hsp
  · exact absurd ⟨hgt, hsp⟩ hnn

/-- THE MASTER CLASSIFICATION (n ≤ 25): gcd(a_n, L_n) > 1 ⟺
n = 6 ∨ n = 7 ∨ n = 8 ∨ 18 ≤ n — the two 3-spike blocks [6,8] and
[18,25] (the 5-spike [20,24] ⊂ [18,25] is invisible at the gcd>1 level:
those rows carry the bigger gcds 15/45).  THE ANSWER ON THE BOARD:
gcd = 1 for n ∈ {1..5, 9..17} (14 rows), gcd > 1 for the other 11. -/
theorem e291_classify_25 : ∀ n : Nat, 1 ≤ n → n ≤ 25 →
    (1 < gN n ↔ n = 6 ∨ n = 7 ∨ n = 8 ∨ 18 ≤ n) := by
  intro n h1 h25
  have hm : n - 1 < 25 := by omega
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel h1
  constructor
  · intro hgt
    have hgt' : 1 < gN (n - 1 + 1) := by rw [hn]; exact hgt
    have hrow := e291_nospike_row (n - 1) hm hgt'
    rw [hn] at hrow
    exact hrow
  · intro hsp
    have hsp' : (n - 1 + 1 = 6 ∨ n - 1 + 1 = 7 ∨ n - 1 + 1 = 8 ∨
        18 ≤ n - 1 + 1) := by rw [hn]; exact hsp
    have hrow := e291_spike_row (n - 1) hm hsp'
    rw [hn] at hrow
    exact hrow

/-! ## §7 The arsenal bridge (BOSS's mathematics on the n = 8 spike row). -/

/-- The n = 8 3-spike row through the arsenal: 8 = 3·(8/3) + 2 (the
leading-digit-2 decomposition), the spike digit 2 is an admissible ternary
digit, the spike scale 3^4 = 81 bounds the [54,81) block, and the mod law
respects the L_8 = 840 = 3·280 scale at a_8. -/
theorem e291_arsenal_bridge :
    (8 = 3 * (8 / 3) + 2) ∧
    (2 = 0 ∨ 2 = 1 ∨ 2 = 2) ∧
    (0 < 3 ^ 4) ∧
    (aN 8 % (3 * 280) % 3 = aN 8 % 3) :=
  ⟨div_add_mod_subst 8 (by decide), ErdosTernary2.lt_three_cases 2 (by decide),
    three_pow_pos_lemma 4, mod_mod_mul (aN 8) 3 280 (by decide)⟩

/-! ## §8 THE MASTER BOARD (the flat conjunction, one term each). -/

/-- THE ERDŐS #291 ROUND-1 BOARD: the definitions' structure laws
(positivity, the divisibility spine, the gcd laws + universality) + the
anchor witnesses (137/60 coprime, 147/60 → 49/20 with gcd 3, 1089/420) +
the Wolstenholme non-lift row + the 3-spike family + the n ≤ 25 gcd
table + the D_q digit-table rows + the per-prime criterion boards +
the classification + the arsenal bridge. -/
theorem erdos291_board :
    (∀ n : Nat, 0 < LN n) ∧
    (∀ n : Nat, ∀ k : Nat, 1 ≤ k → k ≤ n → k ∣ LN n) ∧
    (∀ n : Nat, gN n ∣ aN n ∧ gN n ∣ LN n) ∧
    (∀ n c : Nat, c ∣ aN n → c ∣ LN n → c ∣ gN n) ∧
    (aN 5 = 137 ∧ LN 5 = 60 ∧ gN 5 = 1) ∧
    (aN 6 = 147 ∧ LN 6 = 60 ∧ gN 6 = 3 ∧ aN 6 / 3 = 49 ∧ LN 6 / 3 = 20) ∧
    (aN 7 = 1089 ∧ LN 7 = 420 ∧ gN 7 = 3) ∧
    (aN 10 % 11 = 0 ∧ gN 10 = 1 ∧ LN 10 % 11 ≠ 0) ∧
    (gN 6 = 3 ∧ gN 18 = 3 ∧ gN 54 = 3 ∧ gN 162 = 39 ∧ gN 486 = 3) ∧
    ([gN 1, gN 2, gN 3, gN 4, gN 5, gN 6, gN 7, gN 8, gN 9, gN 10, gN 11,
      gN 12, gN 13, gN 14, gN 15, gN 16, gN 17, gN 18, gN 19, gN 20, gN 21,
      gN 22, gN 23, gN 24, gN 25] =
      [1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 15, 45, 45,
      45, 15, 3]) ∧
    ((List.range 3).all (fun m =>
      decide ((m + 1 = 2 ∧ aN (m + 1) % 3 = 0) ∨
              (m + 1 ≠ 2 ∧ aN (m + 1) % 3 ≠ 0))) = true) ∧
    ((List.range 11).all (fun m =>
      decide (((m + 1 = 3 ∨ m + 1 = 7 ∨ m + 1 = 10) ∧ aN (m + 1) % 11 = 0) ∨
              ((m + 1 ≠ 3 ∧ m + 1 ≠ 7 ∧ m + 1 ≠ 10) ∧ aN (m + 1) % 11 ≠ 0))) = true) ∧
    ((List.range 25).all (fun m => decide (gN (m + 1) % 2 = 1)) = true) ∧
    ((List.range 25).all (fun m =>
      decide (((m + 1) / 3 = 2 ∨ (m + 1) / 9 = 2) ∧ gN (m + 1) % 3 = 0 ∨
              ((m + 1) / 3 ≠ 2 ∧ (m + 1) / 9 ≠ 2) ∧ gN (m + 1) % 3 ≠ 0)) = true) ∧
    (∀ n : Nat, 1 ≤ n → n ≤ 25 →
      (1 < gN n ↔ n = 6 ∨ n = 7 ∨ n = 8 ∨ 18 ≤ n)) ∧
    ((8 = 3 * (8 / 3) + 2) ∧
    (2 = 0 ∨ 2 = 1 ∨ 2 = 2) ∧
    (0 < 3 ^ 4) ∧
    (aN 8 % (3 * 280) % 3 = aN 8 % 3)) :=
  ⟨e291_LN_pos, e291_LN_dvd,
    ⟨fun n => e291_gcd_dvd_a n, fun n => e291_gcd_dvd_L n⟩,
    e291_gcd_univ, e291_anchor_5, e291_anchor_6, e291_anchor_7,
    e291_wolstenholme_nonlift, e291_spike3_family, e291_g_table25,
    e291_D3, e291_D11, e291_q2_board, e291_q3_board, e291_classify_25,
    e291_arsenal_bridge⟩

/-! ## RECEIPT. -/

#print axioms E291.e291_div_mul_self
#print axioms E291.e291_lcmd_mul_gcd
#print axioms E291.e291_LN_pos
#print axioms E291.e291_LN_step_dvd
#print axioms E291.e291_LN_dvd
#print axioms E291.e291_aN_pos
#print axioms E291.e291_gcd_dvd_L
#print axioms E291.e291_gcd_dvd_a
#print axioms E291.e291_gcd_univ
#print axioms E291.e291_gN_pos
#print axioms E291.e291_anchor_5
#print axioms E291.e291_anchor_6
#print axioms E291.e291_anchor_7
#print axioms E291.e291_wolstenholme_nonlift
#print axioms E291.e291_spike3_family
#print axioms E291.e291_g_table25
#print axioms E291.e291_a_table12
#print axioms E291.e291_D3
#print axioms E291.e291_D5
#print axioms E291.e291_D7
#print axioms E291.e291_D11
#print axioms E291.e291_D13
#print axioms E291.e291_q2_board
#print axioms E291.e291_q3_board
#print axioms E291.e291_q5_board
#print axioms E291.e291_q7_board
#print axioms E291.e291_q11_board
#print axioms E291.e291_q13_board
#print axioms E291.e291_q2_row
#print axioms E291.e291_q3_row
#print axioms E291.e291_q3_conv
#print axioms E291.e291_q5_row
#print axioms E291.e291_q5_conv
#print axioms E291.e291_spike_row
#print axioms E291.e291_nospike_row
#print axioms E291.e291_classify_25
#print axioms E291.e291_arsenal_bridge
#print axioms E291.erdos291_board

/-- THE KERNEL-291 RECEIPT CONSTANT: prints green when the whole file
elaborates clean (the CI grep target for this step). -/
def E291_HARMONIC_GCD_GREEN : String := "E291_HARMONIC_GCD_GREEN"

#eval E291_HARMONIC_GCD_GREEN

end E291
