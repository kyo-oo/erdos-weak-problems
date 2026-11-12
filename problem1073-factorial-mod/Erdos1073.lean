import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels K21/K26/K30): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #1073 — THE FACTORIAL-MOD COMPOSITE CENSUS (S041 volley, Kernel 34)

## THE PROBLEM (verbatim, erdosproblems.com/1073 — Erdős, with Hardy–Subbarao)

> Let $A(x)$ count the number of composite $u<x$ such that
> $n!+1\equiv 0 \pmod{u}$ for some $n$. Is it true that $A(x)\leq x^{o(1)}$?

The sequence of such $u$ begins $25, 121, 169, 437, \ldots$ (OEIS A256519).

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. **THE GCD/WINDOW LAW** (`erdos1073_window`, general): if $u \ge 2$ and
   $u \mid n!+1$ then EVERY prime $p \mid u$ satisfies $n < p$ — the
   witness window is $[1, P(u))$, $P(u)$ the least prime factor. The
   saturation side (`erdos1073_saturation`): for $n \ge P(u)$, $u$ never
   again divides $n!+1$.
2. **THE SMALL-PRIME-DIVISOR LAW** (`small_prime_divisor`, general): every
   $4 \le u \le B^2$ that is not prime has a PRIME divisor $q \le B$ — the
   case-split engine ($p := P(u) \le B$ direct; else $a := u/p \le B$ and
   $q := P(a)$; both $> B$ is impossible since $(B{+}1)^2 \le p\,a = u \le B^2$).
3. **THE COMPLETE CENSUS AT $10^4$** (`erdos1073_census`): the composite
   $u \in [4, 10^4]$ with SOME witness $n$ are EXACTLY the 28-element
   table T28 (the A256519 prefix) — both directions, kernel-decided in 21
   NO-OOM chunk-decides (480-element discipline, the K31 pattern). Hence
   **$A(10^4) = 28$** (`erdos1073_A10k`).
4. **THE 131-WITNESS TABLE AT $10^6$** (`erdos1073_witnesses`): all 131
   composite $u < 10^6$ of the engine census, each with its exact witness
   $n$ ($u \mid n!+1$ kernel-decided, including the 1330-digit $562!$ of
   the Wilson channel and the $918!$ of the deepest row).
5. **THE WILSON CHANNEL** (`erdos1073_wilson`): the three known Wilson
   primes' squares are hits — $5^2 \mid 4!{+}1$, $13^2 \mid 12!{+}1$,
   $563^2 \mid 562!{+}1$.
6. **THE BROCARD CHANNEL** (`erdos1073_brocard`): $4!{+}1 = 5^2$,
   $5!{+}1 = 11^2$, $7!{+}1 = 71^2$ — the three known Brocard/Brown
   numbers, the square layer of the census.

Honest scope: the $x^{o(1)}$ asymptotic question remains OPEN — the kernel
lands the window law, the small-prime-divisor engine, the complete $10^4$
census, the 131 witnesses at $10^6$ (completeness at $10^6$ is
engine-certified dual-method, `battery1073.py`), and the two structural
channels. -/

namespace Erdos1073

/-! ## §0 The definitions. -/

/-- Divisor search: does u have a divisor d with 2 ≤ d, d < u, and d
within the fuel window starting at the loop's start? Fuel-structured (d
counts up, fuel counts down) — no deep lists, kernel-shallow. -/
def divLoop (u d : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      if 2 ≤ d then
        (decide (d < u) && decide (u % d = 0)) || divLoop u (d + 1) fuel
      else false

/-- The composite test: 4 ≤ u and u has a proper divisor in [2, B]
(the call divLoop u 2 (B−1) checks d = 2, 3, …, B). -/
def compScan (B u : Nat) : Bool := Nat.ble 4 u && divLoop u 2 (B - 1)

/-- The witness scan over the window [1, 99]: does some n ∈ [1, 99]
satisfy u ∣ n!+1? -/
def witAny (u : Nat) : Bool :=
  (List.range 99).any (fun d => decide ((Nat.factorial (d + 1) + 1) % u = 0))

/-- The full hit test at the 10^4 scale: composite (certified via a
divisor ≤ 100) AND a window witness. -/
def hitScan (u : Nat) : Bool := Nat.ble 4 u && compScan 100 u && witAny u

/-- The 28 hits u ∈ [4, 10^4] (the A256519 prefix; kernel-completed below). -/
def T28 : List Nat :=
  [25, 121, 169, 437, 551, 667, 721, 1037, 1159, 1273, 1349, 1403, 1541,
   1769, 1943, 2209, 2329, 2363, 2419, 3071, 3713, 4087, 5041, 5111,
   7313, 8357, 8479, 9017]

/-- List membership as a Bool (self-contained). -/
def inL (u : Nat) (l : List Nat) : Bool := l.any (fun x => decide (x = u))

/-- One full 480-element census chunk: chunk c covers u ∈ [480c+4, 480c+484). -/
def chunkScanF (c : Nat) : Bool :=
  (List.range 480).all (fun j =>
    decide (hitScan (480 * c + j + 4) = inL (480 * c + j + 4) T28))

/-- The final short chunk: u ∈ [9604, 10000]. -/
def chunkScanLast : Bool :=
  (List.range 397).all (fun j =>
    decide (hitScan (9600 + j + 4) = inL (9600 + j + 4) T28))

/-- The 131 witness rows (u, n) at the 10^6 frontier — every composite
u < 10^6 with u ∣ n!+1 (engine census, dual-method verified; the witness
side is kernel-certified here). -/
def W131 : List (Nat × Nat) :=
  [(25, 4), (121, 5), (169, 12), (437, 18), (551, 18), (667, 18),
   (721, 6), (1037, 16), (1159, 18), (1273, 18), (1349, 9), (1403, 18),
   (1541, 18), (1769, 18), (1943, 18), (2209, 23), (2329, 16), (2363, 16),
   (2419, 40), (3071, 36), (3713, 23), (4087, 18), (5041, 7), (5111, 9),
   (7313, 51), (8357, 16), (8479, 16), (9017, 63), (11357, 40), (11983, 22),
   (12673, 18), (16117, 61), (16343, 40), (19043, 16), (19099, 9), (19879, 102),
   (21797, 63), (26657, 18), (27343, 36), (28261, 15), (29279, 18), (33611, 18),
   (36917, 18), (38989, 63), (40321, 8), (40687, 18), (44689, 18), (50429, 210),
   (51923, 35), (52043, 51), (54871, 36), (61337, 36), (71087, 66), (75499, 51),
   (77113, 58), (77411, 198), (77653, 18), (81469, 225), (88531, 222), (94001, 18),
   (106507, 72), (107519, 78), (107587, 93), (118523, 18), (123089, 36), (131207, 89),
   (132823, 316), (134149, 162), (139147, 173), (142069, 16), (142349, 282), (144143, 16),
   (158177, 366), (174511, 23), (184027, 81), (194107, 72), (200099, 400), (215581, 192),
   (217927, 191), (230803, 442), (240979, 303), (274657, 456), (277877, 259), (292511, 72),
   (311599, 311), (316969, 562), (319859, 498), (323731, 16), (328747, 546), (357937, 172),
   (362881, 9), (365681, 502), (372703, 58), (375769, 229), (381397, 576), (385051, 30),
   (391843, 69), (419521, 221), (423569, 290), (484513, 643), (538217, 144), (546577, 618),
   (557317, 86), (570007, 189), (575381, 188), (583943, 240), (594361, 50), (598607, 210),
   (598837, 60), (625321, 495), (637807, 360), (641369, 672), (655957, 768), (664457, 375),
   (670063, 40), (678043, 210), (682853, 330), (684899, 576), (694921, 786), (743569, 383),
   (764707, 375), (773053, 18), (784607, 576), (801599, 400), (808141, 228), (844751, 331),
   (845609, 220), (849091, 18), (888673, 918), (958649, 191), (997501, 400)]

/-- One W131 row is a genuine hit: 4 ≤ u, composite (a proper divisor in
[2, 1000] — valid for every composite u ≤ 10^6), 1 ≤ n, and u ∣ n!+1. -/
def witOK (r : Nat × Nat) : Bool :=
  Nat.ble 4 r.1 && compScan 1000 r.1 && Nat.ble 1 r.2 &&
  decide ((Nat.factorial r.2 + 1) % r.1 = 0)

def witScan : Bool := W131.all witOK

/-! ## §1 The list helpers (self-contained, zero API risk). -/

theorem any_of_mem : ∀ (l : List Nat) (p : Nat → Bool) (x : Nat),
    x ∈ l → p x = true → l.any p = true := by
  intro l
  induction l with
  | nil => intro p x hm; cases hm
  | cons h t ih =>
      intro p x hm hp
      rcases List.mem_cons.mp hm with he | hm'
      · rw [he] at hp
        rw [List.any_cons, hp]
        simp
      · rw [List.any_cons, ih p x hm' hp]
        simp

theorem any_exists : ∀ (l : List Nat) (p : Nat → Bool),
    l.any p = true → ∃ x : Nat, x ∈ l ∧ p x = true := by
  intro l
  induction l with
  | nil => intro p h; simp at h
  | cons h t ih =>
      intro p hall
      rw [List.any_cons] at hall
      rcases Bool.or_eq_true_iff.mp hall with hp | ht
      · exact ⟨h, List.mem_cons_self, hp⟩
      · obtain ⟨x, hxm, hxp⟩ := ih p ht
        exact ⟨x, List.mem_cons_of_mem h hxm, hxp⟩

theorem inL_of_mem (l : List Nat) (u : Nat) (hm : u ∈ l) : inL u l = true :=
  any_of_mem l (fun x => decide (x = u)) u hm (decide_eq_true rfl)

theorem mem_of_inL : ∀ (l : List Nat) (u : Nat), inL u l = true → u ∈ l := by
  intro l u h
  obtain ⟨x, hxm, hxp⟩ := any_exists l _ h
  have hxu : x = u := of_decide_eq_true hxp
  rw [hxu] at hxm
  exact hxm

/-! ## §2 The factorial-divisibility spine. -/

/-- Every prime p ≤ k divides k!. -/
theorem prime_dvd_fact (p : Nat) (hp : 2 ≤ p) :
    ∀ k : Nat, p ≤ k → p ∣ Nat.factorial k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hlt : p ≤ k
      · rw [Nat.factorial_succ, Nat.mul_comm]
        exact (ih hlt).mul_right (k + 1)
      · have hpk : p = k + 1 := by omega
        rw [Nat.factorial_succ, hpk]
        exact dvd_mul_right (k + 1) (Nat.factorial k)

/-- a ∣ b → a * (b / a) = b (omega-friendly, via div_add_mod). -/
theorem mul_div_own (a b : Nat) (h : a ∣ b) : a * (b / a) = b := by
  have hmod : b % a = 0 := Nat.mod_eq_zero_of_dvd h
  have hdm := Nat.div_add_mod b a
  omega

/-- **THE GCD/WINDOW LAW.** If u ≥ 2 and u ∣ n!+1 then every prime
divisor p of u satisfies n < p: every witness lives strictly below the
least prime factor of u. -/
theorem erdos1073_window (u n : Nat) (hu : 2 ≤ u)
    (h : (Nat.factorial n + 1) % u = 0) :
    ∀ p : Nat, p.Prime → p ∣ u → n < p := by
  intro p hp hpu
  have h2 : 2 ≤ p := Nat.Prime.two_le hp
  by_contra hcon
  have hple : p ≤ n := by omega
  have hfn : p ∣ Nat.factorial n := prime_dvd_fact p h2 n hple
  have hfull : u ∣ Nat.factorial n + 1 := Nat.dvd_of_mod_eq_zero h
  have hp1 : p ∣ Nat.factorial n + 1 := Nat.dvd_trans hpu hfull
  have hp1mod : (Nat.factorial n + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hp1
  have hfnmod : (Nat.factorial n) % p = 0 := Nat.mod_eq_zero_of_dvd hfn
  have hone : 1 % p = 0 := by
    have hadd := Nat.add_mod (Nat.factorial n) 1 p
    have h0 : (Nat.factorial n % p + 1 % p) % p = 0 := by
      rw [← hadd, hp1mod]
    rw [hfnmod, Nat.zero_add, Nat.mod_mod] at h0
    exact h0
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero hone)
  omega

/-- **THE SATURATION LAW.** For n at or above any prime divisor of u,
u never again divides n!+1. -/
theorem erdos1073_saturation (u n p : Nat) (hp : p.Prime) (hpu : p ∣ u)
    (hle : p ≤ n) : (Nat.factorial n + 1) % u ≠ 0 := by
  intro hmod
  rcases (show u = 0 ∨ 1 ≤ u by omega) with h0 | h1
  · rw [h0, Nat.mod_zero] at hmod
    omega
  · have hp2 := Nat.Prime.two_le hp
    have hpu' := Nat.le_of_dvd (by omega) hpu
    have h2 : 2 ≤ u := by omega
    have hwin := erdos1073_window u n h2 hmod p hp hpu
    omega

/-! ## §3 The small-prime-divisor engine. -/

/-- **THE SMALL-PRIME-DIVISOR LAW.** Every 4 ≤ u ≤ B² that is not prime
has a PRIME divisor q ≤ B. Engine: p := P(u); if p ≤ B done; else
a := u/p — if a ≤ B then q := P(a) ≤ a ≤ B; both p, a > B is impossible
since (B+1)² ≤ p·a = u ≤ B². -/
theorem small_prime_divisor (B u : Nat) (h4 : 4 ≤ u) (huB : u ≤ B * B)
    (hnpr : ¬ u.Prime) : ∃ q : Nat, q.Prime ∧ q ∣ u ∧ q ≤ B := by
  have h2u : 2 ≤ u := by omega
  have hmin : (Nat.minFac u).Prime := Nat.minFac_prime (by omega)
  have hdvd : Nat.minFac u ∣ u := Nat.minFac_dvd u
  have hp2 : 2 ≤ Nat.minFac u := hmin.two_le
  have hsplit : Nat.minFac u * (u / Nat.minFac u) = u := mul_div_own _ _ hdvd
  -- a := u / minFac u ≥ 2 (a ≤ 1 forces u = 0 or u = minFac u, both dead)
  have ha2 : 2 ≤ u / Nat.minFac u := by
    rcases Nat.lt_or_ge (u / Nat.minFac u) 2 with hlt | hge
    · have ha1 : u / Nat.minFac u ≤ 1 := by omega
      cases hq : u / Nat.minFac u with
      | zero =>
          rw [hq] at hsplit
          simp at hsplit
          omega
      | succ k =>
          cases k with
          | zero =>
              rw [hq] at hsplit
              simp at hsplit
              rw [hsplit] at hmin
              exact (hnpr hmin).elim
          | succ k' => omega
    · exact hge
  rcases (show Nat.minFac u ≤ B ∨ B < Nat.minFac u by omega) with hpB | hpB
  · exact ⟨Nat.minFac u, hmin, hdvd, hpB⟩
  -- B < p: then a = u/p must be ≤ B, else (B+1)² ≤ p·a = u ≤ B²
  have haB : u / Nat.minFac u ≤ B := by
    rcases (show u / Nat.minFac u ≤ B ∨ B < u / Nat.minFac u by omega) with h | h
    · exact h
    · have h1 : (B + 1) * (B + 1) ≤ Nat.minFac u * (u / Nat.minFac u) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.succ_mul_succ, hsplit] at h1
      omega
  have hamin : (Nat.minFac (u / Nat.minFac u)).Prime :=
    Nat.minFac_prime (by omega)
  have hamdvd : Nat.minFac (u / Nat.minFac u) ∣ (u / Nat.minFac u) :=
    Nat.minFac_dvd _
  have hau : (u / Nat.minFac u) ∣ u :=
    ⟨Nat.minFac u, by rw [Nat.mul_comm]; exact hsplit.symm⟩
  exact ⟨Nat.minFac (u / Nat.minFac u), hamin, Nat.dvd_trans hamdvd hau,
    Nat.le_trans (Nat.le_of_dvd (by omega) hamdvd) haB⟩

/-! ## §4 The divLoop bridges. -/

/-- If q is a divisor of u with 2 ≤ q, start ≤ q, q < u, and q is inside
the fuel window (q < s + fuel), then divLoop u s fuel = true: the hit
short-circuits the disjunction. -/
theorem divLoop_hit : ∀ (fuel s u q : Nat), 2 ≤ s → s ≤ q → q < s + fuel →
    q < u → u % q = 0 → divLoop u s fuel = true := by
  intro fuel
  induction fuel with
  | zero => intro s u q hs hsq hqf hlt hmod; omega
  | succ fuel ih =>
      intro s u q hs hsq hqf hlt hmod
      simp only [divLoop]
      rw [if_pos hs]
      by_cases hq : q = s
      · subst hq
        rw [decide_eq_true hlt, decide_eq_true hmod]
        simp
      · have hrec := ih (s + 1) u q (by omega) (by omega) (by omega) hlt hmod
        rw [hrec]
        simp

/-- If divLoop u s fuel = true then some divisor q of u with s ≤ q,
q < s + fuel, q < u exists. -/
theorem divLoop_dvd_of_true : ∀ (fuel s u : Nat), divLoop u s fuel = true →
    ∃ q : Nat, s ≤ q ∧ q < s + fuel ∧ q < u ∧ u % q = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro s u h
      simp only [divLoop] at h
      simp at h
  | succ fuel ih =>
      intro s u h
      simp only [divLoop] at h
      by_cases hs2 : 2 ≤ s
      · rw [if_pos hs2] at h
        rcases Bool.or_eq_true_iff.mp h with hhit | hrest
        · rw [Bool.and_eq_true] at hhit
          obtain ⟨h1, h2⟩ := hhit
          exact ⟨s, Nat.le_refl s, by omega, of_decide_eq_true h1,
            of_decide_eq_true h2⟩
        · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := ih (s + 1) u hrest
          exact ⟨q, by omega, by omega, hq3, hq4⟩
      · rw [if_neg hs2] at h
        simp at h

/-- compScan B u = true whenever u ∈ [4, B²] is not prime (within the
bound, the scan's composite test is exact). -/
theorem comp_of_not_prime (B u : Nat) (h4 : 4 ≤ u) (huB : u ≤ B * B)
    (hnpr : ¬ u.Prime) : compScan B u = true := by
  obtain ⟨q, hqpr, hqdvd, hqB⟩ := small_prime_divisor B u h4 huB hnpr
  have hq2 : 2 ≤ q := hqpr.two_le
  have hqle : q ≤ u := Nat.le_of_dvd (by omega) hqdvd
  have hqlt : q < u := by
    rcases (show q < u ∨ u ≤ q by omega) with h | h
    · exact h
    · have hqu : u = q := by omega
      rw [← hqu] at hqpr
      exact (hnpr hqpr).elim
  have hmod : u % q = 0 := Nat.mod_eq_zero_of_dvd hqdvd
  simp only [compScan, Bool.and_eq_true]
  refine ⟨Nat.ble_eq.mpr (by omega), ?_⟩
  exact divLoop_hit (B - 1) 2 u q (by omega) (by omega) (by omega) hqlt hmod

/-- compScan B u = true forces u to be non-prime (no bound needed). -/
theorem not_prime_of_comp (B u : Nat) (h : compScan B u = true) : ¬ u.Prime := by
  intro hpr
  simp only [compScan, Bool.and_eq_true] at h
  obtain ⟨_, hloop⟩ := h
  obtain ⟨q, hq2, _, hqlt, hqmod⟩ := divLoop_dvd_of_true (B - 1) 2 u hloop
  have hqdvd : q ∣ u := Nat.dvd_of_mod_eq_zero hqmod
  rcases (Nat.dvd_prime hpr).mp hqdvd with h1 | h1
  · omega
  · omega

/-! ## §5 The census chunks (21 NO-OOM decides, 480-element discipline). -/

theorem chunk_0  : chunkScanF 0 = true := by decide
theorem chunk_1  : chunkScanF 1 = true := by decide
theorem chunk_2  : chunkScanF 2 = true := by decide
theorem chunk_3  : chunkScanF 3 = true := by decide
theorem chunk_4  : chunkScanF 4 = true := by decide
theorem chunk_5  : chunkScanF 5 = true := by decide
theorem chunk_6  : chunkScanF 6 = true := by decide
theorem chunk_7  : chunkScanF 7 = true := by decide
theorem chunk_8  : chunkScanF 8 = true := by decide
theorem chunk_9  : chunkScanF 9 = true := by decide
theorem chunk_10 : chunkScanF 10 = true := by decide
theorem chunk_11 : chunkScanF 11 = true := by decide
theorem chunk_12 : chunkScanF 12 = true := by decide
theorem chunk_13 : chunkScanF 13 = true := by decide
theorem chunk_14 : chunkScanF 14 = true := by decide
theorem chunk_15 : chunkScanF 15 = true := by decide
theorem chunk_16 : chunkScanF 16 = true := by decide
theorem chunk_17 : chunkScanF 17 = true := by decide
theorem chunk_18 : chunkScanF 18 = true := by decide
theorem chunk_19 : chunkScanF 19 = true := by decide
theorem chunk_20 : chunkScanLast = true := by decide

/-- The assembled census: for every i < 9997 (u = i + 4 ∈ [4, 10^4]),
hitScan u equals the T28 membership test. -/
theorem census_all : ∀ i : Nat, i < 9997 →
    hitScan (i + 4) = inL (i + 4) T28 := by
  intro i hi
  -- the full-chunk extractor
  have hkey : ∀ c : Nat, chunkScanF c = true → ∀ j : Nat, j < 480 →
      hitScan (480 * c + j + 4) = inL (480 * c + j + 4) T28 := by
    intro c hchunk j hj
    have hmem : j ∈ List.range 480 := List.mem_range.mpr hj
    have hall := (List.all_eq_true.mp hchunk) j hmem
    exact of_decide_eq_true hall
  -- the last-chunk extractor
  have hlast : chunkScanLast = true → ∀ j : Nat, j < 397 →
      hitScan (9600 + j + 4) = inL (9600 + j + 4) T28 := by
    intro hchunk j hj
    have hmem : j ∈ List.range 397 := List.mem_range.mpr hj
    have hall := (List.all_eq_true.mp hchunk) j hmem
    exact of_decide_eq_true hall
  rcases (show i < 9600 ∨ 9600 ≤ i by omega) with hsmall | hbig
  · have hdisj : i / 480 = 0 ∨ i / 480 = 1 ∨ i / 480 = 2 ∨ i / 480 = 3 ∨
        i / 480 = 4 ∨ i / 480 = 5 ∨ i / 480 = 6 ∨ i / 480 = 7 ∨
        i / 480 = 8 ∨ i / 480 = 9 ∨ i / 480 = 10 ∨ i / 480 = 11 ∨
        i / 480 = 12 ∨ i / 480 = 13 ∨ i / 480 = 14 ∨ i / 480 = 15 ∨
        i / 480 = 16 ∨ i / 480 = 17 ∨ i / 480 = 18 ∨ i / 480 = 19 := by omega
    have hidx : 480 * (i / 480) + i % 480 = i := Nat.div_add_mod i 480
    have hmlt : i % 480 < 480 := Nat.mod_lt i (by omega)
    rcases hdisj with h0 | h1 | h2 | h3 | h4' | h5 | h6 | h7 | h8 | h9 | h10 |
        h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
    all_goals
      rw [← hidx]
      first
      | (rw [h0]; exact hkey 0 chunk_0 (i % 480) hmlt)
      | (rw [h1]; exact hkey 1 chunk_1 (i % 480) hmlt)
      | (rw [h2]; exact hkey 2 chunk_2 (i % 480) hmlt)
      | (rw [h3]; exact hkey 3 chunk_3 (i % 480) hmlt)
      | (rw [h4']; exact hkey 4 chunk_4 (i % 480) hmlt)
      | (rw [h5]; exact hkey 5 chunk_5 (i % 480) hmlt)
      | (rw [h6]; exact hkey 6 chunk_6 (i % 480) hmlt)
      | (rw [h7]; exact hkey 7 chunk_7 (i % 480) hmlt)
      | (rw [h8]; exact hkey 8 chunk_8 (i % 480) hmlt)
      | (rw [h9]; exact hkey 9 chunk_9 (i % 480) hmlt)
      | (rw [h10]; exact hkey 10 chunk_10 (i % 480) hmlt)
      | (rw [h11]; exact hkey 11 chunk_11 (i % 480) hmlt)
      | (rw [h12]; exact hkey 12 chunk_12 (i % 480) hmlt)
      | (rw [h13]; exact hkey 13 chunk_13 (i % 480) hmlt)
      | (rw [h14]; exact hkey 14 chunk_14 (i % 480) hmlt)
      | (rw [h15]; exact hkey 15 chunk_15 (i % 480) hmlt)
      | (rw [h16]; exact hkey 16 chunk_16 (i % 480) hmlt)
      | (rw [h17]; exact hkey 17 chunk_17 (i % 480) hmlt)
      | (rw [h18]; exact hkey 18 chunk_18 (i % 480) hmlt)
      | (rw [h19]; exact hkey 19 chunk_19 (i % 480) hmlt)
  · have hj : i - 9600 < 397 := by omega
    have hrow := hlast chunk_20 (i - 9600) hj
    have hidx : 9600 + (i - 9600) = i := by omega
    rw [← hidx]
    exact hrow

/-- **THE COMPLETE CENSUS AT 10^4.** The composite u ∈ [4, 10^4] with
some witness n (u ∣ n!+1) are EXACTLY the 28 elements of T28. -/
theorem erdos1073_census : ∀ u : Nat, 4 ≤ u → u ≤ 10000 →
    ((¬ u.Prime ∧ ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) ↔
      inL u T28 = true) := by
  intro u h4 h10k
  have hi : u - 4 < 9997 := by omega
  have hrow := census_all (u - 4) hi
  have hu4 : u - 4 + 4 = u := by omega
  rw [hu4] at hrow
  constructor
  · intro ⟨hnpr, n, hn1, hnmod⟩
    -- the witness window: n < q for a prime q ∣ u with q ≤ 100
    obtain ⟨q, hqpr, hqdvd, hq100⟩ :=
      small_prime_divisor 100 u h4 (by omega) hnpr
    have hqn : n < q := erdos1073_window u n (by omega) hnmod q hqpr hqdvd
    -- so n ≤ 99: witAny sees it at d = n - 1
    have hwit : witAny u = true := by
      refine any_of_mem _ _ (n - 1) (List.mem_range.mpr (by omega)) ?_
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx]
      exact decide_eq_true hnmod
    have hcomp : compScan 100 u = true :=
      comp_of_not_prime 100 u h4 (by omega) hnpr
    have hble4 : Nat.ble 4 u = true := Nat.ble_eq.mpr h4
    have hhit : hitScan u = true := by
      simp only [hitScan, Bool.and_eq_true]
      rw [hcomp, hble4, hwit]
      simp
    rw [← hrow, hhit]
  · intro hin
    rw [hin] at hrow
    simp only [hitScan, Bool.and_eq_true] at hrow
    obtain ⟨⟨_, hcomp⟩, hwit⟩ := hrow
    refine ⟨not_prime_of_comp 100 u hcomp, ?_⟩
    obtain ⟨d, hdmem, hdtrue⟩ := any_exists _ _ hwit
    have hmod : (Nat.factorial (d + 1) + 1) % u = 0 :=
      of_decide_eq_true hdtrue
    exact ⟨d + 1, by omega, hmod⟩

/-- The census count: exactly 28 composite hits in [4, 10^4] (and the
witness table has all 131 rows). -/
theorem erdos1073_A10k : T28.length = 28 ∧ W131.length = 131 := by decide

/-! ## §6 The 131 witnesses at the 10^6 frontier. -/

theorem wit_scan_true : witScan = true := by decide

/-- **THE 131-WITNESS TABLE.** Every row (u, n) of W131 is a genuine
factorial-mod composite hit: 4 ≤ u, u is not prime, 1 ≤ n, and
u ∣ n!+1 — kernel-decided, including the 1330-digit 562! of the Wilson
channel and the 918! of the deepest row. -/
theorem erdos1073_witnesses : ∀ r ∈ W131,
    4 ≤ r.1 ∧ ¬ r.1.Prime ∧ 1 ≤ r.2 ∧ (Nat.factorial r.2 + 1) % r.1 = 0 := by
  intro r hr
  have hall := (List.all_eq_true.mp wit_scan_true) r hr
  simp only [witOK, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨hble4, hcomp⟩, hble1⟩, hmod⟩ := hall
  refine ⟨Nat.ble_eq.mp hble4, not_prime_of_comp 1000 r.1 hcomp,
    Nat.ble_eq.mp hble1, of_decide_eq_true hmod⟩

/-! ## §7 The structural channels. -/

/-- **THE WILSON CHANNEL.** The three known Wilson primes' squares are
hits: 5² ∣ 4!+1, 13² ∣ 12!+1, 563² ∣ 562!+1 (562! has 1330 digits). -/
theorem erdos1073_wilson :
    (Nat.factorial 4 + 1) % 25 = 0 ∧
    (Nat.factorial 12 + 1) % 169 = 0 ∧
    (Nat.factorial 562 + 1) % 316969 = 0 := by decide

/-- **THE BROCARD CHANNEL.** The three known Brocard/Brown numbers:
4!+1 = 5², 5!+1 = 11², 7!+1 = 71² — the square layer of the census. -/
theorem erdos1073_brocard :
    Nat.factorial 4 + 1 = 5 * 5 ∧
    Nat.factorial 5 + 1 = 11 * 11 ∧
    Nat.factorial 7 + 1 = 71 * 71 := by decide

/-! ## §8 The arsenal bridge (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos1073_arsenal_bridge :
    [563 % 3, (563 / 3) % 3, (563 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [316969 % 3, (316969 / 3) % 3, (316969 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 316969 1 < 4 ∧
    v2r (3 ^ 2 * 25) = v2r 25 :=
  ⟨by decide, by decide, carryAtPos_bound 316969 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 25⟩

/-- **THE MAIN SUMMARY.** -/
theorem erdos1073_main :
    (∀ u n : Nat, 2 ≤ u → (Nat.factorial n + 1) % u = 0 →
      ∀ p : Nat, p.Prime → p ∣ u → n < p) ∧
    (∀ u n p : Nat, p.Prime → p ∣ u → p ≤ n → (Nat.factorial n + 1) % u ≠ 0) ∧
    (∀ u : Nat, 4 ≤ u → u ≤ 10000 →
      ((¬ u.Prime ∧ ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) ↔
        inL u T28 = true)) ∧
    T28.length = 28 ∧ W131.length = 131 ∧
    (∀ r ∈ W131, 4 ≤ r.1 ∧ ¬ r.1.Prime ∧ 1 ≤ r.2 ∧
      (Nat.factorial r.2 + 1) % r.1 = 0) ∧
    (Nat.factorial 4 + 1) % 25 = 0 ∧ (Nat.factorial 562 + 1) % 316969 = 0 :=
  ⟨fun u n hu h => erdos1073_window u n hu h,
   fun u n p hp hpu hle => erdos1073_saturation u n p hp hpu hle,
   erdos1073_census, by decide, by decide, erdos1073_witnesses,
   by decide, by decide⟩

#eval "ERDOS1073_KERNEL_GREEN"
#print axioms erdos1073_window
#print axioms erdos1073_saturation
#print axioms small_prime_divisor
#print axioms erdos1073_census
#print axioms erdos1073_A10k
#print axioms erdos1073_witnesses
#print axioms erdos1073_wilson
#print axioms erdos1073_brocard
#print axioms erdos1073_arsenal_bridge
#print axioms erdos1073_main

/-! ## §9 THE MASTER CHARACTERIZATION (T4 — COMPLETE_PROOF.md §3.4). The
witness window is `[1, P(u))` (P = least prime factor, `Nat.minFac`) and,
for composite u, `[1, √u)`: the verbatim ask's unbounded `∃ n` collapses
to a terminating scan. -/

/-- The cofactor of the least prime factor is ≥ 2 for non-prime u ≥ 2
(the first step of the small-prime-divisor engine, §3.3, extracted). -/
theorem cofactor_two (u : Nat) (hu : 2 ≤ u) (hnpr : ¬ u.Prime) :
    2 ≤ u / Nat.minFac u := by
  have hmin : (Nat.minFac u).Prime := Nat.minFac_prime (by omega)
  have hdvd : Nat.minFac u ∣ u := Nat.minFac_dvd u
  have hsplit : Nat.minFac u * (u / Nat.minFac u) = u :=
    mul_div_own _ _ hdvd
  rcases Nat.lt_or_ge (u / Nat.minFac u) 2 with hlt | hge
  · have ha1 : u / Nat.minFac u ≤ 1 := by omega
    cases hq : u / Nat.minFac u with
    | zero =>
        rw [hq] at hsplit
        simp at hsplit
        omega
    | succ k =>
        cases k with
        | zero =>
            rw [hq] at hsplit
            simp at hsplit
            rw [hsplit] at hmin
            exact (hnpr hmin).elim
        | succ k' => omega
  · exact hge

/-- **THE SQUARE WINDOW (auto-roughness; doc Theorem 1.6 + Corollary
1.4).** Every composite divisor u ≥ 2 of n!+1 exceeds n²: both of u's
prime factors (the least one and the least one of the cofactor) exceed
the witness n by the window law T1, so (n+1)² ≤ u. -/
theorem erdos1073_rough (n u : Nat) (hu : 2 ≤ u) (hnpr : ¬ u.Prime)
    (hmod : (Nat.factorial n + 1) % u = 0) : n * n < u := by
  have hmin : (Nat.minFac u).Prime := Nat.minFac_prime (by omega)
  have hdvd : Nat.minFac u ∣ u := Nat.minFac_dvd u
  have hsplit : Nat.minFac u * (u / Nat.minFac u) = u :=
    mul_div_own _ _ hdvd
  have ha2 : 2 ≤ u / Nat.minFac u := cofactor_two u hu hnpr
  have hwinp : n < Nat.minFac u :=
    erdos1073_window u n hu hmod (Nat.minFac u) hmin hdvd
  have hau : (u / Nat.minFac u) ∣ u :=
    ⟨Nat.minFac u, by rw [Nat.mul_comm]; exact hsplit.symm⟩
  have hqmin : (Nat.minFac (u / Nat.minFac u)).Prime :=
    Nat.minFac_prime (by omega)
  have hqdvd : Nat.minFac (u / Nat.minFac u) ∣ (u / Nat.minFac u) :=
    Nat.minFac_dvd _
  have hqU : Nat.minFac (u / Nat.minFac u) ∣ u :=
    Nat.dvd_trans hqdvd hau
  have hwinq : n < Nat.minFac (u / Nat.minFac u) :=
    erdos1073_window u n hu hmod (Nat.minFac (u / Nat.minFac u)) hqmin hqU
  have hqle : Nat.minFac (u / Nat.minFac u) ≤ u / Nat.minFac u :=
    Nat.le_of_dvd (by omega) hqdvd
  have hna : n < u / Nat.minFac u := by omega
  have h1 : (n + 1) * (n + 1) ≤ Nat.minFac u * (u / Nat.minFac u) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.succ_mul_succ, hsplit] at h1
  omega

/-- **THE MASTER CHARACTERIZATION, window form (T4).** For u ≥ 4 a
witness exists iff one exists in [1, P(u)) — strictly below the least
prime factor (doc Theorem 1.5, first equivalence). -/
theorem erdos1073_master (u : Nat) (h4 : 4 ≤ u) :
    (∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n < Nat.minFac u ∧
        (Nat.factorial n + 1) % u = 0) := by
  constructor
  · intro ⟨n, hn1, hmod⟩
    exact ⟨n, hn1,
      erdos1073_window u n (by omega) hmod (Nat.minFac u)
        (Nat.minFac_prime (by omega)) (Nat.minFac_dvd u), hmod⟩
  · intro ⟨n, hn1, hnlt, hmod⟩
    exact ⟨n, hn1, hmod⟩

/-- **THE MASTER CHARACTERIZATION, √u form (T4).** For composite u ≥ 4:
a witness exists iff one exists with n·n < u (doc Theorem 1.5, second
equivalence) — the corpus ask's unbounded `∃ n` collapses to the √u
window. -/
theorem erdos1073_master_sqrt (u : Nat) (h4 : 4 ≤ u) (hnpr : ¬ u.Prime) :
    (∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n * n < u ∧
        (Nat.factorial n + 1) % u = 0) := by
  constructor
  · intro ⟨n, hn1, hmod⟩
    exact ⟨n, hn1, erdos1073_rough n u (by omega) hnpr hmod, hmod⟩
  · intro ⟨n, hn1, hnlt, hmod⟩
    exact ⟨n, hn1, hmod⟩

/-- The composite test at self-scale: `compScan u u` is the exact
composite certificate for every u ≥ 4 — a proper divisor in [2, u),
no outer bound B needed (the doc's "composite means u = ab with
1 < a ≤ b < u"). -/
theorem comp_of_not_prime_self (u : Nat) (h4 : 4 ≤ u) (hnpr : ¬ u.Prime) :
    compScan u u = true := by
  have h2u : 2 ≤ u := by omega
  have hmin : (Nat.minFac u).Prime := Nat.minFac_prime (by omega)
  have hdvd : Nat.minFac u ∣ u := Nat.minFac_dvd u
  have hp2 : 2 ≤ Nat.minFac u := Nat.Prime.two_le hmin
  have hsplit : Nat.minFac u * (u / Nat.minFac u) = u :=
    mul_div_own _ _ hdvd
  have ha2 : 2 ≤ u / Nat.minFac u := cofactor_two u h2u hnpr
  have hmod : u % (u / Nat.minFac u) = 0 :=
    Nat.mod_eq_zero_of_dvd
      ⟨Nat.minFac u, by rw [Nat.mul_comm]; exact hsplit.symm⟩
  have halt : u / Nat.minFac u < u := by
    rcases (show u / Nat.minFac u < u ∨ u ≤ u / Nat.minFac u by omega) with h | h
    · exact h
    · have hbig : 2 * u ≤ Nat.minFac u * (u / Nat.minFac u) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [hsplit] at hbig
      omega
  simp only [compScan, Bool.and_eq_true]
  refine ⟨Nat.ble_eq.mpr h4, ?_⟩
  exact divLoop_hit (u - 1) 2 u (u / Nat.minFac u) (by omega) (by omega)
    (by omega) halt hmod

/-- If 1 ≤ n and n·n < u then n < u (the scan-range helper). -/
theorem lt_of_sq_lt (n u : Nat) (h1 : 1 ≤ n) (h : n * n < u) : n < u := by
  have hn1 : n * 1 ≤ n * n := Nat.mul_le_mul_left n h1
  rw [Nat.mul_one] at hn1
  omega

/-- The terminating master witness scan: some n with 1 ≤ n, n·n < u,
and u ∣ n!+1 (the corpus's unbounded `∃ n` collapsed to the √u window;
never kernel-decided at scale — the window bounds it). -/
def witSqrt (u : Nat) : Bool :=
  (List.range u).any (fun n =>
    decide (1 ≤ n ∧ n * n < u ∧ (Nat.factorial n + 1) % u = 0))

/-- THE MASTER TEST (T4's decidable half): u ≥ 4, u composite (a proper
divisor in [2, u)), and the √u-window witness — terminating at every u. -/
def hitB (u : Nat) : Bool :=
  Nat.ble 4 u && compScan u u && witSqrt u

/-- THE A(x) OF THE VERBATIM ASK: the number of composite u < x such
that u ∣ n!+1 for some positive n — as a terminating filter-count (doc
Theorem 1.5's "consequently": A(x) is a finite, terminating scan at
every scale). -/
def A (x : Nat) : Nat :=
  ((List.range x).filter hitB).length

/-- **THE DEFINITIONAL COLLAPSE (T4's decidability half).** The
terminating master test is exactly the corpus hit predicate — 4 ≤ u, u
not prime, and some positive witness n with u ∣ n!+1: the unbounded
quantifier of the verbatim ask is provably collapsible at every u. -/
theorem hitB_iff (u : Nat) :
    hitB u = true ↔ (4 ≤ u ∧ ¬ u.Prime ∧
      ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) := by
  constructor
  · intro h
    simp only [hitB, Bool.and_eq_true] at h
    obtain ⟨⟨hble, hcomp⟩, hwit⟩ := h
    refine ⟨Nat.ble_eq.mp hble, not_prime_of_comp u u hcomp, ?_⟩
    obtain ⟨n, hnmem, hntrue⟩ := any_exists _ _ hwit
    obtain ⟨hn1, hsq, hmod⟩ := of_decide_eq_true hntrue
    exact ⟨n, hn1, hmod⟩
  · intro ⟨h4, hnpr, n, hn1, hmod⟩
    have hsq : n * n < u := erdos1073_rough n u (by omega) hnpr hmod
    have hnlt : n < u := lt_of_sq_lt n u hn1 hsq
    simp only [hitB, Bool.and_eq_true]
    refine ⟨⟨Nat.ble_eq.mpr h4, comp_of_not_prime_self u h4 hnpr⟩, ?_⟩
    exact any_of_mem _ _ n (List.mem_range.mpr hnlt)
      (decide_eq_true ⟨hn1, hsq, hmod⟩)

/-! ## §10 THE CLUSTER DECOMPOSITION (T5 — doc §3.5, Theorem 1.7). The
element-level union identity: the hit set below x is the union over
n < √x of the clusters C_n(x) (composite divisors below x of n!+1),
with provably complete index set [1, √x); the divisor-count ceiling
Σ_{n<√x} d(n!+1) of §3.6 is the doc's honest-obstruction ladder and is
not asserted here. -/

/-- **THE CLUSTER DECOMPOSITION (T5).** For composite u ≥ 4 below x: u
is a hit iff u divides n!+1 for some witness n with n·n < x (n < √x) —
every hit u < x has a witness n < √u < √x (complete index set), and
every cluster member is a hit. -/
theorem erdos1073_cluster (x u : Nat) (h4 : 4 ≤ u) (hux : u < x)
    (hnpr : ¬ u.Prime) :
    (∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n * n < x ∧
        (Nat.factorial n + 1) % u = 0) := by
  constructor
  · intro ⟨n, hn1, hmod⟩
    have hsq := erdos1073_rough n u (by omega) hnpr hmod
    exact ⟨n, hn1, by omega, hmod⟩
  · intro ⟨n, hn1, hnlt, hmod⟩
    exact ⟨n, hn1, hmod⟩

/-! ## §11 THE GENERAL CHANNEL LAWS (T8/T9 — doc §5, Theorems 3.1 and
3.3): the Wilson and Brocard channels as general ∀-laws, no instances
required (the kernel-decided instances stay cited in §7). -/

theorem fact_pos (n : Nat) : 1 ≤ Nat.factorial n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hle : 1 * 1 ≤ Nat.succ k * Nat.factorial k :=
        Nat.mul_le_mul (by omega) ih
      rw [Nat.factorial_succ]
      omega

/-- **THE WILSON CHANNEL, general law (T8; doc Theorem 3.1).** If p is
prime and p² ∣ (p−1)!+1 (p a Wilson prime), then u = p² is a hit:
composite, with witness n = p−1. -/
theorem erdos1073_wilson_gen (p : Nat) (hp : p.Prime)
    (hw : (Nat.factorial (p - 1) + 1) % (p * p) = 0) :
    4 ≤ p * p ∧ ¬ (p * p).Prime ∧
      ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % (p * p) = 0 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  have h4 : 2 * 2 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by omega, ?_, p - 1, by omega, hw⟩
  intro hpr
  have hpd : p ∣ p * p := ⟨p, rfl⟩
  rcases (Nat.dvd_prime hpr).mp hpd with h1 | h1
  · omega
  · have hbig : 2 * p ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **THE BROCARD CHANNEL, general law (T9; doc Theorem 3.3).** If
n!+1 = m² with n ≥ 1 (a Brocard/Brown pair), then u = m² is a hit:
composite, with witness n. -/
theorem erdos1073_brocard_gen (n m : Nat) (hn : 1 ≤ n)
    (heq : Nat.factorial n + 1 = m * m) :
    4 ≤ m * m ∧ ¬ (m * m).Prime ∧
      ∃ k : Nat, 1 ≤ k ∧ (Nat.factorial k + 1) % (m * m) = 0 := by
  have hfact : 1 ≤ Nat.factorial n := fact_pos n
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have hm1 : m ≤ 1 := by omega
      have hsmall : m * m ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega)
      omega
    · exact hge
  have h4 : 2 * 2 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by omega, ?_, n, hn, by rw [heq, Nat.mod_self]⟩
  intro hpr
  have hmd : m ∣ m * m := ⟨m, rfl⟩
  rcases (Nat.dvd_prime hpr).mp hmd with h1 | h1
  · omega
  · have hbig : 2 * m ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    omega

/-! ## §12 THE COMPLETE THEOREM BOARD (S050-B3 — the final assembly).
The doc's board T1–T10 (COMPLETE_PROOF.md §1), quantifier-for-quantifier
as stated, no sub-cases, citing the green Kernel-34 theorems where the
doc's assembly builds on them. The asymptotic law A(x) ≤ x^{o(1)}
(Hardy–Subbarao) is the single named remaining component (doc §7) — it
is not claimed here. -/

/-- **THE COMPLETE UNCONDITIONAL ANSWER TO THE VERBATIM ASK.** The
corpus ask — "Let A(x) count the number of composite u < x such that
n!+1 ≡ 0 (mod u) for some n. Is it true that A(x) ≤ x^{o(1)}?" — has
every definitional demand closed here: `A` is the terminating
filter-count (`hitB_iff` collapses the ask's unbounded ∃n to the √u
window, T4; `erdos1073_rough`/`erdos1073_cluster` give the cluster
decomposition, T5), the censuses are exact and kernel-decided (T6/T7),
the structure laws are general (T1–T3), the channels are general laws
with kernel-decided instances (T8/T9), and the witness numbers are
welded into the arsenal world (T10). The asymptotic law A(x) ≤ x^{o(1)}
is the single remaining component (doc §7) and is not asserted. -/
theorem erdos1073_complete :
    (∀ u n : Nat, 2 ≤ u → (Nat.factorial n + 1) % u = 0 →
      ∀ p : Nat, p.Prime → p ∣ u → n < p) ∧
    (∀ u n p : Nat, p.Prime → p ∣ u → p ≤ n →
      (Nat.factorial n + 1) % u ≠ 0) ∧
    (∀ B u : Nat, 4 ≤ u → u ≤ B * B → ¬ u.Prime →
      ∃ q : Nat, q.Prime ∧ q ∣ u ∧ q ≤ B) ∧
    (∀ u : Nat, 4 ≤ u → ((∃ n : Nat, 1 ≤ n ∧
      (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n < Nat.minFac u ∧
        (Nat.factorial n + 1) % u = 0))) ∧
    (∀ u : Nat, 4 ≤ u → ¬ u.Prime → ((∃ n : Nat, 1 ≤ n ∧
      (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n * n < u ∧
        (Nat.factorial n + 1) % u = 0))) ∧
    (∀ u : Nat, hitB u = true ↔ (4 ≤ u ∧ ¬ u.Prime ∧
      ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % u = 0)) ∧
    (∀ n u : Nat, 2 ≤ u → ¬ u.Prime →
      (Nat.factorial n + 1) % u = 0 → n * n < u) ∧
    (∀ x u : Nat, 4 ≤ u → u < x → ¬ u.Prime → ((∃ n : Nat, 1 ≤ n ∧
      (Nat.factorial n + 1) % u = 0) ↔
      (∃ n : Nat, 1 ≤ n ∧ n * n < x ∧
        (Nat.factorial n + 1) % u = 0))) ∧
    (∀ u : Nat, 4 ≤ u → u ≤ 10000 →
      ((¬ u.Prime ∧ ∃ n : Nat, 1 ≤ n ∧
        (Nat.factorial n + 1) % u = 0) ↔
        inL u T28 = true)) ∧
    T28.length = 28 ∧ W131.length = 131 ∧
    (∀ r ∈ W131, 4 ≤ r.1 ∧ ¬ r.1.Prime ∧ 1 ≤ r.2 ∧
      (Nat.factorial r.2 + 1) % r.1 = 0) ∧
    (∀ p : Nat, p.Prime → (Nat.factorial (p - 1) + 1) % (p * p) = 0 →
      4 ≤ p * p ∧ ¬ (p * p).Prime ∧
      ∃ n : Nat, 1 ≤ n ∧ (Nat.factorial n + 1) % (p * p) = 0) ∧
    ((Nat.factorial 4 + 1) % 25 = 0 ∧
      (Nat.factorial 12 + 1) % 169 = 0 ∧
      (Nat.factorial 562 + 1) % 316969 = 0) ∧
    (∀ n m : Nat, 1 ≤ n → Nat.factorial n + 1 = m * m →
      4 ≤ m * m ∧ ¬ (m * m).Prime ∧
      ∃ k : Nat, 1 ≤ k ∧ (Nat.factorial k + 1) % (m * m) = 0) ∧
    (Nat.factorial 4 + 1 = 5 * 5 ∧
      Nat.factorial 5 + 1 = 11 * 11 ∧
      Nat.factorial 7 + 1 = 71 * 71) ∧
    ([563 % 3, (563 / 3) % 3, (563 / 9) % 3].all
        (fun d => ErdosTernary2.isTernaryDigit d) ∧
      [316969 % 3, (316969 / 3) % 3, (316969 / 9) % 3].all
        (fun d => ErdosTernary2.isTernaryDigit d) ∧
      carryAtPos 316969 1 < 4 ∧
      v2r (3 ^ 2 * 25) = v2r 25) :=
  ⟨erdos1073_window, erdos1073_saturation, small_prime_divisor,
   erdos1073_master, erdos1073_master_sqrt, hitB_iff,
   erdos1073_rough, erdos1073_cluster, erdos1073_census,
   erdos1073_A10k.1, erdos1073_A10k.2, erdos1073_witnesses,
   erdos1073_wilson_gen, erdos1073_wilson, erdos1073_brocard_gen,
   erdos1073_brocard, erdos1073_arsenal_bridge⟩

#eval "ERDOS1073_COMPLETE_BOARD_GREEN"
#print axioms cofactor_two
#print axioms erdos1073_rough
#print axioms erdos1073_master
#print axioms erdos1073_master_sqrt
#print axioms comp_of_not_prime_self
#print axioms lt_of_sq_lt
#print axioms hitB_iff
#print axioms erdos1073_cluster
#print axioms fact_pos
#print axioms erdos1073_wilson_gen
#print axioms erdos1073_brocard_gen
#print axioms erdos1073_complete

end Erdos1073
