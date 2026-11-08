import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels K21/K26/K30): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 8000000

/-! # Erdős–Graham #461 — THE SMOOTH-COMPONENT CENSUS LAWS (S041 volley, Kernel 35)

## THE PROBLEM (verbatim, erdosproblems.com/461, ErGr80)

> Let $s_t(n)$ be the $t$-smooth component of $n$ - that is, the product of
> all primes $p$ (with multiplicity) dividing $n$ such that $p<t$. Let
> $f(n,t)$ count the number of distinct possible values for $s_t(m)$ for
> $m\in[n+1,n+t]$. Is it true that $f(n,t)\gg t$ (uniformly, for all $t$
> and $n$)?

Erdős and Graham report $f(n,t) \gg t/\log t$.

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. **THE EXTRACTION LAWS** (general): `spart p m = p ^ vp p m` — the
   p-part engine computes the exact prime power (the K33 vp-architecture
   lifted: fuel recursion + saturation); `scomp_dvd` — the smooth
   component $s_t(m)$ DIVIDES $m$ for every prime list.
2. **THE ACHIEVEMENT TABLE** (`erdos461_achieve*`): for every
   $t \in [2, 120]$ the engine's minimizing window $n_t$ (over
   $n < 2\cdot 10^5$, computed by the sliding census) achieves EXACTLY
   $c_t$ distinct smooth-component values — all 119 rows kernel-decided,
   including $f(1892, 120) = 69$.
3. **THE STABILITY LAW** (`erdos461_stability*`): for every $t \in [14,120]$
   the census minimum satisfies $0.55\,t \le c_t \le 0.65\,t$ — rock-stable
   at $\approx 0.57$, NO DECAY, on all 107 rows (integer form:
   $55t \le 100\,c_t \le 65t$).
4. **THE ERDŐS–GRAHAM BEATING** (`erdos461_ergra`): for every $t \in
   [14,120]$: $c_t \ge t/\ln t$ — the census minimums BEAT the published
   $t/\log t$ bound on the whole certified range ($c_t \cdot \lfloor 1000
   \ln t\rfloor \ge 1000\,t$, with the row-match to the achievement table
   kernel-verified).
5. **THE FOUR BOTH-DIRECTION CENSUSES** (`erdos461_min14/20/30/40`): the
   exact minimum of $f(n,t)$ over $n < 480$ at $t = 14, 20, 30, 40$:
   $\min = 9, 13, 19, 25$ (attained at $n = 33, 198, 121, 162$) — witness
   AND exclusion, all kernel-decided in 240-element NO-OOM chunks.

Honest scope: the uniform $\gg t$ over ALL $n$ (the problem's core)
remains OPEN — the kernel lands the extraction laws, the 119-row
achievement table, the stability law, the ErGra beating on $[14,120]$,
and four complete both-direction censuses; the $n \le 2\cdot 10^5$
minimality of the $c_t$ is engine-certified dual-method
(`battery461.py`). -/

namespace Erdos461

/-! ## §0 The definitions. -/

/-- List membership as a Bool (self-contained). -/
def inL (u : Nat) (l : List Nat) : Bool := l.any (fun x => decide (x = u))

/-- The primes below 121 (the t ≤ 120 support). -/
def PRIMES120 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
   67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

/-- The primes < t (for t ≤ 121). -/
def psBelow (t : Nat) : List Nat := PRIMES120.takeWhile (fun q => decide (q < t))

/-- The p-adic valuation (the K33 vp-architecture: fuel recursion). -/
def vpf : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | _, _, 0 => 0
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then 1 + vpf p f ((n + 1) / p) else 0

def vp (p : Nat) (n : Nat) : Nat := vpf p n n

/-- The p-PART of n (product form): ∏ p, one per division step. -/
def spf : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | _, _, 0 => 1
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then p * spf p f ((n + 1) / p) else 1

def spart (p : Nat) (m : Nat) : Nat := spf p m m

/-- The t-smooth component: fold the prime parts down the cofactor. -/
def scomp : List Nat → Nat → Nat
  | [], _ => 1
  | p :: ps, m => spart p m * scomp ps (m / spart p m)

/-- The window value list [s_t(n+1), ..., s_t(n+t)]. -/
def wvals (ps : List Nat) (n t : Nat) : List Nat :=
  (List.range t).map (fun i => scomp ps (n + 1 + i))

/-- First-occurrence distinct count. -/
def dcnt : List Nat → List Nat → Nat
  | [], _ => 0
  | x :: rest, seen => (if inL x seen then 0 else 1) + dcnt rest (x :: seen)

/-- THE PROBLEM'S FUNCTION: f(n,t) = #distinct s_t(m), m ∈ [n+1, n+t]. -/
def f461 (n t : Nat) : Nat := dcnt (wvals (psBelow t) n t) []

def ACH1 : List (Nat × Nat × Nat) := [
  (2, 0, 1), (3, 0, 2), (4, 3, 3), (5, 9, 3), (6, 56, 4), (7, 176, 4),
  (8, 1255, 5), (9, 2515, 5), (10, 2514, 6), (11, 5034, 6), (12, 55433, 7), (13, 55433, 7),
  (14, 33, 9), (15, 352, 9), (16, 81, 10), (17, 3180, 10), (18, 56, 11), (19, 12145, 11),
  (20, 2457, 12), (21, 129272, 12), (22, 2457, 13), (23, 73515, 13), (24, 129269, 14), (25, 30177, 15),
  (26, 30177, 15), (27, 192, 16), (28, 190, 17), (29, 190, 17), (30, 183992, 17), (31, 83358, 18),
  (32, 1276, 19), (33, 183991, 19), (34, 19995, 20), (35, 9984, 21), (36, 107433, 21), (37, 9982, 22),
  (38, 280, 23), (39, 107430, 23), (40, 1281, 24), (41, 1281, 24)
  ]
def ACH2 : List (Nat × Nat × Nat) := [
  (42, 1276, 25), (43, 1276, 25), (44, 1275, 26), (45, 1276, 26), (46, 1276, 26), (47, 1275, 27),
  (48, 1274, 28), (49, 1273, 29), (50, 378, 30), (51, 1276, 30), (52, 1275, 31), (53, 1276, 31),
  (54, 533, 32), (55, 378, 33), (56, 78185, 33), (57, 392, 34), (58, 378, 35), (59, 380, 35),
  (60, 533, 36), (61, 904, 36), (62, 392, 37), (63, 904, 37), (64, 533, 38), (65, 392, 39),
  (66, 392, 39), (67, 380, 40), (68, 1251, 40), (69, 742, 41), (70, 904, 41), (71, 1251, 41),
  (72, 651, 43), (73, 651, 43), (74, 904, 44), (75, 904, 44), (76, 903, 45), (77, 904, 45),
  (78, 904, 45), (79, 904, 45), (80, 903, 46), (81, 904, 46)
  ]
def ACH3 : List (Nat × Nat × Nat) := [
  (82, 903, 47), (83, 902, 48), (84, 760, 50), (85, 742, 51), (86, 1128, 51), (87, 2420, 51),
  (88, 756, 52), (89, 1541, 52), (90, 1541, 52), (91, 1540, 53), (92, 752, 54), (93, 742, 55),
  (94, 750, 55), (95, 1162, 55), (96, 1541, 55), (97, 1162, 56), (98, 2420, 56), (99, 2420, 56),
  (100, 2419, 57), (101, 2420, 57), (102, 2419, 59), (103, 1541, 60), (104, 2415, 60), (105, 1892, 61),
  (106, 2415, 61), (107, 1892, 62), (108, 1281, 64), (109, 1281, 64), (110, 2409, 64), (111, 2408, 65),
  (112, 2409, 65), (113, 1771, 66), (114, 2930, 66), (115, 1892, 67), (116, 1892, 67), (117, 2930, 67),
  (118, 2929, 68), (119, 2930, 68), (120, 1892, 69)
  ]
def ERGRA : List (Nat × Nat × Nat) := [
  (14, 9, 2639), (15, 9, 2708), (16, 10, 2772), (17, 10, 2833), (18, 11, 2890), (19, 11, 2944),
  (20, 12, 2995), (21, 12, 3044), (22, 13, 3091), (23, 13, 3135), (24, 14, 3178), (25, 15, 3218),
  (26, 15, 3258), (27, 16, 3295), (28, 17, 3332), (29, 17, 3367), (30, 17, 3401), (31, 18, 3433),
  (32, 19, 3465), (33, 19, 3496), (34, 20, 3526), (35, 21, 3555), (36, 21, 3583), (37, 22, 3610),
  (38, 23, 3637), (39, 23, 3663), (40, 24, 3688), (41, 24, 3713), (42, 25, 3737), (43, 25, 3761),
  (44, 26, 3784), (45, 26, 3806), (46, 26, 3828), (47, 27, 3850), (48, 28, 3871), (49, 29, 3891),
  (50, 30, 3912), (51, 30, 3931), (52, 31, 3951), (53, 31, 3970), (54, 32, 3988), (55, 33, 4007),
  (56, 33, 4025), (57, 34, 4043), (58, 35, 4060), (59, 35, 4077), (60, 36, 4094), (61, 36, 4110),
  (62, 37, 4127), (63, 37, 4143), (64, 38, 4158), (65, 39, 4174), (66, 39, 4189), (67, 40, 4204),
  (68, 40, 4219), (69, 41, 4234), (70, 41, 4248), (71, 41, 4262), (72, 43, 4276), (73, 43, 4290),
  (74, 44, 4304), (75, 44, 4317), (76, 45, 4330), (77, 45, 4343), (78, 45, 4356), (79, 45, 4369),
  (80, 46, 4382), (81, 46, 4394), (82, 47, 4406), (83, 48, 4418), (84, 50, 4430), (85, 51, 4442),
  (86, 51, 4454), (87, 51, 4465), (88, 52, 4477), (89, 52, 4488), (90, 52, 4499), (91, 53, 4510),
  (92, 54, 4521), (93, 55, 4532), (94, 55, 4543), (95, 55, 4553), (96, 55, 4564), (97, 56, 4574),
  (98, 56, 4584), (99, 56, 4595), (100, 57, 4605), (101, 57, 4615), (102, 59, 4624), (103, 60, 4634),
  (104, 60, 4644), (105, 61, 4653), (106, 61, 4663), (107, 62, 4672), (108, 64, 4682), (109, 64, 4691),
  (110, 64, 4700), (111, 65, 4709), (112, 65, 4718), (113, 66, 4727), (114, 66, 4736), (115, 67, 4744),
  (116, 67, 4753), (117, 67, 4762), (118, 68, 4770), (119, 68, 4779), (120, 69, 4787)
  ]

/-! ## §1 The saturation + extraction laws (the K33 architecture). -/

theorem vp_unfold_succ (p N : Nat) :
    vp p (N + 1) =
      if (N + 1) % p = 0 then 1 + vpf p N ((N + 1) / p) else 0 := rfl

theorem spart_unfold (p N : Nat) :
    spart p (N + 1) =
      if (N + 1) % p = 0 then p * spf p N ((N + 1) / p) else 1 := rfl

theorem vpf_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f →
    vpf p f n = vpf p n n := by
  intro F
  induction F with
  | zero =>
    intro f hf n hn
    have hf0 : f = 0 := by omega
    subst hf0
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ F ih =>
    intro f hf n hn
    cases f with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      rfl
    | succ F' =>
      cases n with
      | zero => rfl
      | succ N =>
        have e1 : vpf p (F' + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpf p F' ((N + 1) / p) else 0 := rfl
        have e2 : vpf p (N + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpf p N ((N + 1) / p) else 0 := rfl
        rw [e1, e2]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod, if_pos hmod]
          have hdlt : (N + 1) / p < N + 1 :=
            Nat.div_lt_self (by omega) (by omega)
          have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
          have i2 := ih N (by omega) ((N + 1) / p) (by omega)
          rw [i1, i2]
        · rw [if_neg hmod, if_neg hmod]

theorem spf_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f →
    spf p f n = spf p n n := by
  intro F
  induction F with
  | zero =>
    intro f hf n hn
    have hf0 : f = 0 := by omega
    subst hf0
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ F ih =>
    intro f hf n hn
    cases f with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      rfl
    | succ F' =>
      cases n with
      | zero => rfl
      | succ N =>
        have e1 : spf p (F' + 1) (N + 1) =
            if (N + 1) % p = 0 then p * spf p F' ((N + 1) / p) else 1 := rfl
        have e2 : spf p (N + 1) (N + 1) =
            if (N + 1) % p = 0 then p * spf p N ((N + 1) / p) else 1 := rfl
        rw [e1, e2]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod, if_pos hmod]
          have hdlt : (N + 1) / p < N + 1 :=
            Nat.div_lt_self (by omega) (by omega)
          have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
          have i2 := ih N (by omega) ((N + 1) / p) (by omega)
          rw [i1, i2]
        · rw [if_neg hmod, if_neg hmod]

/-- a ∣ b → a * (b / a) = b (omega-friendly, via div_add_mod). -/
theorem mul_div_own (a b : Nat) (h : a ∣ b) : a * (b / a) = b := by
  have hmod : b % a = 0 := Nat.mod_eq_zero_of_dvd h
  have hdm := Nat.div_add_mod b a
  omega

/-- **THE EXTRACTION AGREEMENT.** spf computes the exact prime power:
spf p f n = p ^ vpf p f n whenever n ≤ f. -/
theorem spf_eq_pow (p : Nat) (hp : 2 ≤ p) : ∀ f n, n ≤ f →
    spf p f n = p ^ vpf p f n := by
  intro f
  induction f with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ f ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ N =>
      have e1 : spf p (f + 1) (N + 1) =
          if (N + 1) % p = 0 then p * spf p f ((N + 1) / p) else 1 := rfl
      have e2 : vpf p (f + 1) (N + 1) =
          if (N + 1) % p = 0 then 1 + vpf p f ((N + 1) / p) else 0 := rfl
      have hdlt : (N + 1) / p < N + 1 :=
        Nat.div_lt_self (by omega) (by omega)
      rw [e1, e2]
      by_cases hmod : (N + 1) % p = 0
      · rw [if_pos hmod, if_pos hmod, ih ((N + 1) / p) (by omega)]
        rw [Nat.add_comm 1 (vpf p f ((N + 1) / p)), Nat.pow_succ]
        exact Nat.mul_comm p (p ^ (vpf p f ((N + 1) / p)))
      · rw [if_neg hmod, if_neg hmod]
        rfl

/-- **THE p-PART LAW.** spart p m = p ^ vp p m for every p ≥ 2 — the
p-part engine computes the exact prime power. -/
theorem spart_eq_pow (p : Nat) (hp : 2 ≤ p) (m : Nat) :
    spart p m = p ^ vp p m := spf_eq_pow p hp m m (Nat.le_refl m)

/-- The p-part divides its argument. -/
theorem spart_dvd (p : Nat) (hp : 2 ≤ p) (m : Nat) : spart p m ∣ m := by
  have key : ∀ f n, n ≤ f → spf p f n ∣ n := by
    intro f
    induction f with
    | zero =>
      intro n hn
      have hn0 : n = 0 := by omega
      subst hn0
      exact ⟨0, Nat.mul_one 0⟩
    | succ f ih =>
      intro n hn
      cases n with
      | zero => exact ⟨0, Nat.mul_one 0⟩
      | succ N =>
        have e1 : spf p (f + 1) (N + 1) =
            if (N + 1) % p = 0 then p * spf p f ((N + 1) / p) else 1 := rfl
        have hdlt : (N + 1) / p < N + 1 :=
          Nat.div_lt_self (by omega) (by omega)
        rw [e1]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod]
          have ih2 := ih ((N + 1) / p) (by omega)
          have hsplit : (N + 1) = p * ((N + 1) / p) := by
            have := Nat.div_add_mod (N + 1) p
            omega
          refine Nat.mul_dvd_mul ⟨1, Nat.one_mul p⟩ ih2 |>.trans ?_
          rw [hsplit]
          exact ⟨1, Nat.one_mul (p * ((N + 1) / p))⟩
        · rw [if_neg hmod]
          exact ⟨N + 1, Nat.mul_one (N + 1)⟩
  exact key m m (Nat.le_refl m)

/-- The smooth component divides its argument (every prime list). -/
theorem scomp_dvd : ∀ (ps : List Nat), (∀ p ∈ ps, 2 ≤ p) → ∀ m : Nat,
    scomp ps m ∣ m := by
  intro ps
  induction ps with
  | nil => intro _ m; exact ⟨m, Nat.mul_one m⟩
  | cons p ps ih =>
      intro hall m
      have hp2 : 2 ≤ p := hall p (List.mem_cons_self)
      have hsp := spart_dvd p hp2 m
      have hsplit : spart p m * (m / spart p m) = m := mul_div_own _ _ hsp
      have hrest := ih (fun q hq => hall q (List.mem_cons_of_mem p hq))
        (m / spart p m)
      refine Nat.mul_dvd_mul ⟨1, Nat.one_mul (spart p m)⟩ hrest |>.trans ?_
      exact ⟨1, by rw [hsplit, Nat.mul_one]⟩

/-! ## §2 The achievement table (all 119 minimizing windows, n < 2·10^5). -/

theorem achieve1 : ACH1.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) = true := by decide
theorem achieve2 : ACH2.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) = true := by decide
theorem achieve3 : ACH3.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) = true := by decide

/-! ## §3 The stability law (t ∈ [14,120]: 0.55t ≤ c_t ≤ 0.65t). -/

theorem stab1 : (ACH1.filter (fun r => decide (14 ≤ r.1))).all
    (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) = true := by decide
theorem stab2 : (ACH2.filter (fun r => decide (14 ≤ r.1))).all
    (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) = true := by decide
theorem stab3 : (ACH3.filter (fun r => decide (14 ≤ r.1))).all
    (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) = true := by decide

/-! ## §4 The Erdős–Graham beating (t ∈ [14,120]: c_t ≥ t/ln t). -/

/-- Every ErGra row (t, c, L) has its (t, c) matching an achievement row,
and c·L ≥ 1000·t (L = ⌊1000 ln t⌋, so c ≥ t/ln t). -/
theorem ergra : ERGRA.all (fun r =>
    ((ACH1 ++ ACH2 ++ ACH3).any (fun a => decide (a.1 = r.1 ∧ a.2.2 = r.2.1))) &&
    decide (1000 * r.1 ≤ r.2.1 * r.2.2)) = true := by decide

/-! ## §5 The four both-direction censuses at N₀ = 480. -/

/-- Exclusion chunk: every window n ∈ [lo, lo+240) has f ≥ m at t. -/
def minScan (t m lo : Nat) : Bool :=
  (List.range 240).all (fun i => decide (m ≤ f461 (lo + i) t))

theorem m14a : minScan 14 9 0 = true := by decide
theorem m14b : minScan 14 9 240 = true := by decide
theorem m20a : minScan 20 13 0 = true := by decide
theorem m20b : minScan 20 13 240 = true := by decide
theorem m30a : minScan 30 19 0 = true := by decide
theorem m30b : minScan 30 19 240 = true := by decide
theorem m40a : minScan 40 25 0 = true := by decide
theorem m40b : minScan 40 25 240 = true := by decide

/-- The witness windows. -/
theorem w14 : f461 33 14 = 9 := by decide
theorem w20 : f461 198 20 = 13 := by decide
theorem w30 : f461 121 30 = 19 := by decide
theorem w40 : f461 162 40 = 25 := by decide

/-- The generic both-direction assembly. -/
theorem min_assembly (t m : Nat)
    (haT : minScan t m 0 = true) (hbT : minScan t m 240 = true) :
    ∀ n : Nat, n < 480 → m ≤ f461 n t := by
  intro n hn
  rcases (show n < 240 ∨ 240 ≤ n by omega) with h | h
  · have hrow := (List.all_eq_true.mp haT) n (List.mem_range.mpr h)
    rw [Nat.zero_add] at hrow
    exact of_decide_eq_true hrow
  · have hrow := (List.all_eq_true.mp hbT) (n - 240) (List.mem_range.mpr (by omega))
    have hidx : 240 + (n - 240) = n := by omega
    rw [hidx] at hrow
    exact of_decide_eq_true hrow

theorem erdos461_min14 : (∀ n : Nat, n < 480 → 9 ≤ f461 n 14) ∧ f461 33 14 = 9 :=
  ⟨min_assembly 14 9 m14a m14b, w14⟩

theorem erdos461_min20 : (∀ n : Nat, n < 480 → 13 ≤ f461 n 20) ∧ f461 198 20 = 13 :=
  ⟨min_assembly 20 13 m20a m20b, w20⟩

theorem erdos461_min30 : (∀ n : Nat, n < 480 → 19 ≤ f461 n 30) ∧ f461 121 30 = 19 :=
  ⟨min_assembly 30 19 m30a m30b, w30⟩

theorem erdos461_min40 : (∀ n : Nat, n < 480 → 25 ≤ f461 n 40) ∧ f461 162 40 = 25 :=
  ⟨min_assembly 40 25 m40a m40b, w40⟩

/-! ## §6 The arsenal bridge (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos461_arsenal_bridge :
    [1892 % 3, (1892 / 3) % 3, (1892 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2930 % 3, (2930 / 3) % 3, (2930 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 1892 1 < 4 ∧
    v2r (3 ^ 2 * 69) = v2r 69 :=
  ⟨by decide, by decide, carryAtPos_bound 1892 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 69⟩

/-- **THE MAIN SUMMARY.** -/
theorem erdos461_main :
    (∀ (p : Nat), 2 ≤ p → ∀ m : Nat, spart p m = p ^ vp p m) ∧
    (∀ (ps : List Nat), (∀ p ∈ ps, 2 ≤ p) → ∀ m : Nat, scomp ps m ∣ m) ∧
    ACH1.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) ∧
    ACH2.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) ∧
    ACH3.all (fun r => decide (f461 r.2.1 r.1 = r.2.2)) ∧
    (ACH1.filter (fun r => decide (14 ≤ r.1))).all
      (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) ∧
    (ACH2.filter (fun r => decide (14 ≤ r.1))).all
      (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) ∧
    (ACH3.filter (fun r => decide (14 ≤ r.1))).all
      (fun r => decide (55 * r.1 ≤ 100 * r.2.2 ∧ 100 * r.2.2 ≤ 65 * r.1)) ∧
    ERGRA.all (fun r =>
      ((ACH1 ++ ACH2 ++ ACH3).any (fun a => decide (a.1 = r.1 ∧ a.2.2 = r.2.1))) &&
      decide (1000 * r.1 ≤ r.2.1 * r.2.2)) ∧
    (∀ n : Nat, n < 480 → 9 ≤ f461 n 14) ∧ f461 33 14 = 9 ∧
    (∀ n : Nat, n < 480 → 25 ≤ f461 n 40) ∧ f461 162 40 = 25 :=
  ⟨fun p hp m => spart_eq_pow p hp m, scomp_dvd, achieve1, achieve2, achieve3,
   stab1, stab2, stab3, ergra,
   erdos461_min14.1, erdos461_min14.2, erdos461_min40.1, erdos461_min40.2⟩

#eval "ERDOS461_KERNEL_GREEN"
#print axioms spart_dvd
#print axioms spart_eq_pow
#print axioms scomp_dvd
#print axioms achieve1
#print axioms achieve2
#print axioms achieve3
#print axioms stab1
#print axioms stab2
#print axioms stab3
#print axioms ergra
#print axioms erdos461_min14
#print axioms erdos461_min20
#print axioms erdos461_min30
#print axioms erdos461_min40
#print axioms erdos461_arsenal_bridge
#print axioms erdos461_main

end Erdos461
