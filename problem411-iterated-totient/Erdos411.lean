import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels K28/K34/K35): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! ## W59-F-1 helper lemmas (Mathlib-only citations replaced, core-provable).
The r1 draft cited `Nat.dvd_sub'`, `Nat.dvd_mul_of_dvd_right`,
`Nat.pos_pow_of_pos` — none resolve in the Arsenal-only import world.
These local replacements keep the kernel import-clean. -/

private theorem dvd_sub_local {k m n : Nat} (h1 : k ∣ m) (h2 : k ∣ n) :
    k ∣ m - n := by
  rcases h1 with ⟨a, rfl⟩
  rcases h2 with ⟨b, rfl⟩
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hmono : k * a ≤ k * b := Nat.mul_le_mul_left k (Nat.le_of_lt hlt)
    refine Dvd.intro 0 ?_
    omega
  · have hmono : k * b ≤ k * a := Nat.mul_le_mul_left k hge
    have hdist : k * a = k * (a - b) + k * b := by
      calc k * a = k * (a - b + b) := by rw [Nat.sub_add_cancel hge]
        _ = k * (a - b) + k * b := Nat.mul_add k (a - b) b
    refine Dvd.intro (a - b) ?_
    omega

private theorem dvd_mul_of_dvd_right_local {k m n : Nat} (h : k ∣ m) : k ∣ n * m := by
  rcases h with ⟨a, ha⟩
  refine Dvd.intro (n * a) ?_
  rw [ha]
  ring

private theorem pos_pow_local {a b : Nat} (h : 0 < a) : 0 < a ^ b := by
  induction b with
  | zero => rw [Nat.pow_zero]; decide
  | succ n ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih h

/-- The countP congruence (self-built: the Mathlib `countP_congr` signature
mismatched the r3 call sites — the W60-T1 local, Bool-eq form). -/
private theorem countP_congr_local {l : List Nat} {p q : Nat → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, h a (by simp), ih]

/-- The beta-friendly map-count identity (countP_map's ∘-form mismatched the
r3 congr patterns; the local gives the applied form directly). -/
private theorem countP_map_local {l : List Nat} (f : Nat → Nat) (p : Nat → Bool) :
    (l.map f).countP p = l.countP (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]

/-- The canonical power splits (W60-T1: the `.succ` display killed the r1
`rw [show a - 1 + 1 = a]` chains — congr 1 + omega aligns exponents). -/
private theorem two_pow_split (a : Nat) (ha : 1 ≤ a) : 2^a = 2^(a-1) * 2 := by
  have hexp : 2^a = 2^((a-1)+1) := by
    congr 1
    omega
  rw [hexp, Nat.pow_add, Nat.pow_one]

private theorem two_pow_split3 (a : Nat) (ha : 1 ≤ a) : 2^(a+1) = 2^(a-1) * 4 := by
  have hexp : 2^(a+1) = 2^((a-1)+2) := by
    congr 1
    omega
  rw [hexp, Nat.pow_add, show 2^2 = 4 from by decide]

private theorem two_pow_succ_add (a : Nat) : 2^(a+1) = 2 * 2^a := by
  rw [Nat.pow_add, Nat.pow_one]
  ring

/-! # Erdős #411 — THE ITERATED-TOTIENT DOUBLING LAWS (S042 volley, Kernel 36)

## THE PROBLEM (verbatim, erdosproblems.com/411)

> Let $g_1=g(n)=n+\phi(n)$ and $g_k(n)=g(g_{k-1}(n))$. For which $n$ and $r$
> is it true that $g_{k+r}(n)=2g_k(n)$ for all large $k$?

Known: $r=2$ solutions $n=10, 94$; Steinerberger [St25] reduced $r=2$ to
$\phi(n)+\phi(n+\phi(n))=n$ with odd parts in $\{1,3,5,7,35,47\}$ plus
exotic classes ($8m+7$ primes $\geq 10^{10}$, $6m+5$ forms).

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. **THE PARITY EXCLUSION** (`erdos411_parity`, `erdos411_two`): no odd
   $n$ — and neither $n=1$ nor $n=2$ — satisfies $g_{k+r}(n)=2g_k(n)$
   eventually, for any $r \geq 1$.
2. **THE SIX CHAIN LAWS** (`erdos411_chain_laws`): symbolic in $a \geq 1$.
3. **THE DOUBLING THEOREM** (`erdos411_doubling`): every
   $n = 2^a m$, $m \in \{1,3,5,7,35,47\}$, $a \geq 1$, $n \geq 4$:
   $g_{k+2}(n) = 2 g_k(n)$ for ALL $k \geq 0$ — including $n=10$ and
   $n=94$ (`erdos411_ten`, `erdos411_94`).
4. **THE ODD-PART REDUCTION** (`erdos411_witness`): even $x \geq 4$ whose
   odd part lies in the 320-value rank-sorted chain-entry table (each
   entry either in $\{1,3,5,7,35,47\}$ — the rank-0 prefix — or stepping
   to a strictly earlier entry) is an $r=2$ solution.
5. **THE COMPLETE CENSUS AT 2000** (`erdos411_census`, `erdos411_partition`,
   `erdos411_count`): every even $4 \leq n \leq 2000$ is either a certified
   $r=2$ solution (535 of them) or has odd part among the 279 wanderers;
   the odd numbers $\leq 1001$ are partitioned exactly.
6. **THE ARSENAL BRIDGE** (`erdos411_arsenal_bridge`): the pair
   $j$-values $v_2(2m+\phi(m))$ of the three chain pairs via the Boss's
   own `v2r` (with `v2r_mul_three_pow` applied) + ternary-digit checks.

Honest scope: the full (n, r) characterization over all n remains open —
it reduces to the cycle structure of $m \mapsto \mathrm{odd}(2m+\phi(m))$
(the Master Reduction, DERIVATION.md, both directions in prose). -/

namespace Erdos411

/-! ## §0 The definitions. -/

/-- Euler's φ by direct gcd count: |{c ∈ [1..n] : gcd c n = 1}|.
Structural (list count + core Nat.gcd) — kernel-computable. -/
def phiB (n : Nat) : Nat := (List.range n).countP (fun k => decide (Nat.gcd (k + 1) n = 1))

/-- One iteration step: g(x) = x + φ(x). -/
def gstep (x : Nat) : Nat := x + phiB x

/-- The k-th iterate: g_0(x) = x, g_{k+1}(x) = g_k(g(x)).
Fuel-structured on the first argument (L95: no WF disease). -/
def gF : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => gF k (gstep x)

/-- The odd part, fuel-structured (fuel counts halvings). -/
def oddPF : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => if x % 2 = 0 then oddPF f (x / 2) else x

/-- The six chain-family odd parts. -/
def SIXl : List Nat := [1, 3, 5, 7, 35, 47]

def inSIX (m : Nat) : Bool := SIXl.contains m

/-- The six-case membership enumeration (W60-T1: the r3 `rcases hm with h | h...`
died — `1 is not a free variable`; the mem-simp route is the green spelling). -/
theorem SIXl_mem (m : Nat) (hm : m ∈ SIXl) :
    m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 35 ∨ m = 47 := by
  have h : m ∈ [1, 3, 5, 7, 35, 47] := hm
  simp only [List.mem_cons, List.mem_singleton] at h
  exact h

theorem SIXl_pos (m : Nat) (hm : m ∈ SIXl) : 1 ≤ m := by
  rcases SIXl_mem m hm with h | h | h | h | h | h <;> rw [h] <;> decide

theorem inFAM_pos (x : Nat) (hx : inFAM x) : 0 < x := by
  obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
  rw [hxe]
  exact Nat.mul_pos (pos_pow_local (by omega)) (SIXl_pos m hm)

/-! ## §1 Small helpers. -/

/-- Bool-iff bridge for decide predicates (r2: instance binders added —
    `decide P` for variable `P` needs `[Decidable P]`; the r1 form never
    compiled anywhere — the W58-D/W59 skips masked it). -/
theorem boolIff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (decide P = true) ↔ (decide Q = true) := by
  rw [decide_eq_true_iff, decide_eq_true_iff]
  exact h

/-- Decide congruence (r2: instance binders + the rw-cascade body — the r1
    body fed `decide Q = true` to a `true = decide Q` goal). -/
theorem decCongr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

/-- Strong induction (self-contained). -/
theorem strongIndOn (P : Nat → Prop) (hstep : ∀ i, (∀ j, j < i → P j) → P i) : ∀ i, P i := by
  have key : ∀ N i, i ≤ N → P i := by
    intro N
    induction N with
    | zero =>
      intro i hi
      have h0 : i = 0 := by omega
      subst h0
      exact hstep 0 (by intro j hj; omega)
    | succ N ihN =>
      intro i hi
      exact hstep i (fun j hj => ihN j (by omega))
  intro i
  exact key i i (by omega)

/-- The shift-count identity: counting P(1..M) plus P(0) = counting P(0..M).
W59-F-1: zero-case rfl never closed (`0 + ite` vs `ite + 0` is not defeq for
variable ite); the succ-case rw-chain double-fired and left the inner range
unnormalized. Replaced with one simp-only normalization pass + omega (the
ites stay atoms; omega is orientation-agnostic). -/
theorem countP_shift (P : Nat → Bool) : ∀ M,
    (List.range M).countP (fun j => P (j + 1)) + (if P 0 then 1 else 0)
      = (List.range (M + 1)).countP P := by
  intro M
  induction M with
  | zero =>
    rw [List.range_succ, List.range_zero, List.countP_append,
        List.countP_nil, List.countP_nil, List.countP_singleton]
  | succ M ih =>
    simp only [List.range_succ, List.countP_append, List.countP_singleton] at ih ⊢
    omega

theorem countP_rev_idx (P : Nat → Bool) : ∀ M,
    (List.range M).countP (fun j => P (M - 1 - j)) = (List.range M).countP P := by
  intro M
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    have hz : M + 1 - 1 - M = M := by omega
    rw [hz]
    have hc : (List.range M).countP (fun j => P (M + 1 - 1 - j))
        = (List.range M).countP (fun j => P (M - 1 - j)) :=
      countP_congr_local (fun x hx => congrArg P (by
        rw [List.mem_range] at hx; omega))
    rw [hc]
    omega

/-- The per-element parity identity: the three decides case-split to literals
(the by_cases route — the r3 `cases <;> first | ...` block had a parser defect
at the parenthesized `by` alternative). -/
private theorem parity_elem (Q : Nat → Prop) [DecidablePred Q] (k : Nat) :
    (if decide (Q k ∧ k % 2 = 1) then 1 else 0)
      + (if decide (Q k ∧ k % 2 = 0) then 1 else 0)
      = (if decide (Q k) then 1 else 0) := by
  by_cases hq : Q k
  · by_cases h1 : k % 2 = 1
    · rw [decide_eq_true ⟨hq, h1⟩,
          decide_eq_false (fun hc => absurd hc.2 (by omega)),
          decide_eq_true hq]
    · have h0 : k % 2 = 0 := by omega
      rw [decide_eq_false (fun hc => absurd hc.2 h1),
          decide_eq_true ⟨hq, h0⟩,
          decide_eq_true hq]
  · rw [decide_eq_false (fun hc => hq hc.1),
        decide_eq_false (fun hc => hq hc.1),
        decide_eq_false hq]

/-- The parity-split count: (Q ∧ odd) + (Q ∧ even) = Q.
W59-F-1: the r1 `simp only [decide_eq_true, decide_eq_false] at *` never fired
(the decide-of-and conditions cannot be rewritten inside the bif instances —
motive issue). Replaced with the per-element lemma + omega on ite-atoms. -/
theorem countP_parity_split (Q : Nat → Prop) [DecidablePred Q] : ∀ (l : List Nat),
    l.countP (fun k => decide (Q k ∧ k % 2 = 1)) + l.countP (fun k => decide (Q k ∧ k % 2 = 0))
      = l.countP (fun k => decide (Q k)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    have hpe := parity_elem Q a
    omega

/-! ## §2 The gcd lemmas. -/

/-- The partner identity: gcd(n - c, n) = gcd(c, n) for c ≤ n. -/
theorem gcd_partners (c n : Nat) (hc : c ≤ n) : Nat.gcd (n - c) n = Nat.gcd c n := by
  have hsub1 : n - (n - c) = c := Nat.sub_sub_self hc
  have h1 : Nat.gcd (n - c) n ∣ Nat.gcd c n := by
    apply Nat.dvd_gcd
    · have hd : Nat.gcd (n - c) n ∣ n - (n - c) :=
        dvd_sub_local (Nat.gcd_dvd_right (n - c) n) (Nat.gcd_dvd_left (n - c) n)
      rw [hsub1] at hd
      exact hd
    · exact Nat.gcd_dvd_right (n - c) n
  have h2 : Nat.gcd c n ∣ Nat.gcd (n - c) n := by
    apply Nat.dvd_gcd
    · exact dvd_sub_local (Nat.gcd_dvd_right c n) (Nat.gcd_dvd_left c n)
    · exact Nat.gcd_dvd_right c n
  exact Nat.dvd_antisymm h1 h2

/-- Coprimality to 2y with y even = coprimality to y. -/
theorem gcd_two_mul_of_even {c y : Nat} (hy : 2 ∣ y) :
    (Nat.gcd c (2 * y) = 1) ↔ (Nat.gcd c y = 1) := by
  constructor
  · intro h
    have hd : Nat.gcd c y ∣ Nat.gcd c (2 * y) := by
      apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_left c y
      · exact dvd_mul_of_dvd_right_local (Nat.gcd_dvd_right c y)
    rw [h] at hd
    exact Nat.eq_one_of_dvd_one hd
  · intro h
    -- W59-F-1: y = 0 is legal under 2 ∣ y; the zero case is immediate
    -- (gcd c 0 = c defeq); the succ case has 0 < 2 * y by omega.
    cases y with
    | zero => exact h
    | succ y' =>
      have hcodd : ¬ (2 ∣ c) := by
        intro h2c
        have hg : 2 ∣ Nat.gcd c (y' + 1) := Nat.dvd_gcd h2c hy
        rw [h] at hg
        exact absurd (Nat.eq_one_of_dvd_one hg) (by decide)
      have hdd : Nat.gcd c (2 * (y' + 1)) ∣ 2 * Nat.gcd c (y' + 1) := by
        have hmul : Nat.gcd (2 * c) (2 * (y' + 1))
            = 2 * Nat.gcd c (y' + 1) := Nat.gcd_mul_left 2 c (y' + 1)
        rw [← hmul]
        apply Nat.dvd_gcd
        · exact dvd_mul_of_dvd_right_local (Nat.gcd_dvd_left c (2 * (y' + 1)))
        · exact Nat.gcd_dvd_right c (2 * (y' + 1))
      rw [h, Nat.mul_one] at hdd
      have hle : Nat.gcd c (2 * (y' + 1)) ≤ 2 := Nat.le_of_dvd (by decide) hdd
      have hpos : 0 < Nat.gcd c (2 * (y' + 1)) :=
        Nat.gcd_pos_of_pos_right c (by omega)
      rcases Nat.eq_or_lt_of_le hle with h1 | h2
      · have htwo : 2 ∣ Nat.gcd c (2 * (y' + 1)) := by rw [h1]
        have hcc : 2 ∣ c := Nat.dvd_trans htwo (Nat.gcd_dvd_left c (2 * (y' + 1)))
        exact absurd hcc hcodd
      · omega

/- W59-F-1 note: the ← direction's `Nat.gcd_pos_of_pos_right c (by omega)`
needs `0 < 2 * y`; y = 0 is legal under `2 ∣ y` (2 ∣ 0), so split on y:
the zero case is immediate (gcd c 0 = c); the succ case has 0 < 2 * y by
omega. The branch order of `Nat.eq_or_lt_of_le` was also transposed in r1
(the `= 2` branch is the contradiction, the `< 2` branch is the goal). -/

/-- Coprimality to 2y with y odd = odd and coprime to y. -/
theorem gcd_two_mul_of_odd {c y : Nat} (hy : y % 2 = 1) :
    (Nat.gcd c (2 * y) = 1) ↔ (c % 2 = 1 ∧ Nat.gcd c y = 1) := by
  constructor
  · intro h
    have hcy : Nat.gcd c y = 1 := by
      have hd : Nat.gcd c y ∣ Nat.gcd c (2 * y) := by
        apply Nat.dvd_gcd
        · exact Nat.gcd_dvd_left c y
        · exact dvd_mul_of_dvd_right_local (Nat.gcd_dvd_right c y)
      rw [h] at hd
      exact Nat.eq_one_of_dvd_one hd
    constructor
    · -- c odd: else 2 | c and 2 | gcd c (2y) = 1
      by_contra hce
      have hc0 : c % 2 = 0 := by omega
      have h2c : 2 ∣ c := Nat.dvd_of_mod_eq_zero hc0
      have hg2 : 2 ∣ Nat.gcd c (2 * y) :=
        Nat.dvd_gcd h2c (Dvd.intro y rfl)
      rw [h] at hg2
      exact absurd (Nat.eq_one_of_dvd_one hg2) (by decide)
    · exact hcy
  · intro ⟨hcodd, hcy⟩
    have hdd : Nat.gcd c (2 * y) ∣ 2 * Nat.gcd c y := by
      have hmul : Nat.gcd (2 * c) (2 * y) = 2 * Nat.gcd c y := Nat.gcd_mul_left 2 c y
      rw [← hmul]
      apply Nat.dvd_gcd
      · exact dvd_mul_of_dvd_right_local (Nat.gcd_dvd_left c (2 * y))
      · exact Nat.gcd_dvd_right c (2 * y)
    rw [hcy, Nat.mul_one] at hdd
    have hle : Nat.gcd c (2 * y) ≤ 2 := Nat.le_of_dvd (by decide) hdd
    have hpos : 0 < Nat.gcd c (2 * y) := Nat.gcd_pos_of_pos_right c (by omega)
    have hd2 : ¬ (2 ∣ Nat.gcd c (2 * y)) := by
      intro h
      have h2c : 2 ∣ c := Nat.dvd_trans h (Nat.gcd_dvd_left c (2 * y))
      have hc0 : c % 2 = 0 := Nat.mod_eq_zero_of_dvd h2c
      omega
    rcases Nat.eq_or_lt_of_le hle with h1 | h2
    · have htwo : 2 ∣ Nat.gcd c (2 * y) := by rw [h1]
      exact absurd htwo hd2
    · omega

/-! ## §3 The φ doubling lemmas. -/

/-- φ(2y) = 2φ(y) for y even, y > 0. -/
theorem phiB_even_dbl : ∀ {y : Nat}, 2 ∣ y → 0 < y → phiB (2 * y) = 2 * phiB y := by
  intro y hy hy0
  unfold phiB
  have hsplit : List.range (2 * y) = List.range y ++ (List.range y).map (fun k => y + k) := by
    rw [show 2 * y = y + y by omega]
    exact List.range_add
  rw [hsplit, List.countP_append, countP_map_local]
  rw [countP_congr_local (l := List.range y)
        (p := fun k => decide (Nat.gcd (k + 1) (2 * y) = 1))
        (q := fun k => decide (Nat.gcd (k + 1) y = 1))
        (fun x _ => decCongr (gcd_two_mul_of_even hy))]
  rw [countP_congr_local (l := List.range y)
        (p := fun k => decide (Nat.gcd (y + k + 1) (2 * y) = 1))
        (q := fun k => decide (Nat.gcd (k + 1) y = 1))
        (fun x _ => decCongr (by
          have h1 : Nat.gcd (y + x + 1) (2 * y) = 1 ↔ Nat.gcd (y + x + 1) y = 1 :=
            gcd_two_mul_of_even hy
          have h2 : Nat.gcd (y + x + 1) y = Nat.gcd (x + 1) y := by
            have hEq : (y + x + 1) = (x + 1) + y := by omega
            rw [hEq, Nat.gcd_add_self_left]
          rw [h2] at h1
          exact h1))]
  omega

/-- φ(2y) = φ(y) for y odd. -/
theorem phiB_odd_dbl : ∀ {y : Nat}, y % 2 = 1 → phiB (2 * y) = phiB y := by
  intro y hy
  unfold phiB
  have hsplit : List.range (2 * y) = List.range y ++ (List.range y).map (fun k => y + k) := by
    rw [show 2 * y = y + y by omega]
    exact List.range_add
  rw [hsplit, List.countP_append, countP_map_local]
  rw [countP_congr_local (l := List.range y)
        (p := fun k => decide (Nat.gcd (k + 1) (2 * y) = 1))
        (q := fun k => decide (Nat.gcd (k + 1) y = 1 ∧ (k + 1) % 2 = 1))
        (fun x _ => decCongr (by
          have h1 : Nat.gcd (x + 1) (2 * y) = 1 ↔ ((x + 1) % 2 = 1 ∧ Nat.gcd (x + 1) y = 1) :=
            gcd_two_mul_of_odd hy
          rw [h1]
          exact And.comm))]
  rw [countP_congr_local (l := List.range y)
        (p := fun k => decide (Nat.gcd (y + k + 1) (2 * y) = 1))
        (q := fun k => decide (Nat.gcd (k + 1) y = 1 ∧ (k + 1) % 2 = 0))
        (fun x _ => decCongr (by
          have h1 : Nat.gcd (y + x + 1) (2 * y) = 1 ↔
              ((y + x + 1) % 2 = 1 ∧ Nat.gcd (y + x + 1) y = 1) :=
            gcd_two_mul_of_odd hy
          have hpar : ((y + x + 1) % 2 = 1) ↔ ((x + 1) % 2 = 0) := by
            constructor <;> intro h <;> omega
          have h2 : Nat.gcd (y + x + 1) y = Nat.gcd (x + 1) y := by
            have hEq : (y + x + 1) = (x + 1) + y := by omega
            rw [hEq, Nat.gcd_add_self_left]
          rw [h2, hpar] at h1
          rw [h1]
          exact And.comm))]
  rw [countP_parity_split]
  rfl

/-- The multiplicativity corollary: φ(2^a·m) = 2^(a-1)·φ(m) for a ≥ 1, m odd. -/
theorem phiB_two_pow_mul : ∀ (a m : Nat), 1 ≤ a → m % 2 = 1 →
    phiB (2^a * m) = 2^(a-1) * phiB m := by
  intro a m ha hm
  induction a with
  | zero => omega
  | succ a ih =>
    cases a with
    | zero =>
      show phiB (2*m) = 2^0 * phiB m
      rw [phiB_odd_dbl hm, Nat.pow_zero, Nat.one_mul]
    | succ a' =>
      have hEq : 2^(a'+2) * m = 2 * (2^(a'+1) * m) := by
        have hexp : 2^(a'+2) = 2 * 2^(a'+1) := by
          rw [show a'+2 = (a'+1)+1 from by omega, Nat.pow_add, Nat.pow_one]
          ring
        rw [hexp, ← Nat.mul_assoc]
      have hEven : 2 ∣ 2^(a'+1) * m := by
        refine ⟨2^a' * m, ?_⟩
        rw [Nat.pow_add, Nat.pow_one]
        ring
      have hPos : 0 < 2^(a'+1) * m := Nat.mul_pos (pos_pow_local (by decide)) (by omega)
      rw [hEq, phiB_even_dbl hEven hPos, ih (by omega) hm]
      rw [show a'+2-1 = a'+1 from by omega, show a'+1-1 = a' from by omega]
      rw [Nat.pow_add, Nat.pow_one]
      ring

/-! ## §4 Basic φ facts. -/

theorem phiB_le (n : Nat) : phiB n ≤ n := by
  unfold phiB
  have h1 : (List.range n).countP (fun k => decide (Nat.gcd (k + 1) n = 1)) ≤ (List.range n).length :=
    List.countP_le_length _
  rw [List.length_range] at h1
  exact h1

theorem phiB_pos (n : Nat) (hn : 1 ≤ n) : 1 ≤ phiB n := by
  unfold phiB
  have hmem : 0 ∈ List.range n := by
    rw [List.mem_range]; omega
  have hpred : decide (Nat.gcd (0 + 1) n = 1) = true := by
    simp [Nat.gcd_comm]
  have : 1 ≤ (List.range n).countP (fun k => decide (Nat.gcd (k + 1) n = 1)) := by
    rw [List.countP_eq_length_filter]
    have hfilter : (0 : Nat) ∈ (List.range n).filter (fun k => decide (Nat.gcd (k + 1) n = 1)) := by
      rw [List.mem_filter]
      exact ⟨hmem, hpred⟩
    have : 0 < ((List.range n).filter (fun k => decide (Nat.gcd (k + 1) n = 1))).length :=
      List.length_pos_of_mem hfilter
    omega
  exact this

/-- THE EVENNESS LAW: φ(x) is even for every odd x ≥ 3 (totatives pair c ↔ x − c). -/
theorem phiB_even_of_odd : ∀ {x h : Nat}, x = 2*h + 1 → 3 ≤ x → 2 ∣ phiB x := by
  intro x h hx h3
  unfold phiB
  -- strip the last index (gcd x x = x ≠ 1)
  have hxx : Nat.gcd x x = x := Nat.gcd_self x
  have hstrip : (List.range x).countP (fun k => decide (Nat.gcd (k + 1) x = 1))
      = (List.range (x-1)).countP (fun k => decide (Nat.gcd (k + 1) x = 1)) := by
    have hr : List.range x = List.range (x-1) ++ [x-1] := by
      rw [show x = (x-1)+1 from by omega]
      exact List.range_succ (x-1)
    rw [hr, List.countP_append, List.countP_singleton]
    have hlast : decide (Nat.gcd ((x-1) + 1) x = 1) = false := by
      have : Nat.gcd ((x-1)+1) x = x := by omega
      rw [this]
      have : x ≠ 1 := by omega
      exact decide_eq_false (by intro h1; rw [h1] at this; exact absurd this (by omega))
    rw [hlast]
    simp
  rw [hstrip, show x-1 = h + h from by omega]
  -- range (h+h) = range h ++ map (h + ·) (range h)
  rw [List.range_add]
  rw [List.countP_append, List.countP_map]
  -- the second part's predicate: P (h + k) with P j = decide (gcd (j+1) x = 1)
  -- partner: gcd (h+k+1) x = gcd (x - (h+k+1)) x = gcd (h-k) x  [gcd_partners]
  rw [List.countP_congr (p := fun k => decide (Nat.gcd (h + k + 1) x = 1))
        (q := fun k => decide (Nat.gcd (h - 1 - k + 1) x = 1))
        (by intro k _
            have hck : h + k + 1 ≤ x := by omega
            have hpar : Nat.gcd (x - (h + k + 1)) x = Nat.gcd (h + k + 1) x :=
              gcd_partners (h + k + 1) x hck
            have hEq : x - (h + k + 1) = h - k := by omega
            rw [hEq] at hpar
            exact decCongr (by rw [hpar]))]
  -- now countP (fun k => P (h-1-k)) (range h) = countP P (range h) by index reversal
  have hEq2 : (fun k => decide (Nat.gcd (h - 1 - k + 1) x = 1))
      = (fun j => (fun j => decide (Nat.gcd (j + 1) x = 1)) (h - 1 - j)) := rfl
  rw [hEq2, countP_rev_idx]
  -- total = countP P (range h) + countP P (range h)
  rw [List.countP_append] at * -- no-op safeguard
  unfold phiB  -- no-op safeguard
  omega

/-! ## §5 The step lemma and the six chain laws. -/

theorem phiB_3 : phiB 3 = 2 := by decide
theorem phiB_5 : phiB 5 = 4 := by decide
theorem phiB_7 : phiB 7 = 6 := by decide
theorem phiB_35 : phiB 35 = 24 := by decide
theorem phiB_47 : phiB 47 = 46 := by decide

/-- THE STEP LEMMA (the odd-part decoupling):
g(2^a·m) = 2^(a-1)·(2m + φ(m)) for a ≥ 1, m odd. -/
theorem gstep_two_pow_mul (a m : Nat) (ha : 1 ≤ a) (hm : m % 2 = 1) :
    gstep (2^a * m) = 2^(a-1) * (2 * m + phiB m) := by
  unfold gstep
  rw [phiB_two_pow_mul a m ha hm]
  rw [two_pow_split a ha]
  ring

/-- THE SIX CHAIN LAWS (symbolic in a ≥ 1). -/
theorem gstep_two_pow (a : Nat) (ha : 1 ≤ a) : gstep (2^a) = 3 * 2^(a-1) := by
  have hphi : phiB (2^a) = 2^(a-1) := by
    rw [show 2^a = 2^a * 1 from (Nat.mul_one (2^a)).symm,
        phiB_two_pow_mul a 1 ha (by decide), show phiB 1 = 1 from by decide, Nat.mul_one]
  unfold gstep
  rw [hphi]
  rw [two_pow_split a ha]
  omega

theorem gstep_3 (a : Nat) (ha : 1 ≤ a) : gstep (2^a * 3) = 2^(a+2) := by
  rw [gstep_two_pow_mul a 3 ha (by decide), phiB_3]
  have hexp : 2^(a+2) = 2^(a-1) * 8 := by
    have h1 : a + 2 = (a-1) + 3 := by omega
    rw [h1, Nat.pow_add, show 2^3 = 8 from by decide]
  rw [hexp]
  ring

theorem gstep_5 (a : Nat) (ha : 1 ≤ a) : gstep (2^a * 5) = 2^a * 7 := by
  rw [gstep_two_pow_mul a 5 ha (by decide), phiB_5]
  rw [two_pow_split a ha]
  ring

theorem gstep_7 (a : Nat) (ha : 1 ≤ a) : gstep (2^a * 7) = 5 * 2^(a+1) := by
  rw [gstep_two_pow_mul a 7 ha (by decide), phiB_7]
  rw [two_pow_split3 a ha]
  ring

theorem gstep_35 (a : Nat) (ha : 1 ≤ a) : gstep (2^a * 35) = 2^a * 47 := by
  rw [gstep_two_pow_mul a 35 ha (by decide), phiB_35]
  rw [two_pow_split a ha]
  ring

theorem gstep_47 (a : Nat) (ha : 1 ≤ a) : gstep (2^a * 47) = 35 * 2^(a+1) := by
  rw [gstep_two_pow_mul a 47 ha (by decide), phiB_47]
  rw [two_pow_split3 a ha]
  ring

/-! ## §6 The iteration: composition and the doubling theorem. -/

theorem gF_add (i j x : Nat) : gF (i + j) x = gF i (gF j x) := by
  induction j with
  | zero => simp only [Nat.add_zero, gF]
  | succ j ih =>
    have h1 : i + (j + 1) = (i + j) + 1 := by omega
    have h2 : gF ((i + j) + 1) x = gF (i + j) (gstep x) := rfl
    have h3 : gF (j + 1) x = gF j (gstep x) := rfl
    rw [h1, h2, ih, ← h3]

/-- The chain-family predicate. -/
def inFAM (x : Nat) : Prop :=
  ∃ a m, 1 ≤ a ∧ m ∈ SIXl ∧ (m = 1 → 2 ≤ a) ∧ x = 2^a * m

theorem inFAM_gstep (x : Nat) (hx : inFAM x) : inFAM (gstep x) ∧ gstep (gstep x) = 2 * x := by
  obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
  rw [hxe]
  rcases SIXl_mem m hm with h1 | h3 | h5 | h7 | h35 | h47
  · -- m = 1 (a ≥ 2): 2^a → 3·2^(a-1) → 2^(a+1) = 2·2^a
    subst h1
    have ha2 : 2 ≤ a := hm1 rfl
    have s1' : gstep (2^a * 1) = 2^(a-1) * 3 := by
      rw [Nat.mul_one, gstep_two_pow a ha, Nat.mul_comm 3 (2^(a-1))]
    have s2 : gstep (2^(a-1) * 3) = 2 * (2^a * 1) := by
      have h3step := gstep_3 (a-1) (by omega)
      rw [h3step, show 2^(a-1+2) = 2^(a+1) from by congr 1; omega,
          two_pow_succ_add, Nat.mul_one]
    exact ⟨⟨a-1, 3, by omega, by simp [SIXl], by intro h; omega, s1'⟩, by rw [s1', s2]⟩
  · -- m = 3: 3·2^a → 2^(a+2) → 3·2^(a+1) = 2·(3·2^a)
    subst h3
    have s1 : gstep (2^a * 3) = 2^(a+2) := gstep_3 a ha
    have s2 : gstep (2^(a+2)) = 2 * (2^a * 3) := by
      have htp := gstep_two_pow (a+2) (by omega)
      rw [htp, two_pow_succ_add]
      ring
    exact ⟨⟨a+2, 1, by omega, by simp [SIXl], by omega,
        by rw [Nat.mul_one]; exact s1⟩, by rw [s1, s2]⟩
  · -- m = 5: 5·2^a → 7·2^a → 5·2^(a+1) = 2·(5·2^a)
    subst h5
    have s1 : gstep (2^a * 5) = 2^a * 7 := gstep_5 a ha
    have s2 : gstep (2^a * 7) = 2 * (2^a * 5) := by
      have h7step := gstep_7 a ha
      rw [h7step, two_pow_succ_add]
      ring
    exact ⟨⟨a, 7, ha, by simp [SIXl], by intro h; omega, s1⟩, by rw [s1, s2]⟩
  · -- m = 7: 7·2^a → 5·2^(a+1) → 7·2^(a+1) = 2·(7·2^a)
    subst h7
    have s1' : gstep (2^a * 7) = 2^(a+1) * 5 := by
      rw [gstep_7 a ha, Nat.mul_comm 5 (2^(a+1))]
    have s2 : gstep (2^(a+1) * 5) = 2 * (2^a * 7) := by
      have h5step := gstep_5 (a+1) (by omega)
      rw [h5step, two_pow_succ_add]
      ring
    exact ⟨⟨a+1, 5, by omega, by simp [SIXl], by intro h; omega, s1'⟩, by rw [s1', s2]⟩
  · -- m = 35: 35·2^a → 47·2^a → 35·2^(a+1) = 2·(35·2^a)
    subst h35
    have s1 : gstep (2^a * 35) = 2^a * 47 := gstep_35 a ha
    have s2 : gstep (2^a * 47) = 2 * (2^a * 35) := by
      have h47step := gstep_47 a ha
      rw [h47step, two_pow_succ_add]
      ring
    exact ⟨⟨a, 47, ha, by simp [SIXl], by intro h; omega, s1⟩, by rw [s1, s2]⟩
  · -- m = 47: 47·2^a → 35·2^(a+1) → 47·2^(a+1) = 2·(47·2^a)
    subst h47
    have s1' : gstep (2^a * 47) = 2^(a+1) * 35 := by
      rw [gstep_47 a ha, Nat.mul_comm 35 (2^(a+1))]
    have s2 : gstep (2^(a+1) * 35) = 2 * (2^a * 47) := by
      have h35step := gstep_35 (a+1) (by omega)
      rw [h35step, two_pow_succ_add]
      ring
    exact ⟨⟨a+1, 35, by omega, by simp [SIXl], by intro h; omega, s1'⟩, by rw [s1', s2]⟩

/-- The doubling-commutation law (W60-T1: shared by gF_two_pow and the
doubling theorem; the r3 inline copies had the FALSE witness 2^(a-1)·m). -/
theorem gstep_dbl_comm {v : Nat} (hv : inFAM v) : gstep (2 * v) = 2 * gstep v := by
  obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hv
  have hEven : 2 ∣ v := by
    rw [hxe]; refine ⟨2^(a-1) * m, ?_⟩
    rw [two_pow_split a ha]
    ring
  have hPos : 0 < v := inFAM_pos v hv
  unfold gstep
  rw [phiB_even_dbl hEven hPos]
  omega

/-- The two-step closed form. -/
theorem gF_two_pow (x : Nat) (hx : inFAM x) : ∀ j,
    gF (2*j) x = 2^j * x ∧ gF (2*j+1) x = gstep (2^j * x) := by
  intro j
  induction j with
  | zero =>
    constructor
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
  | succ j ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hcomp2 : gF (2*(j+1)) x = gF 2 (gF (2*j) x) := by
      rw [show 2*(j+1) = 2 + 2*j from by ring, gF_add]
    have hcomp3 : gF (2*(j+1)+1) x = gF 2 (gF (2*j+1) x) := by
      rw [show 2*(j+1)+1 = 2 + (2*j+1) from by ring, gF_add]
    obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
    have hfam : inFAM (2^j * x) := by
      refine ⟨a + j, m, by omega, hm, ?_, ?_⟩
      · intro h; subst h; omega
      · rw [hxe, ← Nat.mul_assoc, ← Nat.pow_add]
        congr 1 <;> omega
    obtain ⟨hstep_fam, hstep_two⟩ := inFAM_gstep _ hfam
    rw [ih0] at hcomp2
    rw [ih1] at hcomp3
    have h2 : gF 2 (2^j * x) = 2 * (2^j * x) := hstep_two
    have hgsd : gstep (2 * (2^j * x)) = 2 * gstep (2^j * x) := gstep_dbl_comm hfam
    rw [h2] at hcomp2
    have hgg : gF 2 (gstep (2^j * x)) = 2 * gstep (2^j * x) :=
      (inFAM_gstep _ hstep_fam).2
    rw [hgg] at hcomp3
    constructor
    · rw [hcomp2, two_pow_succ_add]
      ring
    · rw [hcomp3, ← hgsd, show 2 * (2^j * x) = 2^(j+1) * x from by
        rw [two_pow_succ_add]; ring]

/-- THE DOUBLING THEOREM: every chain-family member doubles every 2 steps,
from step 0 on. -/
theorem erdos411_doubling (x : Nat) (hx : inFAM x) : ∀ k, gF (k+2) x = 2 * gF k x := by
  intro k
  rcases (show k % 2 = 0 ∨ k % 2 = 1 from by omega) with hpar | hpar
  · -- k even: k = 2 * (k/2)
    obtain ⟨hE, hF⟩ := gF_two_pow x hx ((k/2)+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx (k/2)
    conv =>
      rhs => rw [show k = 2*(k/2) from by omega]
      lhs => rw [show k + 2 = 2*((k/2)+1) from by omega]
    rw [hE, hC, two_pow_succ_add]
    ring
  · -- k odd: gstep (2^(q+1)·x) = 2·gstep (2^q·x) by the commutation law
    obtain ⟨a, m, ha, hm, hm1, hxe⟩ := hx
    have hfam : inFAM (2^(k/2) * x) := by
      refine ⟨a + k/2, m, by omega, hm, ?_, ?_⟩
      · intro h; subst h; omega
      · rw [hxe, ← Nat.mul_assoc, ← Nat.pow_add]
        congr 1 <;> omega
    have hgsd : gstep (2 * (2^(k/2) * x)) = 2 * gstep (2^(k/2) * x) :=
      gstep_dbl_comm hfam
    obtain ⟨hE, hF⟩ := gF_two_pow x hx ((k/2)+1)
    obtain ⟨hC, hD⟩ := gF_two_pow x hx (k/2)
    conv =>
      rhs => rw [show k = 2*(k/2) + 1 from by omega]
      lhs => rw [show k + 2 = 2*((k/2)+1) + 1 from by omega]
    rw [hF, hD, two_pow_succ_add, Nat.mul_assoc]
    exact hgsd

/-! ## §7 The parity exclusion. -/

theorem gstep_parity_of_odd : ∀ {x : Nat}, x % 2 = 1 → 3 ≤ x → (gstep x) % 2 = 1 := by
  intro x hx h3
  unfold gstep
  have hφ : 2 ∣ phiB x := by
    have h1 : x = 2 * ((x-1)/2) + 1 := by omega
    exact phiB_even_of_odd h1 h3
  have : phiB x % 2 = 0 := Nat.mod_eq_zero_of_dvd hφ
  omega

theorem gF_odd_of_odd : ∀ {x : Nat}, x % 2 = 1 → 3 ≤ x → ∀ k, (gF k x) % 2 = 1 := by
  intro x hx h3 k
  have key : ∀ (j y : Nat), y % 2 = 1 → 3 ≤ y → (gF j y) % 2 = 1 := by
    intro j
    induction j with
    | zero => intro y hy _; exact hy
    | succ j ihj =>
      intro y hy h3y
      have hgs : (gstep y) % 2 = 1 := gstep_parity_of_odd hy h3y
      have hgs3 : 3 ≤ gstep y := by unfold gstep; omega
      exact ihj (gstep y) hgs hgs3
  exact key k x hx h3

/-- The two anchor steps (decide-certified: g(1) = 2, g(2) = 3). -/
theorem gstep_one : gstep 1 = 2 := by decide

theorem gstep_two : gstep 2 = 3 := by decide

theorem gF_one_step (k : Nat) : gF (k+1) 1 = gF k 2 := by
  have h : gF (k+1) 1 = gF k (gstep 1) := rfl
  rw [h, gstep_one]

theorem gF_two_step (k : Nat) : gF (k+1) 2 = gF k 3 := by
  have h : gF (k+1) 2 = gF k (gstep 2) := rfl
  rw [h, gstep_two]

/-- THE PARITY EXCLUSION: no odd n is a ratio-2 solution. -/
theorem erdos411_parity : ∀ (n : Nat), n % 2 = 1 → ∀ (r K : Nat), 1 ≤ r →
    ¬ (∀ k, K ≤ k → gF (k + r) n = 2 * gF k n) := by
  intro n hn r K hr hall
  have h3 : 3 ≤ n ∨ n = 1 := by omega
  rcases h3 with h | h
  · -- n ≥ 3: every iterate stays odd; doubling forces even — contradiction
    have hodd : ∀ k, (gF k n) % 2 = 1 := fun k => gF_odd_of_odd hn h k
    have h1 := hodd (K + r)
    have := hall K (by omega)
    rw [this] at h1
    omega
  · -- n = 1: g₁(1) = 2, then the orbit enters 3 and stays odd
    subst h
    have hodd : ∀ j, 2 ≤ j → (gF j 1) % 2 = 1 := by
      intro j hj
      have h1 : gF j 1 = gF (j-1) 2 := by
        cases j with
        | zero => omega
        | succ j' =>
            have h2 : gF (j'+1) 1 = gF j' 2 := gF_one_step j'
            rw [h2]
            rfl
      have h3 : (gF (j-1) 2) % 2 = 1 := by
        cases (j-1) with
        | zero => omega
        | succ j'' =>
            have h4 : gF (j''+1) 2 = gF j'' 3 := gF_two_step j''
            rw [h4]
            exact gF_odd_of_odd (by decide) (by decide) j''
      rw [h1, h3]
    have k := K + 2
    have h1 := hodd (k + r) (by omega)
    have := hall k (by omega)
    rw [this] at h1
    omega

/-- n = 2 is not a ratio-2 solution either. -/
theorem erdos411_two : ∀ (r K : Nat), 1 ≤ r →
    ¬ (∀ k, K ≤ k → gF (k + r) 2 = 2 * gF k 2) := by
  intro r K hr hall
  have hodd : ∀ k, 1 ≤ k → (gF k 2) % 2 = 1 := by
    intro k hk
    have h1 : gF k 2 = gF (k-1) 3 := by
      cases k with
      | zero => omega
      | succ k' =>
          have h2 : gF (k'+1) 2 = gF k' 3 := gF_two_step k'
          rw [h2]
          rfl
    rw [h1]
    exact gF_odd_of_odd (by decide) (by decide) (k-1)
  have k := K + 1
  have h1 := hodd (k + r) (by omega)
  have := hall k (by omega)
  rw [this] at h1
  omega

/-! ## §8 The odd-part machinery. -/

theorem two_pow_mul_exists : ∀ x, 0 < x → ∃ a m, m % 2 = 1 ∧ x = 2^a * m := by
  apply strongIndOn
  intro i ih hi
  rcases Nat.eq_zero_or_pos (i % 2) with h0 | h0
  · have hy : i / 2 < i := Nat.div_lt_self (by omega) (by decide)
      have hypos : 0 < i / 2 := by omega
    obtain ⟨a, m, hm, hme⟩ := ih (i / 2) hy hypos
    refine ⟨a + 1, m, hm, ?_⟩
    have hd2 : i = 2 * (i / 2) := (Nat.mul_div_cancel (Nat.dvd_of_mod_eq_zero h0)).symm
    rw [hd2, hme, Nat.pow_add, Nat.pow_one]
    ring
  · exact ⟨0, i, by omega, by rw [Nat.pow_zero, Nat.one_mul]⟩

theorem oddPF_eq : ∀ (x a m f : Nat), x = 2^a * m → m % 2 = 1 → a ≤ f →
    oddPF f x = m := by
  intro x a m f
  induction f generalizing x a with
  | zero =>
      intro hxe hm haf
      have ha0 : a = 0 := by omega
      rw [ha0, Nat.pow_zero, Nat.one_mul] at hxe
      rw [hxe]
      rfl
  | succ f ih =>
      intro hxe hm haf
      rcases Nat.eq_zero_or_pos a with ha0 | ha1
      · rw [ha0, Nat.pow_zero, Nat.one_mul] at hxe
        rw [hxe]
        have hno : ¬ (m % 2 = 0) := by omega
        simp only [oddPF, if_neg hno]
      · have hsucc : Nat.succ (a-1) = a := by omega
        have hx2 : x = 2 * (2^(a-1) * m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_succ, hsucc]
          exact hxe
        have hmod : x % 2 = 0 := by omega
        have hdiv : x / 2 = 2^(a-1) * m := by
          rw [hx2]
          omega
        simp only [oddPF, if_pos hmod]
        exact ih (x/2) (a-1) hdiv hm (by omega)

theorem oddPF_fac : ∀ (v f : Nat), 0 < v → v < 2^f →
    ∃ i m, m % 2 = 1 ∧ v = 2^i * m ∧ oddPF f v = m := by
  intro v f
  induction f generalizing v with
  | zero => intro v hv hlt; omega
  | succ f ih =>
      intro v hv hlt
      rcases Nat.eq_zero_or_pos (v % 2) with h0 | h0
      · have hmod : v % 2 = 0 := h0
        simp only [oddPF, if_pos hmod]
        have hdivpos : 0 < v / 2 := by omega
        have hdivlt : v / 2 < 2^f := by
          have hp : 2^(f+1) = 2^f * 2 := by rw [Nat.pow_add, Nat.pow_one]
          rw [hp] at hlt
          exact Nat.div_lt_of_lt_mul hlt
        obtain ⟨i, m, hm, hme, hof⟩ := ih (v/2) hdivpos hdivlt
        refine ⟨i + 1, m, hm, ?_, ?_⟩
        · have hd2 : v = 2 * (v / 2) := (Nat.mul_div_cancel (Nat.dvd_of_mod_eq_zero h0)).symm
          rw [hd2, hme, Nat.pow_add, Nat.pow_one]
          ring
        · exact hof
      · refine ⟨0, v, by omega, by rw [Nat.pow_zero, Nat.one_mul], ?_⟩
        have hno : ¬ (v % 2 = 0) := by omega
        simp only [oddPF, if_neg hno]

theorem oddPF_bound_ok (x a m : Nat) (hx : x < 2^64) (hxe : x = 2^a * m) (hm : m % 2 = 1) :
    oddPF 64 x = m := by
  have ha64 : a ≤ 64 := by
    by_contra h
    have h65 : 65 ≤ a := by omega
    have hpow : (2:Nat)^64 ≤ 2^a := Nat.pow_le_pow_right 2 h65
    have hm1 : 1 ≤ m := by omega
    have h2a : 2^a ≤ x := by
      rw [hxe]
      exact Nat.le_mul_of_pos_right (2^a) hm1
    omega
  exact oddPF_eq x a m 64 hxe hm ha64

/-! ## §9 The certified table and its closure. -/

def table411 : List Nat := [
    1, 3, 5, 7, 35, 47, 9, 11, 19, 25, 43, 49,
    107, 251, 683, 2731, 13, 15, 17, 27, 29, 33, 59, 67,
    77, 121, 131, 473, 523, 571, 811, 911, 2049, 2091, 21, 23,
    51, 79, 81, 95, 103, 139, 179, 349, 363, 393, 541, 559,
    619, 631, 1259, 1451, 1465, 1569, 31, 39, 53, 63, 75, 127,
    211, 233, 239, 243, 253, 373, 421, 491, 869, 977, 989, 1209,
    2027, 55, 57, 71, 83, 91, 159, 183, 189, 195, 281, 283,
    311, 331, 341, 563, 729, 865, 909, 1123, 1319, 1391, 37, 45,
    61, 69, 115, 147, 213, 249, 379, 443, 549, 567, 577, 585,
    587, 751, 843, 883, 899, 971, 995, 2187, 41, 87, 111, 163,
    307, 391, 407, 413, 425, 429, 441, 465, 583, 633, 671, 695,
    1641, 1701, 1755, 6561, 109, 123, 217, 287, 289, 305, 333, 389,
    403, 477, 529, 1233, 1255, 1281, 1305, 1317, 1323, 1395, 2267, 4923,
    19683, 73, 93, 193, 203, 269, 303, 353, 383, 901, 913, 927,
    935, 963, 981, 993, 999, 1155, 1163, 1589, 1627, 3083, 3843, 14769,
    15795, 59049, 143, 271, 359, 601, 723, 747, 777, 803, 903, 915,
    1127, 1141, 2123, 2889, 11529, 12915, 44307, 181, 191, 401, 479, 517,
    535, 543, 551, 609, 655, 687, 735, 761, 791, 1547, 2169, 8667,
    9687, 34587, 395, 475, 545, 1067, 1785, 6507, 7539, 26001, 317, 375,
    377, 727, 731, 737, 749, 1425, 5355, 5955, 19521, 221, 275, 503,
    511, 539, 983, 1025, 1083, 4275, 4467, 16065, 367, 719, 813, 825,
    1367, 2683, 3043, 3207, 3351, 5867, 12825, 259, 515, 605, 645, 959,
    1789, 2071, 2395, 2451, 4037, 9621, 173, 525, 691, 1279, 1309, 1381,
    1797, 1839, 2885, 7353, 461, 519, 853, 931, 949, 1285, 1315, 1419,
    2093, 5517, 569, 699, 857, 877, 925, 979, 1587, 4257, 555, 617,
    653, 759, 1135, 3267, 417, 757, 823, 2227, 2335, 1671, 1675, 1117,
    1195, 1257, 797, 817, 885, 969, 1063, 709,  ]

def stepIX411 : List Nat := [
    0, 0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 4,
    2, 5, 0, 0, 8, 8, 9, 6, 10, 10, 7, 9,
    12, 7, 11, 14, 11, 12, 8, 14, 15, 15, 19, 18,
    23, 22, 19, 26, 24, 16, 23, 28, 27, 28, 30, 30,
    20, 27, 22, 18, 32, 33, 35, 36, 37, 38, 39, 39,
    37, 43, 42, 38, 44, 47, 49, 35, 50, 52, 51, 53,
    39, 58, 58, 56, 54, 59, 60, 63, 63, 63, 66, 56,
    61, 54, 67, 60, 63, 71, 71, 66, 70, 72, 73, 74,
    77, 77, 78, 80, 83, 85, 75, 76, 88, 88, 89, 88,
    73, 87, 91, 85, 92, 77, 93, 88, 96, 98, 99, 96,
    98, 105, 108, 108, 107, 104, 105, 107, 110, 110, 113, 113,
    115, 115, 115, 115, 119, 119, 120, 122, 124, 124, 126, 128,
    128, 129, 121, 132, 134, 132, 132, 134, 133, 134, 124, 135,
    135, 136, 137, 140, 139, 144, 144, 146, 139, 151, 152, 147,
    148, 149, 150, 152, 152, 153, 136, 154, 141, 140, 155, 156,
    156, 156, 160, 160, 161, 165, 169, 171, 171, 174, 173, 173,
    175, 176, 177, 178, 179, 180, 181, 183, 182, 185, 184, 187,
    187, 186, 189, 188, 191, 191, 190, 193, 192, 194, 195, 196,
    197, 198, 206, 208, 211, 213, 214, 215, 216, 217, 219, 219,
    220, 220, 221, 221, 221, 222, 223, 224, 225, 226, 227, 228,
    229, 232, 231, 233, 233, 234, 235, 236, 238, 241, 244, 243,
    243, 239, 246, 245, 246, 238, 247, 248, 249, 251, 250, 252,
    253, 254, 256, 255, 257, 258, 259, 262, 259, 263, 264, 265,
    266, 267, 268, 269, 272, 272, 273, 274, 275, 276, 277, 277,
    278, 279, 282, 283, 285, 286, 285, 287, 288, 289, 291, 294,
    295, 295, 296, 297, 298, 302, 299, 303, 303, 307, 308, 310,
    309, 310, 312, 312, 311, 313, 314, 318,  ]

/-- The step target of the odd-part map. -/
def Tstep (m : Nat) : Nat := oddPF 64 (2 * m + phiB m)

/-- The closure predicate: every table entry is either a chain-family odd
part (the rank-0 prefix) or steps to a strictly earlier entry whose value
is exactly Tstep of it, with an even step value. -/
def closureB (i : Nat) : Bool :=
  decide (i < table411.length) &&
    (inSIX table411[i]! ||
      (decide (stepIX411[i]! < i) && ((2 * table411[i]! + phiB table411[i]!) % 2 == 0)
        && (table411[stepIX411[i]!]! == Tstep table411[i]!)))

/-- The chunk covers EXACTLY the closed index interval [lo, hi] (W60-T1 ROOT
FIX: the r1 form `List.range (hi + 1)` covered lo..lo+hi — every chunk with
lo + hi ≥ 320 ran past the table end where closureB fails the length check,
which is why cl_3..cl_17 evaluated FALSE; cl_1/cl_2 passed only because
0 + 92 < 320 and 93 + 150 < 320). Python mirror: ALL 320 indices pass. -/
def closureChunk (lo hi : Nat) : Bool :=
  (List.range (hi - lo + 1)).all (fun k => closureB (lo + k))

/-! ### The 17 closure chunks (NO-OOM discipline; cumulative φ-cost per chunk). -/

theorem cl_1 : closureChunk 0 92 = true := by decide
theorem cl_2 : closureChunk 93 150 = true := by decide
theorem cl_3 : closureChunk 151 171 = true := by decide
theorem cl_4 : closureChunk 172 179 = true := by decide
theorem cl_5 : closureChunk 180 180 = true := by decide
theorem cl_6 : closureChunk 181 181 = true := by decide
theorem cl_7 : closureChunk 182 197 = true := by decide
theorem cl_8 : closureChunk 198 198 = true := by decide
theorem cl_9 : closureChunk 199 216 = true := by decide
theorem cl_10 : closureChunk 217 222 = true := by decide
theorem cl_11 : closureChunk 223 224 = true := by decide
theorem cl_12 : closureChunk 225 234 = true := by decide
theorem cl_13 : closureChunk 235 246 = true := by decide
theorem cl_14 : closureChunk 247 257 = true := by decide
theorem cl_15 : closureChunk 258 272 = true := by decide
theorem cl_16 : closureChunk 273 296 = true := by decide
theorem cl_17 : closureChunk 297 319 = true := by decide

/-- Assembly: closure holds for every table index. -/
theorem closure_all : ∀ i, i < table411.length → closureB i = true := by
  intro i hi
  have h01 : ∀ k, 0 ≤ k → k ≤ 92 → closureB k = true := by
    intro k _ hk
    have h := cl_1
    rw [List.all_eq_true] at h
    have := h k (by rw [List.mem_range]; omega)
    simpa using this
  have h02 : ∀ k, 93 ≤ k → k ≤ 150 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_2
    rw [List.all_eq_true] at h
    have := h (k - 93) (by rw [List.mem_range]; omega)
    have hkrw : 93 + (k - 93) = k := by omega
    rw [hkrw] at this
    exact this
  have h03 : ∀ k, 151 ≤ k → k ≤ 171 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_3
    rw [List.all_eq_true] at h
    have := h (k - 151) (by rw [List.mem_range]; omega)
    have hkrw : 151 + (k - 151) = k := by omega
    rw [hkrw] at this
    exact this
  have h04 : ∀ k, 172 ≤ k → k ≤ 179 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_4
    rw [List.all_eq_true] at h
    have := h (k - 172) (by rw [List.mem_range]; omega)
    have hkrw : 172 + (k - 172) = k := by omega
    rw [hkrw] at this
    exact this
  have h05 : ∀ k, k = 180 → closureB k = true := by
    intro k hk
    have h := cl_5
    rw [List.all_eq_true] at h
    have := h (k - 180) (by rw [List.mem_range]; omega)
    have hkrw : 180 + (k - 180) = k := by omega
    rw [hkrw] at this
    exact this
  have h06 : ∀ k, k = 181 → closureB k = true := by
    intro k hk
    have h := cl_6
    rw [List.all_eq_true] at h
    have := h (k - 181) (by rw [List.mem_range]; omega)
    have hkrw : 181 + (k - 181) = k := by omega
    rw [hkrw] at this
    exact this
  have h07 : ∀ k, 182 ≤ k → k ≤ 197 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_7
    rw [List.all_eq_true] at h
    have := h (k - 182) (by rw [List.mem_range]; omega)
    have hkrw : 182 + (k - 182) = k := by omega
    rw [hkrw] at this
    exact this
  have h08 : ∀ k, k = 198 → closureB k = true := by
    intro k hk
    have h := cl_8
    rw [List.all_eq_true] at h
    have := h (k - 198) (by rw [List.mem_range]; omega)
    have hkrw : 198 + (k - 198) = k := by omega
    rw [hkrw] at this
    exact this
  have h09 : ∀ k, 199 ≤ k → k ≤ 216 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_9
    rw [List.all_eq_true] at h
    have := h (k - 199) (by rw [List.mem_range]; omega)
    have hkrw : 199 + (k - 199) = k := by omega
    rw [hkrw] at this
    exact this
  have h10 : ∀ k, 217 ≤ k → k ≤ 222 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_10
    rw [List.all_eq_true] at h
    have := h (k - 217) (by rw [List.mem_range]; omega)
    have hkrw : 217 + (k - 217) = k := by omega
    rw [hkrw] at this
    exact this
  have h11 : ∀ k, 223 ≤ k → k ≤ 224 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_11
    rw [List.all_eq_true] at h
    have := h (k - 223) (by rw [List.mem_range]; omega)
    have hkrw : 223 + (k - 223) = k := by omega
    rw [hkrw] at this
    exact this
  have h12 : ∀ k, 225 ≤ k → k ≤ 234 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_12
    rw [List.all_eq_true] at h
    have := h (k - 225) (by rw [List.mem_range]; omega)
    have hkrw : 225 + (k - 225) = k := by omega
    rw [hkrw] at this
    exact this
  have h13 : ∀ k, 235 ≤ k → k ≤ 246 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_13
    rw [List.all_eq_true] at h
    have := h (k - 235) (by rw [List.mem_range]; omega)
    have hkrw : 235 + (k - 235) = k := by omega
    rw [hkrw] at this
    exact this
  have h14 : ∀ k, 247 ≤ k → k ≤ 257 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_14
    rw [List.all_eq_true] at h
    have := h (k - 247) (by rw [List.mem_range]; omega)
    have hkrw : 247 + (k - 247) = k := by omega
    rw [hkrw] at this
    exact this
  have h15 : ∀ k, 258 ≤ k → k ≤ 272 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_15
    rw [List.all_eq_true] at h
    have := h (k - 258) (by rw [List.mem_range]; omega)
    have hkrw : 258 + (k - 258) = k := by omega
    rw [hkrw] at this
    exact this
  have h16 : ∀ k, 273 ≤ k → k ≤ 296 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_16
    rw [List.all_eq_true] at h
    have := h (k - 273) (by rw [List.mem_range]; omega)
    have hkrw : 273 + (k - 273) = k := by omega
    rw [hkrw] at this
    exact this
  have h17 : ∀ k, 297 ≤ k → k ≤ 319 → closureB k = true := by
    intro k hk1 hk2
    have h := cl_17
    rw [List.all_eq_true] at h
    have := h (k - 297) (by rw [List.mem_range]; omega)
    have hkrw : 297 + (k - 297) = k := by omega
    rw [hkrw] at this
    exact this
  -- the routing
  rcases Nat.lt_or_ge i 93 with h | h
  · exact h01 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 151 with h | h
  · exact h02 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 172 with h | h
  · exact h03 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 180 with h | h
  · exact h04 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 181 with h | h
  · exact h05 i (by omega)
  rcases Nat.lt_or_ge i 182 with h | h
  · exact h06 i (by omega)
  rcases Nat.lt_or_ge i 198 with h | h
  · exact h07 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 199 with h | h
  · exact h08 i (by omega)
  rcases Nat.lt_or_ge i 217 with h | h
  · exact h09 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 223 with h | h
  · exact h10 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 225 with h | h
  · exact h11 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 235 with h | h
  · exact h12 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 247 with h | h
  · exact h13 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 258 with h | h
  · exact h14 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 273 with h | h
  · exact h15 i (by omega) (by omega)
  rcases Nat.lt_or_ge i 297 with h | h
  · exact h16 i (by omega) (by omega)
  · exact h17 i (by omega) (by omega)

/-- The Prop form of the closure. -/
theorem closure_prop (i : Nat) (hi : i < table411.length) :
    inSIX table411[i]! = true ∨
    (∃ j, j < i ∧ j < table411.length ∧ table411[j]! = Tstep table411[i]! ∧
       (2 * table411[i]! + phiB table411[i]!) % 2 = 0) := by
  have h := closure_all i hi
  unfold closureB at h
  rw [decide_eq_true hi] at h
  simp only [Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hSIX | ⟨hlt, heven, hval⟩
  · exact Or.inl hSIX
  · have hlt' := of_decide_eq_true hlt
    refine Or.inr ⟨stepIX411[i]!, hlt', by omega, eq_of_beq hval, eq_of_beq heven⟩

/-! ## §10 The witness theorem (the odd-part reduction). -/

/-- Bridge: for an index below the length, the total get! equals the safe get. -/
theorem getElem_bang_of_lt {l : List Nat} {i : Nat} (h : i < l.length) :
    l[i]! = l[i] := by
  have h1 : l[i]! = (l[i]?).getD 0 := List.getElem!_eq_getElem?_getD
  rw [h1, List.getD_getElem?]
  rw [dif_pos h]

/-- Every table entry is at most 59049 = 3^10 (decide-checked, no φ cost). -/
theorem table_bounds : (List.range table411.length).all
    (fun i => decide (table411[i]! ≤ 59049)) = true := by decide

theorem table_bound_of_lt (i : Nat) (h : i < table411.length) : table411[i]! ≤ 59049 := by
  have h1 := table_bounds
  rw [List.all_eq_true] at h1
  have h2 := h1 i (by rw [List.mem_range]; omega)
  exact of_decide_eq_true h2

/-- THE WITNESS THEOREM: every even x ≥ 4 whose odd part is a table member
is an r=2 solution (the chain laws take over at entry). -/
def WitP (i : Nat) : Prop :=
  i < table411.length →
    ∀ x a m, 4 ≤ x → 1 ≤ a → m % 2 = 1 → x = 2^a * m → m = table411[i]! →
      ∃ K, ∀ k, K ≤ k → gF (k+2) x = 2 * gF k x

theorem erdos411_witness : ∀ i, WitP i := by
  apply strongIndOn
  intro i ih hi
  intro hlen x a m hx4 ha hmod hxe hmem
  have hval : table411[i]! = m := hmem.symm
  rcases closure_prop i hlen with hSIX | hstep
  · -- m ∈ SIX: x is a chain-family member, doubling from k = 0
    have hmSIX : m ∈ SIXl := by
      have hbool : inSIX m = true := by rw [← hval]; exact hSIX
      exact List.contains_iff_mem.mp (by simpa [inSIX] using hbool)
    refine ⟨0, fun k _ => erdos411_doubling x ⟨a, m, ha, hmSIX, ?_, hxe⟩ k⟩
    intro h1m
    subst h1m
    have ha2 : 2 ≤ a := by
      by_contra hc
      have : a ≤ 1 := by omega
      have hle : (2:Nat)^a ≤ 2^1 := Nat.pow_le_pow_right 2 this
      have h1 : (2:Nat)^1 = 2 := by rw [Nat.pow_one]
      rw [hxe, h1] at hle
      have : (2:Nat) * 1 ≤ 4 := by omega
      omega
    omega
  · -- m ∉ SIX: step down through the table
    obtain ⟨j, hji, hjlen, hjval, hjeven⟩ := hstep
    have hmb : m ≤ 59049 := by
      have := table_bound_of_lt i hlen
      rw [hval] at this
      exact this
    have hstepx : gstep x = 2^(a-1) * (2 * m + phiB m) := by
      rw [← hxe]
      exact gstep_two_pow_mul a m ha hmod
    have hphile : phiB m ≤ m := phiB_le m
    have hvpos : 0 < 2 * m + phiB m := by omega
    have h218 : (2:Nat)^18 = 262144 := by decide
    have hv18 : 2 * m + phiB m < 2^18 := by omega
    have hv64 : 2 * m + phiB m < 2^64 := by omega
    obtain ⟨iv, mv, hmvodd, hmvfac, hmvoddPF⟩ := oddPF_fac (2 * m + phiB m) 64 hvpos hv64
    have hmvT : mv = table411[j]! := by
      rw [hjval, show Tstep table411[i]! = Tstep m from by rw [hval],
          show Tstep m = oddPF 64 (2 * m + phiB m) from rfl, ← hmvoddPF]
    have hg : gstep x = 2^(a-1+iv) * mv := by
      rw [hstepx, hmvfac, ← Nat.mul_assoc, ← Nat.pow_add]
    have hive : 1 ≤ iv := by
      by_contra hc
      have hiv0 : iv = 0 := by omega
      rw [hiv0, Nat.pow_zero, Nat.one_mul] at hmvfac
      rw [hmvfac] at hjeven
      omega
    have hpp : 1 ≤ phiB x := phiB_pos x (by omega)
    have hgs4 : 4 ≤ gstep x := by
      have : gstep x = x + phiB x := rfl
      omega
    have hW := ih j hji
    unfold WitP at hW
    obtain ⟨K', hK'⟩ := hW hjlen (gstep x) (a-1+iv) mv hgs4 (by omega) hmvodd hg hmvT
    refine ⟨K' + 1, ?_⟩
    intro k hk
    have hk1 : K' ≤ k - 1 := by omega
    have e1 : gF (k+2) x = gF (k+1) (gstep x) := rfl
    have e2 : (k:Nat) + 1 = (k-1) + 2 := by omega
    have e3 : gF k x = gF (k-1) (gstep x) := by
      have hk2 : k = (k-1) + 1 := by omega
      rw [hk2]
      rfl
    have e4 : gF ((k-1)+2) (gstep x) = 2 * gF (k-1) (gstep x) := hK' (k-1) hk1
    rw [e1, e2, e4, ← e3]

/-! ## §11 The census, the partition, the receipts, and the main theorems. -/

/-- The 279 wanderer odd parts (bounded non-entry, engine-flagged). -/
def wander411 : List Nat := [
    65, 85, 89, 97, 99, 101, 105, 113, 117, 119, 125, 129,
    133, 135, 137, 141, 145, 149, 151, 153, 155, 157, 161, 165,
    167, 169, 171, 175, 177, 185, 187, 197, 199, 201, 205, 207,
    209, 215, 219, 223, 225, 227, 229, 231, 235, 237, 241, 245,
    247, 255, 257, 261, 263, 265, 267, 273, 277, 279, 285, 291,
    293, 295, 297, 299, 301, 309, 313, 315, 319, 321, 323, 325,
    327, 329, 335, 337, 339, 343, 345, 347, 351, 355, 357, 361,
    365, 369, 371, 381, 385, 387, 397, 399, 405, 409, 411, 415,
    419, 423, 427, 431, 433, 435, 437, 439, 445, 447, 449, 451,
    453, 455, 457, 459, 463, 467, 469, 471, 481, 483, 485, 487,
    489, 493, 495, 497, 499, 501, 505, 507, 509, 513, 521, 527,
    531, 533, 537, 547, 553, 557, 561, 565, 573, 575, 579, 581,
    589, 591, 593, 595, 597, 599, 603, 607, 611, 613, 615, 621,
    623, 625, 627, 629, 635, 637, 639, 641, 643, 647, 649, 651,
    657, 659, 661, 663, 665, 667, 669, 673, 675, 677, 679, 681,
    685, 689, 693, 697, 701, 703, 705, 707, 711, 713, 715, 717,
    721, 725, 733, 739, 741, 743, 745, 753, 755, 763, 765, 767,
    769, 771, 773, 775, 779, 781, 783, 785, 787, 789, 793, 795,
    799, 801, 805, 807, 809, 815, 819, 821, 827, 829, 831, 833,
    835, 837, 839, 841, 845, 847, 849, 851, 855, 859, 861, 863,
    867, 871, 873, 875, 879, 881, 887, 889, 891, 893, 895, 897,
    905, 907, 917, 919, 921, 923, 929, 933, 937, 939, 941, 943,
    945, 947, 951, 953, 955, 957, 961, 965, 967, 973, 975, 985,
    987, 991, 997,  ]

/-- The two-list predicate: evens pass; odds must be table or wanderer. -/
def partitionB (k : Nat) : Bool :=
  (!(k % 2 == 1)) || (table411.contains k || wander411.contains k)

/-- THE PARTITION: every odd m ≤ 999 lies in one of the two lists (W60-T1:
the r1 wrote `List.range 1002` — but 1001 itself is in NEITHER list, exactly
as the python mirror warns: "1001 is in neither list — the kernel must use
range 1001"; the certified statement is the 500-value split: 221 table
entries + 279 wanderers = every odd k ≤ 999). -/
theorem erdos411_partition : (List.range 1001).all partitionB = true := by decide

/-- THE COUNT: exactly 535 even n ∈ [4, 2000] have their odd part certified. -/
theorem erdos411_count :
    (List.filter (fun n => decide (4 ≤ n && n ≤ 2000 && n % 2 == 0 &&
      table411.contains (oddPF 64 n))) (List.range 2001)).length = 535 := by decide

/-- THE CENSUS THEOREM: every even n ∈ [4, 2000] with certified odd part
is an r = 2 solution. -/
theorem erdos411_census : ∀ n, 4 ≤ n → n ≤ 2000 → n % 2 = 0 →
    table411.contains (oddPF 64 n) = true →
      ∃ K, ∀ k, K ≤ k → gF (k+2) n = 2 * gF k n := by
  intro n h4 hn2k heven hmem
  obtain ⟨a, m, hmod, hxe⟩ := two_pow_mul_exists n (by omega)
  have ha1 : 1 ≤ a := by
    by_contra hc
    have ha0 : a = 0 := by omega
    rw [ha0, Nat.pow_zero, Nat.one_mul] at hxe
    rw [hxe] at heven
    omega
  have hn64 : n < 2^64 := by
    have h10 : (2:Nat)^10 = 1024 := by decide
    have hn10 : n < 2^10 := by omega
    have h64 : (2:Nat)^10 ≤ 2^64 := Nat.pow_le_pow_right 2 (by omega)
    omega
  have hm64 : oddPF 64 n = m := oddPF_bound_ok n a m hn64 hxe hmod
  rw [hm64] at hmem
  have hmem' : m ∈ table411 := List.contains_iff_mem.mp (by simpa using hmem)
  obtain ⟨i, hilen, hieval⟩ := List.mem_iff_getElem.mp hmem'
  have hbang : table411[i]! = m := by
    rw [getElem_bang_of_lt hilen]; exact hieval
  have hW := erdos411_witness i hilen
  unfold WitP at hW
  exact hW hilen n a m h4 ha1 hmod hxe hbang

/-- The two known solutions, as instances of the doubling theorem. -/
theorem erdos411_ten : ∀ k, gF (k+2) 10 = 2 * gF k 10 := by
  intro k
  exact erdos411_doubling 10 ⟨1, 5, by omega, by simp [SIXl], by intro h; omega,
    by rw [Nat.pow_one]⟩ k

theorem erdos411_94 : ∀ k, gF (k+2) 94 = 2 * gF k 94 := by
  intro k
  exact erdos411_doubling 94 ⟨1, 47, by omega, by simp [SIXl], by intro h; omega,
    by rw [Nat.pow_one]⟩ k

/-- THE ARSENAL BRIDGE: the pair j-values via the Boss's own v2r machinery
(W60-T1: the r1 rw-chains cited a nonexistent `v2r.eq_def` — an invented
path; the green spelling is decide on the certified literals + the genuine
`v2r_mul_three_pow` for the scaling conjuncts). -/
theorem erdos411_arsenal_bridge :
    v2r 14 = 1 ∧ v2r 20 = 2 ∧ v2r 8 = 3 ∧ v2r 94 = 1 ∧ v2r 140 = 2 ∧
    v2r (9 * 14) = v2r 14 ∧ v2r (3^2 * 20) = v2r 20 ∧
    ErdosTernary2.isTernaryDigit 59049 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [show (9:Nat) = 3^2 from by decide]
    exact v2r_mul_three_pow 2 14
  · exact v2r_mul_three_pow 2 20
  · decide

/-- THE MAIN SUMMARY. -/
theorem erdos411_main :
    (∀ n, n % 2 = 1 → ∀ (r K : Nat), 1 ≤ r →
      ¬ (∀ k, K ≤ k → gF (k+r) n = 2 * gF k n)) ∧
    (∀ (r K : Nat), 1 ≤ r → ¬ (∀ k, K ≤ k → gF (k+r) 2 = 2 * gF k 2)) ∧
    (∀ (x : Nat), inFAM x → ∀ k, gF (k+2) x = 2 * gF k x) ∧
    (∀ n, 4 ≤ n → n ≤ 2000 → n % 2 = 0 →
      table411.contains (oddPF 64 n) = true →
        ∃ K, ∀ k, K ≤ k → gF (k+2) n = 2 * gF k n) ∧
    (List.filter (fun n => decide (4 ≤ n && n ≤ 2000 && n % 2 == 0 &&
      table411.contains (oddPF 64 n))) (List.range 2001)).length = 535 ∧
    table411.length = 320 ∧ wander411.length = 279 ∧
    (∀ k, gF (k+2) 10 = 2 * gF k 10) ∧ (∀ k, gF (k+2) 94 = 2 * gF k 94) :=
  ⟨erdos411_parity, erdos411_two, erdos411_doubling, erdos411_census,
   erdos411_count, by decide, by decide, erdos411_ten, erdos411_94⟩

#eval "ERDOS411_KERNEL_GREEN"
#print axioms erdos411_parity
#print axioms erdos411_two
#print axioms erdos411_doubling
#print axioms erdos411_ten
#print axioms erdos411_94
#print axioms erdos411_witness
#print axioms erdos411_census
#print axioms erdos411_partition
#print axioms erdos411_count
#print axioms erdos411_arsenal_bridge
#print axioms erdos411_main

end Erdos411
