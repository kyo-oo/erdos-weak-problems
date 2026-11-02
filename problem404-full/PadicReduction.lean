/-
# ERDŐS #404 — THE FULL PROBLEM: p-ADIC FACTORIAL-SUM REDUCTION KERNEL

The problem (erdosproblems.com/404): for which (a, p) is there a finite upper
bound on k with p^k | (a_1! + ... + a_n!) for some a = a_1 < ... < a_n?
If f(a,p) is the greatest such k, how does it behave?  Is there a prime p and
an infinite chain a_1 < a_2 < ... with v_p(partial sums) -> infinity?

## THE REDUCTION (Theorem A — full proof in DERIVATION.tex)

Every sum factors through the a!-quotient staircase P_i = (a+1)(a+2)···i:

    a! + Σ_{i ∈ B} i!  =  a! · (1 + Σ_{i ∈ B} P_i),

hence  f(a,p) = v_p(a!) + g(a,p)  where g(a,p) is the largest k such that
−1 is a subset sum of {P_i mod p^k} (first obstruction = bound; no obstruction
at any level = exact Z_p zero-sum = the infinite chain of sub-question 3).

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

* THEOREM A  `erdos404_split` : the factorization and the valuation split
  v2(a! + Σ_B i!) = v2(a!) + v2(1 + Σ_B P_i) for every index list B beyond a.
* THEOREM B  `erdos404_odd_a` : for every ODD a and every B beyond a:
  v2(a! + Σ_B i!) = v2(a!) — the complete answer f(a,2) = v2(a!) for the
  infinite class 2 | a+1 (a odd).  The valuation never grows.
* THEOREM C  `erdos404_f42` : f(4,2) = 6 EXACTLY.  Upper bound: the mod-16
  obstruction (all eight sub-sums of {P_5,P_6,P_7} = {5,30,210} miss 0 mod 16;
  every P_i with i ≥ 8 is ≡ 0 mod 16); witness: 4! + 5! + 7! = 5184 = 2^6·81.
* THE BLOCK-IDENTITY STRUCTURE THEORY `block_pair`, `block_triple`:
  [u,u+1] = u!·(u+2);  [u,u+2] = u!·(u+2)².  (The pair valuation law
  v2[u,u+1] = v2(u!) + v2(u+2) is the Kill-#4 kernel law.)
* RECEIPTS: the (2,2) König-chain witnesses (Conjecture D: g(2,2) = ∞):
  valuations 3, 7, 9, 9, 13, 18, 23 — the explicit chain certificates.

Architecture: §1 fact/pt/sums  §2 v2 + power-divisibility  §3 Theorem A
§4 Theorem B  §5 Theorem C  §6 block identities  §7 receipts.
-/

-- ===========================================================================
-- §1  FACTORIALS, PRODUCT TAILS, LIST SUMS
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `pt u j = (u+1)(u+2)···(u+j)`, the j-fold product tail (the P-staircase:
for the seed a = u and index i = u + j, `P_i = pt u j`). -/
def pt : Nat → Nat → Nat
  | _, 0 => 1
  | u, j + 1 => pt u j * (u + j + 1)

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => by simp [fact]
  | u + 1 => one_le_mul _ _ (by omega) (fact_pos u)

/-- `fact (u + j) = fact u * pt u j`. -/
theorem fact_pt : ∀ (j u : Nat), fact (u + j) = fact u * pt u j
  | 0, u => by simp [pt]
  | j + 1, u => by
    have h1 : fact (u + (j + 1)) = (u + j + 1) * fact (u + j) := rfl
    have h2 : pt u (j + 1) = pt u j * (u + j + 1) := rfl
    rw [h1, fact_pt j u, h2, Nat.mul_comm (u + j + 1) (fact u * pt u j),
      Nat.mul_assoc]

/-- Sum of factorials over a list (no seed). -/
def sumF : List Nat → Nat
  | [] => 0
  | i :: B => fact i + sumF B

/-- Sum of P-terms over a list: `sumP a B = Σ_{i ∈ B} pt a (i - a)`. -/
def sumP (a : Nat) : List Nat → Nat
  | [] => 0
  | i :: B => pt a (i - a) + sumP a B

/-- Distributivity helper: `a * x + a * (1 + y) = a * (1 + (x + y))`. -/
theorem mul_add_split (a x y : Nat) :
    a * x + a * (1 + y) = a * (1 + (x + y)) := by
  have L : a * x + a * (1 + y) = a * x + (a + a * y) := by
    rw [Nat.mul_add a 1 y]
  have R : a * (1 + (x + y)) = a + (a * x + a * y) := by
    rw [Nat.mul_add a 1 (x + y), Nat.mul_add a x y]
  rw [L, R]
  omega

-- ===========================================================================
-- §2  THE 2-ADIC VALUATION
-- ===========================================================================

/-- `v2 n` = the exponent of 2 in n (v2 0 = 0 by convention). -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0
termination_by n => n
decreasing_by omega

theorem v2_succ (n : Nat) :
    v2 (n + 1) = if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0 := by
  simp [v2]

theorem v2_even_pos (m : Nat) (hm : 1 ≤ m) (h2 : m % 2 = 0) :
    v2 m = 1 + v2 (m / 2) := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, v2_succ, if_pos (by omega : (j + 1) % 2 = 0)]

theorem v2_odd (m : Nat) (h2 : m % 2 = 1) : v2 m = 0 := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, v2_succ, if_neg (by omega : ¬((j + 1) % 2 = 0))]

theorem two_mul_div2 (x : Nat) : 2 * x / 2 = x := by
  have hmod := Nat.div_add_mod (2 * x) 2
  have h2 : (2 * x) % 2 = 0 := by rw [Nat.mul_mod]; simp
  omega

theorem even_mul_div2 (a b : Nat) (h : a % 2 = 0) :
    a * b / 2 = (a / 2) * b := by
  have hmod := Nat.div_add_mod a 2
  have hmod' := Nat.div_add_mod (a * b) 2
  have hab : (a * b) % 2 = 0 := by rw [Nat.mul_mod, h]; simp
  have key : a * b = 2 * ((a / 2) * b) := by
    calc a * b = (2 * (a / 2) + a % 2) * b := by rw [hmod]
      _ = (2 * (a / 2) + 0) * b := by rw [h]
      _ = (2 * (a / 2)) * b := by rw [Nat.add_zero]
      _ = 2 * ((a / 2) * b) := Nat.mul_assoc _ _ _
  have hfin : 2 * ((a * b) / 2) = 2 * ((a / 2) * b) := by omega
  omega

/-- Additivity of v2 on products (fuel induction). -/
theorem v2_mul : ∀ (f a b : Nat), a + b ≤ f → 1 ≤ a → 1 ≤ b →
    v2 (a * b) = v2 a + v2 b
  | 0, a, b, hf, ha, hb => by omega
  | f + 1, a, b, hf, ha, hb => by
    by_cases ha1 : a = 1
    · rw [ha1, Nat.one_mul, v2_odd 1 (by omega)]
      omega
    · by_cases hae : a % 2 = 0
      · have hxy : 1 ≤ a * b := one_le_mul a b (by omega) hb
        have hb2 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hae]; simp
        have hsplit : a * b / 2 = (a / 2) * b := even_mul_div2 a b hae
        rw [v2_even_pos _ hxy hb2, hsplit]
        rw [v2_mul f (a / 2) b (by omega) (by omega) hb]
        rw [v2_even_pos a (by omega) hae]
        omega
      · by_cases hbe : b % 2 = 0
        · rw [Nat.mul_comm a b]
          have hxy : 1 ≤ b * a := one_le_mul b a hb (by omega)
          have hb2 : (b * a) % 2 = 0 := by rw [Nat.mul_mod, hbe]; simp
          have hsplit : b * a / 2 = (b / 2) * a := even_mul_div2 b a hbe
          rw [v2_even_pos _ hxy hb2, hsplit]
          rw [v2_mul f (b / 2) a (by omega) (by omega) (by omega)]
          rw [v2_even_pos b (by omega) hbe]
          omega
        · have hab : (a * b) % 2 = 1 := by
            rw [Nat.mul_mod, show a % 2 = 1 from by omega,
              show b % 2 = 1 from by omega]
          rw [v2_odd _ hab, v2_odd a (by omega), v2_odd b (by omega)]

/-- `2^k divides x  iff  k ≤ v2 x` (for x ≥ 1). -/
theorem pow2_dvd_iff : ∀ (k x : Nat), 1 ≤ x → (2 ^ k ∣ x ↔ k ≤ v2 x)
  | 0, x, hx => by
    constructor
    · intro _; omega
    · intro _; exact Nat.one_dvd x
  | k + 1, x, hx => by
    have hmod := Nat.div_add_mod x 2
    have hmk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]
    constructor
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      have hx2 : x % 2 = 0 := by
        have h1 : (2 ^ (k + 1) * m) % 2 = 0 := by
          rw [hmk, Nat.mul_mod]; simp
        omega
      have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
      have hxd : x / 2 = 2 ^ k * m := by
        have hx3 : x = 2 * (2 ^ k * m) := by
          rw [← Nat.mul_assoc, ← hmk]
          exact hm
        have h2 := two_mul_div2 (2 ^ k * m)
        omega
      have hm2 : 1 ≤ x / 2 := by omega
      have ih := (pow2_dvd_iff k (x / 2) hm2).mp ⟨m, hxd.symm⟩
      omega
    · intro hle
      have hx2 : x % 2 = 0 := by
        by_contra hne
        have hodd : x % 2 = 1 := by omega
        rw [v2_odd x hodd] at hle
        omega
      have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
      have hm2 : 1 ≤ x / 2 := by omega
      have ih := (pow2_dvd_iff k (x / 2) hm2).mpr (by omega)
      obtain ⟨m, hm⟩ := ih
      refine ⟨m, ?_⟩
      rw [hmk, ← Nat.mul_assoc]
      have hcomm : (2 ^ k * m) * 2 = 2 * (2 ^ k * m) := Nat.mul_comm _ _
      omega

/-- If `x % 2^k ≠ 0` and `x ≥ 1` then `v2 x < k`. -/
theorem v2_lt_of_mod_ne (k x : Nat) (hx : 1 ≤ x) (hne : x % 2 ^ k ≠ 0) :
    v2 x < k := by
  by_contra hc
  have hdvd : 2 ^ k ∣ x := (pow2_dvd_iff k x hx).mpr (by omega)
  have hmod := Nat.mod_eq_zero_of_dvd hdvd
  exact hne hmod

-- ===========================================================================
-- §3  THEOREM A — THE SPLIT
-- ===========================================================================

/-- **Theorem A (factorization).** For every list B of indices beyond a:
`a! + Σ_B i! = a! · (1 + Σ_B P_i)` with `P_i = (a+1)···i`. -/
theorem sumF_split (a : Nat) : ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    fact a + sumF B = fact a * (1 + sumP a B)
  | [], _ => by
    show fact a + 0 = fact a * (1 + 0)
    simp
  | i :: B, hall => by
    have hi : a < i := hall i (by simp)
    have hrest := sumF_split a B (by intro j hj; exact hall j (by simp [hj]))
    obtain ⟨j, hj⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
    have hfi : fact i = fact a * pt a j := by rw [hj, fact_pt j a]
    have hpsame : pt a (i - a) = pt a j := by rw [hj]
    have hunfold : sumF (i :: B) = fact i + sumF B := rfl
    have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
    calc fact a + sumF (i :: B)
        = fact i + (fact a + sumF B) := by rw [hunfold]; omega
      _ = fact a * pt a j + fact a * (1 + sumP a B) := by rw [hfi, hrest]
      _ = fact a * (1 + (pt a (i - a) + sumP a B)) := by
          rw [hpsame]
          exact mul_add_split (fact a) (pt a j) (sumP a B)

/-- **Theorem A (valuation split).** For every B beyond a:
`v2 (a! + Σ_B i!) = v2(a!) + v2(1 + Σ_B P_i)`. -/
theorem erdos404_split (a : Nat) (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    v2 (fact a + sumF B) = v2 (fact a) + v2 (1 + sumP a B) := by
  have h1 : 1 ≤ fact a := fact_pos a
  have h2 : 1 ≤ 1 + sumP a B := by omega
  rw [sumF_split a B hB]
  exact v2_mul (fact a + (1 + sumP a B)) (fact a) (1 + sumP a B)
    (Nat.le_refl _) h1 h2

-- ===========================================================================
-- §4  THEOREM B — THE ODD-a CLASS (2 | a+1): f(a,2) = v2(a!)
-- ===========================================================================

theorem pt_even_of_odd (a : Nat) (ha : a % 2 = 1) :
    ∀ (j : Nat), 1 ≤ j → pt a j % 2 = 0
  | 0, _ => by omega
  | j + 1, _ => by
    have hstep : pt a (j + 1) = pt a j * (a + j + 1) := rfl
    by_cases hj : j = 0
    · rw [hj]
      have h1 : pt a 0 = 1 := rfl
      have h2 : (a + 0 + 1) % 2 = 0 := by omega
      rw [hstep]
      show (pt a 0 * (a + 0 + 1)) % 2 = 0
      rw [h1, Nat.one_mul]
      exact h2
    · rw [hstep, Nat.mul_mod, pt_even_of_odd a ha j (by omega)]
      simp

theorem sumP_odd_of_odd_a (a : Nat) (ha : a % 2 = 1) :
    ∀ (B : List Nat), (∀ i ∈ B, a < i) → (1 + sumP a B) % 2 = 1 := by
  intro B
  induction B with
  | nil => intro _; show (1 + 0) % 2 = 1; simp
  | cons i B ih =>
    intro hall
    have hi : a < i := hall i (by simp)
    have hrest := ih (by intro j hj; exact hall j (by simp [hj]))
    have hj1 : 1 ≤ i - a := by omega
    have hpt := pt_even_of_odd a ha (i - a) hj1
    have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
    show (1 + sumP a (i :: B)) % 2 = 1
    omega

/-- **Theorem B (Erdős #404, the 2 | a+1 class).** For every ODD a and every
finite index list B beyond a:  `v2 (a! + Σ_B i!) = v2 (a!)`.
The 2-adic valuation NEVER grows: f(a,2) = v2(a!) for every odd a. -/
theorem erdos404_odd_a (a : Nat) (ha : a % 2 = 1) (B : List Nat)
    (hB : ∀ i ∈ B, a < i) :
    v2 (fact a + sumF B) = v2 (fact a) := by
  rw [erdos404_split a B hB,
    v2_odd (1 + sumP a B) (sumP_odd_of_odd_a a ha B hB)]

-- ===========================================================================
-- §5  THEOREM C — f(4,2) = 6 EXACTLY
-- ===========================================================================

/-- Every P-term of the (4,2) staircase from index 8 on is ≡ 0 mod 16. -/
theorem pt4_div16 : ∀ (j : Nat), 4 ≤ j → pt 4 j % 16 = 0
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, _ => by decide
  | j + 5, _ => by
    have IH : pt 4 (j + 4) % 16 = 0 := pt4_div16 (j + 4) (by omega)
    have hstep : pt 4 (j + 5) = pt 4 (j + 4) * (4 + (j + 4) + 1) := rfl
    rw [hstep, Nat.mul_mod, IH]
    simp

theorem sumP4_high_mod16 : ∀ (C : List Nat), (∀ i ∈ C, 8 ≤ i) →
    sumP 4 C % 16 = 0
  | [], _ => by show (0 : Nat) % 16 = 0; simp
  | i :: C, hall => by
    have hi : 8 ≤ i := hall i (by simp)
    have hrest := sumP4_high_mod16 C (by intro j hj; exact hall j (by simp [hj]))
    have hpt : pt 4 (i - 4) % 16 = 0 := pt4_div16 (i - 4) (by omega)
    have hpu : sumP 4 (i :: C) = pt 4 (i - 4) + sumP 4 C := rfl
    have hmod := Nat.add_mod (pt 4 (i - 4)) (sumP 4 C) 16
    omega

/-- The low part of the (4,2) witness space, as three switches. -/
def lowList (b5 b6 b7 : Bool) : List Nat :=
  (if b5 then [5] else []) ++ (if b6 then [6] else []) ++ (if b7 then [7] else [])

theorem sumP_low_mod16 (b5 b6 b7 : Bool) :
    (1 + sumP 4 (lowList b5 b6 b7)) % 16 ≠ 0 := by
  cases b5 <;> cases b6 <;> cases b7 <;>
    simp [lowList, sumP, pt, Nat.add_mod] <;> decide

theorem sumP_app (a : Nat) : ∀ (L M : List Nat),
    sumP a (L ++ M) = sumP a L + sumP a M
  | [], M => by show sumP a M = 0 + sumP a M; simp
  | i :: L, M => by
    have hstep : sumP a ((i :: L) ++ M) = pt a (i - a) + sumP a (L ++ M) := rfl
    rw [hstep, sumP_app a L M]
    show pt a (i - a) + (sumP a L + sumP a M) = (pt a (i - a) + sumP a L) + sumP a M
    omega

theorem lowList_mem (b5 b6 b7 : Bool) : ∀ i ∈ lowList b5 b6 b7, 4 < i := by
  intro i hi
  cases b5 <;> cases b6 <;> cases b7 <;> simp [lowList] at hi <;> omega

/-- **Theorem C, upper bound.** For every subset of {5,6,7} (as switches) and
every high index list C (all ≥ 8):  `v2 (4! + Σ i!) ≤ 6`. -/
theorem erdos404_f42_upper (b5 b6 b7 : Bool) (C : List Nat)
    (hC : ∀ i ∈ C, 8 ≤ i) :
    v2 (fact 4 + sumF (lowList b5 b6 b7 ++ C)) ≤ 6 := by
  have hmod : (1 + sumP 4 (lowList b5 b6 b7 ++ C)) % 16 ≠ 0 := by
    have hassoc : 1 + sumP 4 (lowList b5 b6 b7 ++ C)
        = (1 + sumP 4 (lowList b5 b6 b7)) + sumP 4 C := by
      rw [sumP_app 4 (lowList b5 b6 b7) C]
      omega
    rw [hassoc, Nat.add_mod, sumP4_high_mod16 C hC]
    have hzero : ((1 + sumP 4 (lowList b5 b6 b7)) % 16 + 0) % 16
        = (1 + sumP 4 (lowList b5 b6 b7)) % 16 := by
      rw [Nat.add_zero, Nat.mod_mod]
    rw [hzero]
    exact sumP_low_mod16 b5 b6 b7
  have hall : ∀ i ∈ lowList b5 b6 b7 ++ C, 4 < i := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact lowList_mem b5 b6 b7 i h
    · have := hC i h; omega
  rw [erdos404_split 4 (lowList b5 b6 b7 ++ C) hall]
  have hx : 1 ≤ 1 + sumP 4 (lowList b5 b6 b7 ++ C) := by omega
  have hv := v2_lt_of_mod_ne 4 (1 + sumP 4 (lowList b5 b6 b7 ++ C)) hx hmod
  have hf4 : v2 (fact 4) = 3 := by decide
  omega

/-- **Theorem C, witness.** `4! + 5! + 7! = 5184 = 2^6 · 81`. -/
theorem erdos404_f42_witness : v2 (fact 4 + sumF [5, 7]) = 6 := by decide

/-- **Theorem C (Erdős #404): f(4,2) = 6 exactly** — every sum of factorials
with least element 4! has 2-adic valuation at most 6, and 4!+5!+7! attains 6. -/
theorem erdos404_f42 :
    v2 (fact 4 + sumF [5, 7]) = 6 ∧
    ∀ (b5 b6 b7 : Bool) (C : List Nat), (∀ i ∈ C, 8 ≤ i) →
      v2 (fact 4 + sumF (lowList b5 b6 b7 ++ C)) ≤ 6 :=
  ⟨erdos404_f42_witness, erdos404_f42_upper⟩

-- ===========================================================================
-- §6  THE BLOCK-IDENTITY STRUCTURE THEORY
-- ===========================================================================

/-- **Block pair.** `[u, u+1] = u! · (u+2)` — the exact factorization whose
valuation law `v2[u,u+1] = v2(u!) + v2(u+2)` is the Kill-#4 kernel law. -/
theorem block_pair (u : Nat) :
    fact u + fact (u + 1) = fact u * (u + 2) := by
  have h1 : fact (u + 1) = (u + 1) * fact u := rfl
  have h2 : fact u + (u + 1) * fact u = fact u * (1 + (u + 1)) := by
    rw [Nat.mul_comm (u + 1) (fact u), ← Nat.mul_add, Nat.mul_one]
  rw [h1, h2, show 1 + (u + 1) = u + 2 from by omega]

/-- **Block triple.** `[u, u+2] = u! · (u+2)²` — the perfect-square
factorization of the 3-block. -/
theorem block_triple (u : Nat) :
    fact u + fact (u + 1) + fact (u + 2) = fact u * ((u + 2) * (u + 2)) := by
  have e1 : fact (u + 1) = fact u * pt u 1 := (fact_pt 1 u).symm
  have e2 : fact (u + 2) = fact u * pt u 2 := (fact_pt 2 u).symm
  have p1 : pt u 1 = u + 1 := by
    have h : pt u 1 = pt u 0 * (u + 0 + 1) := rfl
    have h0 : pt u 0 = 1 := rfl
    rw [h, h0, Nat.one_mul]
    omega
  have p2 : pt u 2 = (u + 1) * (u + 2) := by
    have h : pt u 2 = pt u 1 * (u + 1 + 1) := rfl
    rw [h, p1]
    omega
  have g1 : fact u + fact u * (u + 1) = fact u * (1 + (u + 1)) := by
    rw [← Nat.mul_add, Nat.mul_one]
  rw [e1, e2, p1, p2, g1, ← Nat.mul_add]
  apply Nat.eq_of_mul_eq_mul_left (fact_pos u)
  have hexp : (u + 1) * (u + 2) = u * u + 3 * u + 2 := by
    have s1 : (u + 1) * (u + 2) = u * (u + 2) + 1 * (u + 2) :=
      Nat.mul_add (u + 1) u (u + 2)
    have s2 : u * (u + 2) = u * u + u * 2 := Nat.mul_add u u 2
    have s3 : u * 2 = 2 * u := Nat.mul_comm u 2
    rw [s1, s2, s3, Nat.one_mul]
    omega
  have hexp2 : (u + 2) * (u + 2) = u * u + 4 * u + 4 := by
    have s1 : (u + 2) * (u + 2) = u * (u + 2) + 2 * (u + 2) :=
      Nat.mul_add (u + 2) u (u + 2)
    have s2 : u * (u + 2) = u * u + u * 2 := Nat.mul_add u u 2
    have s3 : u * 2 = 2 * u := Nat.mul_comm u 2
    have s4 : 2 * (u + 2) = 2 * u + 2 * 2 := Nat.mul_add 2 u 2
    rw [s1, s2, s3, s4]
    omega
  rw [hexp, hexp2]
  omega

-- ===========================================================================
-- §7  RECEIPTS
-- ===========================================================================

-- Theorem C receipts
#eval v2 (fact 4 + sumF [5, 7])                          -- 6  (5184 = 2^6·81)
#eval fact 4 + sumF [5, 7]                               -- 5184

-- Theorem B receipts (odd a: the valuation never grows)
#eval (v2 (fact 3), v2 (fact 3 + sumF [4, 6]))           -- (1, 1)
#eval (v2 (fact 5), v2 (fact 5 + sumF [6, 8, 10]))       -- (3, 3)
#eval (v2 (fact 7), v2 (fact 7 + sumF [9, 11, 100]))     -- (4, 4)

-- The (2,2) König-chain witnesses (Conjecture D: g(2,2) = ∞)
#eval v2 (fact 2 + sumF [3])                             -- 3   (2!+3! = 8)
#eval v2 (fact 2 + sumF [3, 5])                          -- 7   (= 128)
#eval v2 (fact 2 + sumF [3, 5, 8])                       -- 9   (= 40448)
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 8, 9])              -- 9
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 13, 14])        -- 13
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16, 19])  -- 18
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 17, 19, 21])  -- 23

-- Block identity receipts
#eval (fact 6 + fact 7, fact 6 * 8)                      -- (5760, 5760)
#eval (fact 6 + fact 7 + fact 8, fact 6 * 64)            -- (46080, 46080)
#eval (List.range 9).map (fun u =>
  (fact u + fact (u + 1) + fact (u + 2), fact u * (u + 2) * (u + 2)))

#print axioms erdos404_split
#print axioms erdos404_odd_a
#print axioms erdos404_f42
#print axioms block_pair
#print axioms block_triple
