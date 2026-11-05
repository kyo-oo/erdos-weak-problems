/-
# ERDŐS #404 — THEOREM B FOR EVERY PRIME p: THE `p ∣ a+1` CLASS (KILL #15)

The problem (erdosproblems.com/404): for which (a, p) is there a finite upper
bound on k with p^k | (a_1! + ... + a_n!) for some a = a_1 < ... < a_n?
If f(a,p) is the greatest such k, how does it behave?

## THE CLASS THEOREM (Theorem B, generalized from p = 2 to EVERY prime)

For EVERY prime p and EVERY a with `p ∣ a + 1`, and EVERY finite index list
B beyond a:

    v_p (a! + Σ_{i ∈ B} i!)  =  v_p (a!).

The p-adic valuation NEVER grows on the whole class.  Consequently
**f(a,p) = v_p(a!) exactly** for every (a,p) with p prime dividing a+1 —
e.g. for every prime p at a = p − 1, and for the p = 2 / odd-a class of
Kill #7 (`erdos404_odd_a`), which is the p = 2 instance of this theorem.

The proof needs p ≥ 2 only (primality is never used — the theorem holds for
every integer p ≥ 2 dividing a+1):

* every staircase term  P_i = (a+1)(a+2)···i  carries the factor (a+1) ≡ 0
  (mod p), so  `1 + Σ P_i ≡ 1 (mod p)`;
* the unit-congruence law  `vpad_congr_unit`:  u ≡ 1 (mod p)  ⟹
  v_p(x·u) = v_p(x)  for all x ≥ 1 — by fuel induction on x, using only
  mod-arithmetic (NO Euclid lemma needed:  (x·u) % p = x % p);
* the split of Theorem A:  a! + Σ_B i! = a! · (1 + Σ_B P_i).

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

* `vpadf`/`vpad` — the general-p p-adic valuation (fuel-structural,
  kernel-transparent), with the saturation law `vpadf_sat` (fuel ≥ value
  never changes the result), the step law `vpad_step` and the non-divisor
  law `vpad_nondiv`.
* `vpad_congr_unit` — the unit-congruence law (the engine of the class).
* `pt_dvd_of_dvd`, `sumP_mod_zero`, `sumP_unit_mod` — the staircase dies
  mod p on the class.
* **`erdos404_theoremB`** — the class theorem, stated for all p ≥ 2.
* RECEIPTS: concrete valuations across several primes (2, 3, 5, 11).

Architecture: §1 helpers (shared with PadicReduction.lean)  §2 the general-p
valuation  §3 the unit-congruence law  §4 the staircase congruence
§5 Theorem B  §6 receipts.
-/

-- ===========================================================================
-- §1  FACTORIALS, PRODUCT TAILS, LIST SUMS, ARITHMETIC HELPERS
-- (shared with problem404-full/PadicReduction.lean; repeated here so this
--  kernel is self-contained and CI-compiles standalone)
-- ===========================================================================

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

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
    omega
  have R : a * (1 + (x + y)) = a + (a * x + a * y) := by
    rw [Nat.mul_add a 1 (x + y), Nat.mul_add a x y]
    omega
  rw [L, R]
  omega

/-- **Theorem A (factorization).** For every list B of indices beyond a:
`a! + Σ_B i! = a! · (1 + Σ_B P_i)` with `P_i = (a+1)···i`. -/
theorem sumF_split (a : Nat) : ∀ (B : List Nat), (∀ i ∈ B, a < i) →
    fact a + sumF B = fact a * (1 + sumP a B)
  | [], _ => by
    show fact a + 0 = fact a * (1 + 0)
    simp
  | i :: B, hall => by
    have hi : a < i := hall i (List.mem_cons_self ..)
    have hrest := sumF_split a B (by
      intro j hj
      exact hall j (List.mem_cons_of_mem _ hj))
    obtain ⟨j, hj⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
    have hfi : fact i = fact a * pt a j := by rw [hj, fact_pt j a]
    have hij : i - a = j := by omega
    have hpsame : pt a (i - a) = pt a j := by rw [hij]
    have hunfold : sumF (i :: B) = fact i + sumF B := rfl
    have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
    calc fact a + sumF (i :: B)
        = fact i + (fact a + sumF B) := by rw [hunfold]; omega
      _ = fact a * pt a j + fact a * (1 + sumP a B) := by rw [hfi, hrest]
      _ = fact a * (1 + (pt a (i - a) + sumP a B)) := by
          rw [hpsame]
          exact mul_add_split (fact a) (pt a j) (sumP a B)

-- ===========================================================================
-- §2  THE p-ADIC VALUATION (general p, fuel-structural, kernel-transparent)
-- ===========================================================================

/-- Fuel-structural p-adic valuation engine: `vpadf p f n` counts factors of
p in n with f fuel.  Structural recursion on the fuel — total for every p
(for p ≤ 1 the count is meaningless but the recursion still terminates). -/
def vpadf : Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | _, _, 0 => 0
  | p, f + 1, n + 1 =>
      if (n + 1) % p = 0 then 1 + vpadf p f ((n + 1) / p) else 0

/-- `vpad p n = vpadf p n n` — fuel = value always suffices
(v_p(n) ≤ log_2 n ≤ n for p ≥ 2). -/
def vpad (p : Nat) (n : Nat) : Nat := vpadf p n n

theorem vpad_unfold_succ (p N : Nat) :
    vpad p (N + 1) =
      if (N + 1) % p = 0 then 1 + vpadf p N ((N + 1) / p) else 0 := rfl

/-- **Saturation.** For p ≥ 2, fuel beyond the value never changes the
result: `vpadf p f n = vpadf p n n` whenever `n ≤ f`.  (Cumulative fuel
induction on the bound F.) -/
theorem vpadf_sat (p : Nat) (hp : 2 ≤ p) :
    ∀ (F f : Nat), f ≤ F → ∀ (n : Nat), n ≤ f →
    vpadf p f n = vpadf p n n := by
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
        have e1 : vpadf p (F' + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpadf p F' ((N + 1) / p) else 0 := rfl
        have e2 : vpadf p (N + 1) (N + 1) =
            if (N + 1) % p = 0 then 1 + vpadf p N ((N + 1) / p) else 0 := rfl
        rw [e1, e2]
        by_cases hmod : (N + 1) % p = 0
        · rw [if_pos hmod, if_pos hmod]
          have hdlt : (N + 1) / p < N + 1 :=
            Nat.div_lt_self (by omega) (by omega)
          have i1 := ih F' (by omega) ((N + 1) / p) (by omega)
          have i2 := ih N (by omega) ((N + 1) / p) (by omega)
          rw [i1, i2]
        · rw [if_neg hmod, if_neg hmod]

/-- If `p ∤ n` (and n ≥ 1) then `vpad p n = 0`. -/
theorem vpad_nondiv (p n : Nat) (hn : 1 ≤ n) (hne : n % p ≠ 0) :
    vpad p n = 0 := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hne' : (N + 1) % p ≠ 0 := by rw [← hN]; exact hne
  rw [hN, vpad_unfold_succ, if_neg hne']

/-- **The step law.** For p ≥ 2 and p ∣ n ≥ 1:
`vpad p n = 1 + vpad p (n / p)`. -/
theorem vpad_step (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (hd : n % p = 0) :
    vpad p n = 1 + vpad p (n / p) := by
  obtain ⟨N, hN⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hmod : (N + 1) % p = 0 := by rw [← hN]; exact hd
  have h1 : vpad p (N + 1) = 1 + vpadf p N ((N + 1) / p) := by
    rw [vpad_unfold_succ, if_pos hmod]
  have hdlt : (N + 1) / p < N + 1 := Nat.div_lt_self (by omega) (by omega)
  have h2 : vpadf p N ((N + 1) / p) = vpad p ((N + 1) / p) :=
    vpadf_sat p hp N N (Nat.le_refl _) ((N + 1) / p) (by omega)
  rw [hN, h1, h2]

-- ===========================================================================
-- §3  THE UNIT-CONGRUENCE LAW (the engine of the class)
-- ===========================================================================

/-- **Unit-congruence law.** If `u ≡ 1 (mod p)` and x, u ≥ 1 with p ≥ 2,
then `v_p (x · u) = v_p (x)`.  Fuel induction on x; needs NO Euclid lemma —
`(x·u) % p = x % p` by mod-arithmetic alone. -/
theorem vpad_congr_unit : ∀ (F p x u : Nat), x ≤ F → 2 ≤ p → 1 ≤ x → 1 ≤ u →
    u % p = 1 → vpad p (x * u) = vpad p x := by
  intro F
  induction F with
  | zero => intro p x u hxF hp hx hu hu1; omega
  | succ F ih =>
    intro p x u hxF hp hx hu hu1
    by_cases hx0 : x % p = 0
    · -- p ∣ x: step both sides down by one p
      have hmod := Nat.div_add_mod x p
      rw [hx0] at hmod
      have hxdiv : p * (x / p) = x := by simpa using hmod
      have hxp1 : 1 ≤ x / p := by
        rcases Nat.eq_zero_or_pos (x / p) with h | h
        · rw [h, Nat.mul_zero] at hxdiv; omega
        · exact h
      have hxdiv' : (x / p) * p = x := by rw [Nat.mul_comm]; exact hxdiv
      have hxpF : x / p ≤ F := by
        have h2 : (x / p) * 2 ≤ (x / p) * p := Nat.mul_le_mul_left _ hp
        omega
      have hxu0 : (x * u) % p = 0 := by
        rw [Nat.mul_mod, hx0, hu1]
        simp
      have hxu1 : 1 ≤ x * u := one_le_mul x u hx hu
      have hstep := vpad_step p (x * u) hp hxu1 hxu0
      have hdiv : (x * u) / p = (x / p) * u := by
        obtain ⟨m, hm⟩ : ∃ m, x / p = m := ⟨x / p, rfl⟩
        have hdx : p * m = x := by rw [← hm]; exact hxdiv
        rw [hm, ← hdx, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
      rw [hstep, hdiv, ih p (x / p) u hxpF hp hxp1 hu hu1]
      have hstepx := vpad_step p x hp hx hx0
      omega
    · -- p ∤ x: then p ∤ x·u (congruence!), both valuations are 0
      have hxu0 : (x * u) % p ≠ 0 := by
        rw [Nat.mul_mod, hu1, Nat.mul_one, Nat.mod_mod]
        exact hx0
      rw [vpad_nondiv p (x * u) (one_le_mul x u hx hu) hxu0,
          vpad_nondiv p x hx hx0]

-- ===========================================================================
-- §4  THE STAIRCASE DIES MOD p ON THE CLASS  (p ∣ a+1)
-- ===========================================================================

/-- If `p ∣ a + 1` then every staircase term `pt a j = (a+1)···(a+j)`
(with j ≥ 1) is divisible by p. -/
theorem pt_dvd_of_dvd (a p : Nat) (hd : p ∣ a + 1) :
    ∀ (j : Nat), 1 ≤ j → p ∣ pt a j
  | 0, _ => by omega
  | 1, _ => by
    have h1 : pt a 1 = 1 * (a + 1) := rfl
    rw [h1, Nat.one_mul]
    exact hd
  | j + 2, _ => by
    have IH : p ∣ pt a (j + 1) := pt_dvd_of_dvd a p hd (j + 1) (by omega)
    have hstep : pt a (j + 2) = pt a (j + 1) * (a + (j + 1) + 1) := rfl
    rw [hstep]
    exact Nat.dvd_trans IH (Nat.dvd_mul_right _ _)

/-- If `p ∣ a + 1`, the whole staircase sum is ≡ 0 mod p. -/
theorem sumP_mod_zero (a p : Nat) (hd : p ∣ a + 1) :
    ∀ (B : List Nat), (∀ i ∈ B, a < i) → sumP a B % p = 0 := by
  intro B
  induction B with
  | nil => intro _; show (0 : Nat) % p = 0; simp
  | cons i B ih =>
    intro hall
    have hi : a < i := hall i (List.mem_cons_self ..)
    have hrest := ih (by
      intro j hj
      exact hall j (List.mem_cons_of_mem _ hj))
    have hj1 : 1 ≤ i - a := by omega
    have hpt := pt_dvd_of_dvd a p hd (i - a) hj1
    have hptmod : pt a (i - a) % p = 0 := Nat.mod_eq_zero_of_dvd hpt
    have hpu : sumP a (i :: B) = pt a (i - a) + sumP a B := rfl
    show sumP a (i :: B) % p = 0
    rw [hpu, Nat.add_mod, hptmod, hrest, Nat.zero_add, Nat.zero_mod]

/-- If `p ∣ a + 1` (p ≥ 2), then `1 + Σ P ≡ 1 (mod p)`: the unit factor. -/
theorem sumP_unit_mod (a p : Nat) (hp : 2 ≤ p) (hd : p ∣ a + 1)
    (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    (1 + sumP a B) % p = 1 := by
  have h0 := sumP_mod_zero a p hd B hB
  rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

-- ===========================================================================
-- §5  THEOREM B — THE p ∣ a+1 CLASS FOR EVERY p ≥ 2 (hence every prime)
-- ===========================================================================

/-- **THEOREM B (Erdős #404, the `p ∣ a+1` class, every prime p).**
For every p ≥ 2 with `p ∣ a + 1` and every finite index list B beyond a:

    v_p (a! + Σ_{i ∈ B} i!) = v_p (a!).

The p-adic valuation never grows.  Consequently
`f(a,p) = v_p(a!)` exactly on the class — e.g. f(p−1, p) = v_p((p−1)!)
for every prime p, and (at p = 2) every odd a.  Primality is never used:
the theorem holds for every integer p ≥ 2 dividing a+1. -/
theorem erdos404_theoremB (a p : Nat) (hp : 2 ≤ p) (hd : p ∣ a + 1)
    (B : List Nat) (hB : ∀ i ∈ B, a < i) :
    vpad p (fact a + sumF B) = vpad p (fact a) := by
  have hsplit : fact a + sumF B = fact a * (1 + sumP a B) :=
    sumF_split a B hB
  have hu1 : (1 + sumP a B) % p = 1 := sumP_unit_mod a p hp hd B hB
  rw [hsplit, vpad_congr_unit (fact a) p (fact a) (1 + sumP a B)
    (Nat.le_refl (fact a)) hp (fact_pos a) (by omega) hu1]

-- ===========================================================================
-- §6  RECEIPTS
-- ===========================================================================

-- Valuation sanity across primes (compiler-evaluated; vpadf is structural)
#eval (vpad 2 (fact 4), vpad 3 (fact 6), vpad 5 (fact 10), vpad 7 (fact 7))
     -- (3, 2, 2, 1): 24 = 2^3·3; 720 = 3^2·80; 3628800 = 5^2·145152; 5040 = 7·720

-- Theorem B receipts: the valuation never grows on the class
-- a = 2, p = 3 (3 ∣ 3):   2! + 4! + 6! = 746, v_3 = 0 = v_3(2!)
#eval (vpad 3 (fact 2), vpad 3 (fact 2 + sumF [4, 6]))            -- (0, 0)
-- a = 5, p = 2 (2 ∣ 6):   5! + 6! + 8! = 41160 = 2^3·5145, v_2 = 3 = v_2(5!)
#eval (vpad 2 (fact 5), vpad 2 (fact 5 + sumF [6, 8]))            -- (3, 3)
-- a = 8, p = 3 (3 ∣ 9):   8! + 10! + 11!, v_3 = 2 = v_3(8!)
#eval (vpad 3 (fact 8), vpad 3 (fact 8 + sumF [10, 11]))          -- (2, 2)
-- a = 10, p = 11 (11 ∣ 11):  v_11(10!) = 0 = v_11(10! + 11! + 15!)
#eval (vpad 11 (fact 10), vpad 11 (fact 10 + sumF [11, 15]))      -- (0, 0)
-- a = 14, p = 5 (5 ∣ 15):  v_5(14!) = 2 = v_5(14! + 16! + 21!)
#eval (vpad 5 (fact 14), vpad 5 (fact 14 + sumF [16, 21]))        -- (2, 2)
-- a = 1, p = 2 (2 ∣ 2):   1! + 2! + 3! = 9, v_2 = 0 = v_2(1!)
#eval (vpad 2 (fact 1), vpad 2 (fact 1 + sumF [2, 3]))            -- (0, 0)

#print axioms erdos404_theoremB
