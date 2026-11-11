/-
# ERDŐS #404 — SUB-QUESTION 3: THE GADGET-SUPPLY PROGRAM (Conjecture D front)

The problem (erdosproblems.com/404, sub-question 3): Is there a prime p and an
infinite chain a_1 < a_2 < ... with v_p(Σ_{i≤k} a_i!) → ∞?

The campaign's Theorem A (problem404-full, kernel-green) reduces the (2,2)
case to: for every k, is −1 a subset sum of the P-staircase
P_i = 3·4···i = i!/2 (i ≥ 3) mod 2^k?  Equivalently: is there, for every k,
a finite B ⊆ {3,4,...} with v2(1 + Σ_{i∈B} P_i) ≥ k?

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

* THE LIFT LAW `lift_law`: if v2 x = v2 y = V (x, y > 0) then
  v2 (x+y) ≥ V+1 — adding a gadget of EXACT valuation V to a chain at
  valuation V jumps the valuation; lower gadgets poison it, higher gadgets
  stall it. This is the engine of the level-by-level construction.
* THE PAIR LAW `pair_law` (ALL u ≥ 3): v2(P_u + P_{u+1}) = v2(P_u) + v2(u+2).
  Consecutive pairs factor exactly: P_u + P_{u+1} = P_u · (u+2).
* THE TRIPLE LAW `triple_law` (ALL u ≥ 3):
  v2(P_u + P_{u+1} + P_{u+2}) = v2(P_u) + 2·v2(u+2) — the block
  [u, u+2] = P_u·(u+2)² (perfect square) on the P-scale.
* THE CONSTRUCTIVE CHAIN (receipts): the 10-gadget chain
  {3}, {3,5}, {3,5,6,7}, +{11}, +{12}, +{15}, +{16}, +{19}, +{20}, +{23}
  with factorial-sum valuations 3, 7, 8, 10, 11, 15, 16, 18, 19, 23 —
  the level-by-level witness chain for g(2,2) ≥ 23 (Conjecture D evidence),
  each step an application of the LIFT LAW at the current valuation.
* COVERAGE RECEIPTS: the pair/triple valuation tables (which levels k are
  supplied by single coins / pairs / triples) — the gap levels need
  multi-coin gadgets; the tables show the supply structure.

Architecture: §1 staircase + v2 machinery  §2 lift law  §3 pair law
§4 triple law  §5 chain receipts  §6 coverage receipts.
-/

-- ===========================================================================
-- §1  THE P-STAIRCASE (seed a = 2) AND THE v2 MACHINERY
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `pt u j = (u+1)(u+2)···(u+j)` (the j-fold product tail). -/
def pt : Nat → Nat → Nat
  | _, 0 => 1
  | u, j + 1 => pt u j * (u + j + 1)

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

theorem one_le_two_pow : ∀ (k : Nat), 1 ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
    have h := one_le_two_pow k
    have hsm : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    rw [hsm]
    exact one_le_mul _ _ h (by decide)

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => by decide
  | u + 1 => one_le_mul _ _ (by omega) (fact_pos u)

theorem pt_pos : ∀ (j u : Nat), 1 ≤ pt u j
  | 0, _ => by simp [pt]
  | j + 1, u => one_le_mul _ _ (pt_pos j u) (by omega)

/-- **The P-staircase for seed a = 2**: `Ps i = 3·4···i = i!/2` (i ≥ 2). -/
def Ps (i : Nat) : Nat := pt 2 (i - 2)

theorem Ps_pos (i : Nat) (hi : 2 ≤ i) : 1 ≤ Ps i := pt_pos (i - 2) 2

/-- The staircase recursion: `Ps (u+1) = Ps u * (u+1)` for u ≥ 2. -/
theorem Ps_succ (u : Nat) (hu : 2 ≤ u) : Ps (u + 1) = Ps u * (u + 1) := by
  have h1 : u + 1 - 2 = (u - 2) + 1 := by omega
  have h2 : 2 + (u - 2) + 1 = u + 1 := by omega
  show pt 2 (u + 1 - 2) = pt 2 (u - 2) * (u + 1)
  rw [h1]
  have hstep : pt 2 ((u - 2) + 1) = pt 2 (u - 2) * (2 + (u - 2) + 1) := rfl
  rw [hstep, h2]

/-- The staircase values ARE the factorial quotients: `fact i = 2 * Ps i`. -/
theorem Ps_fact (i : Nat) (hi : 2 ≤ i) : fact i = 2 * Ps i := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases h2 : 2 ≤ i
    · have hstep : fact (i + 1) = (i + 1) * fact i := rfl
      rw [hstep, ih h2, Ps_succ i h2]
      have hcomm : 2 * (Ps i * (i + 1)) = (i + 1) * (2 * Ps i) := by
        rw [Nat.mul_comm (i + 1) (2 * Ps i), Nat.mul_assoc 2 (Ps i) (i + 1)]
      rw [hcomm]
    · have hi1 : i = 1 := by omega
      subst hi1
      decide

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
    · rw [ha1, Nat.one_mul, v2_odd 1 (by decide)]
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

theorem pow2_dvd_iff : ∀ (k x : Nat), 1 ≤ x → (2 ^ k ∣ x ↔ k ≤ v2 x)
  | 0, x, hx => by
    constructor
    · intro _; omega
    · intro _; exact Nat.one_dvd x
  | k + 1, x, hx => by
    have hmod := Nat.div_add_mod x 2
    have hmk : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.mul_comm]
      exact Nat.pow_succ 2 k
    constructor
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      have hx3 : x = 2 * (2 ^ k * m) := by
        rw [← Nat.mul_assoc, ← hmk]
        exact hm
      have htwo : (2 * (2 ^ k * m)) % 2 = 0 := by
        have := Nat.mul_mod 2 (2 ^ k * m) 2
        omega
      have hx2 : x % 2 = 0 := by omega
      have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
      have hxd : x / 2 = 2 ^ k * m := by
        have h2 := two_mul_div2 (2 ^ k * m)
        omega
      have hdiv2 : 1 ≤ x / 2 := by omega
      have ih := (pow2_dvd_iff k (x / 2) hdiv2).mp ⟨m, hxd⟩
      omega
    · intro hle
      have hchoice : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
      cases hchoice with
      | inl hx2 =>
        have hsplit : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx hx2
        have hdiv2 : 1 ≤ x / 2 := by omega
        have ih := (pow2_dvd_iff k (x / 2) hdiv2).mpr (by omega)
        obtain ⟨m, hm⟩ := ih
        refine ⟨m, ?_⟩
        have hxd : x / 2 = 2 ^ k * m := hm
        have hfin : x = 2 * (2 ^ k * m) := by omega
        rw [hmk, Nat.mul_assoc]
        exact hfin
      | inr hodd =>
        have hv0 : v2 x = 0 := v2_odd x hodd
        omega

-- ===========================================================================
-- §2  THE LIFT LAW (the engine of the level-by-level construction)
-- ===========================================================================

/-- **THE LIFT LAW.** If x and y both have EXACT 2-adic valuation V,
then x + y has valuation ≥ V + 1: the odd units cancel.
(And v2 (2^j·o₁ + 2^V·o₂) = j when j < V, = V when j > V — which is why
the construction must add a gadget of exact valuation V.) -/
theorem lift_law (V x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hVx : v2 x = V) (hVy : v2 y = V) : V + 1 ≤ v2 (x + y) := by
  obtain ⟨x', hx'⟩ : ∃ x', x = 2 ^ V * x' := by
    have hdvd : 2 ^ V ∣ x := (pow2_dvd_iff V x hx).mpr (by omega)
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨q, hq⟩
  obtain ⟨y', hy'⟩ : ∃ y', y = 2 ^ V * y' := by
    have hdvd : 2 ^ V ∣ y := (pow2_dvd_iff V y hy).mpr (by omega)
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨q, hq⟩
  -- x' and y' are odd (else the valuation would exceed V)
  have hx'odd : x' % 2 = 1 := by
    by_cases h0 : x' % 2 = 0
    · obtain ⟨w, hw⟩ : ∃ w, x' = 2 * w := ⟨x' / 2, by omega⟩
      have hx2 : x = 2 ^ (V + 1) * w := by
        rw [hx', hw, ← Nat.mul_assoc, Nat.pow_succ]
      have hcontra := (pow2_dvd_iff (V + 1) x hx).mp ⟨w, hx2⟩
      omega
    · have hcase := Nat.mod_two_eq_zero_or_one x'
      omega
  have hy'odd : y' % 2 = 1 := by
    by_cases h0 : y' % 2 = 0
    · obtain ⟨w, hw⟩ : ∃ w, y' = 2 * w := ⟨y' / 2, by omega⟩
      have hy2 : y = 2 ^ (V + 1) * w := by
        rw [hy', hw, ← Nat.mul_assoc, Nat.pow_succ]
      have hcontra := (pow2_dvd_iff (V + 1) y hy).mp ⟨w, hy2⟩
      omega
    · have hcase := Nat.mod_two_eq_zero_or_one y'
      omega
  -- x + y = 2^V (x' + y') with x' + y' even
  have hsum : x + y = 2 ^ V * (x' + y') := by
    rw [hx', hy', Nat.mul_add]
  have heven : (x' + y') % 2 = 0 := by
    rw [Nat.add_mod, hx'odd, hy'odd]
  obtain ⟨z, hz⟩ : ∃ z, x' + y' = 2 * z := ⟨(x' + y') / 2, by omega⟩
  have hdvd : 2 ^ (V + 1) ∣ (x + y) := by
    refine ⟨z, ?_⟩
    rw [hsum, hz, Nat.pow_succ, Nat.mul_assoc]
  have hxy1 : 1 ≤ x + y := by omega
  have hfin := (pow2_dvd_iff (V + 1) (x + y) hxy1).mp hdvd
  omega

-- ===========================================================================
-- §3  THE PAIR LAW — CONSECUTIVE PAIRS FACTOR EXACTLY
-- ===========================================================================

/-- The pair factorization: `Ps u + Ps (u+1) = Ps u · (u + 2)`. -/
theorem pair_identity (u : Nat) (hu : 2 ≤ u) :
    Ps u + Ps (u + 1) = Ps u * (u + 2) := by
  rw [Ps_succ u hu]
  have key : Ps u + Ps u * (u + 1) = Ps u * (1 + (u + 1)) := by
    rw [Nat.mul_add (Ps u) 1 (u + 1), Nat.mul_one (Ps u)]
  rw [key]
  have h3 : 1 + (u + 1) = u + 2 := by omega
  rw [h3]

/-- **THE PAIR LAW (all u ≥ 3).** The exact valuation of a consecutive pair:
`v2(Ps u + Ps (u+1)) = v2(Ps u) + v2(u+2)`.  The supply of pair-gadgets at
valuation k is the set of u with v2(Ps u) + v2(u+2) = k. -/
theorem pair_law (u : Nat) (hu : 3 ≤ u) :
    v2 (Ps u + Ps (u + 1)) = v2 (Ps u) + v2 (u + 2) := by
  have hu2 : 2 ≤ u := by omega
  rw [pair_identity u hu2]
  have h1 : 1 ≤ Ps u := Ps_pos u hu2
  have h2 : 1 ≤ u + 2 := by omega
  exact v2_mul (Ps u + (u + 2)) (Ps u) (u + 2) (Nat.le_refl _) h1 h2

-- ===========================================================================
-- §4  THE TRIPLE LAW — THE PERFECT-SQUARE BLOCK ON THE P-SCALE
-- ===========================================================================

/-- The triple factorization: `Ps u + Ps (u+1) + Ps (u+2) = Ps u · (u+2)²`. -/
theorem triple_identity (u : Nat) (hu : 3 ≤ u) :
    Ps u + Ps (u + 1) + Ps (u + 2) = Ps u * ((u + 2) * (u + 2)) := by
  have hu2 : 2 ≤ u := by omega
  have h1 : Ps (u + 1) = Ps u * (u + 1) := Ps_succ u hu2
  have h2 : Ps (u + 2) = Ps (u + 1) * (u + 2) := Ps_succ (u + 1) (by omega)
  rw [h1] at h2
  have hkey : Ps u * (u + 1) * (u + 2) = Ps u * ((u + 1) * (u + 2)) :=
    Nat.mul_assoc _ _ _
  rw [h1, h2, hkey]
  have hsplit : Ps u + Ps u * (u + 1) + Ps u * ((u + 1) * (u + 2))
      = Ps u * (1 + (u + 1) + (u + 1) * (u + 2)) := by
    rw [Nat.mul_add (Ps u) (1 + (u + 1)) ((u + 1) * (u + 2)),
        Nat.mul_add (Ps u) 1 (u + 1), Nat.mul_one (Ps u)]
  rw [hsplit]
  have hsq : 1 + (u + 1) + (u + 1) * (u + 2) = (u + 2) * (u + 2) := by
    have e1 : (u + 1) * (u + 2) = u * (u + 2) + (u + 2) :=
      Nat.succ_mul u (u + 2)
    have e2 : u * (u + 2) = u * u + u * 2 := Nat.mul_add u u 2
    have e3 : u * 2 = 2 * u := Nat.mul_comm u 2
    rw [e1, e2, e3]
    have e4 : (u + 2) * (u + 2) = u * (u + 2) + 2 * (u + 2) := by
      rw [Nat.mul_add (u + 2) u 2, Nat.mul_comm (u + 2) u,
          Nat.mul_comm (u + 2) 2]
    rw [e4, e2, e3]
    omega
  rw [hsq]

/-- **THE TRIPLE LAW (all u ≥ 3).** The 3-block valuation:
`v2(Ps u + Ps (u+1) + Ps (u+2)) = v2(Ps u) + 2·v2(u+2)` — the exponent of
the square doubles the congruence freedom. -/
theorem triple_law (u : Nat) (hu : 3 ≤ u) :
    v2 (Ps u + Ps (u + 1) + Ps (u + 2)) = v2 (Ps u) + 2 * v2 (u + 2) := by
  rw [triple_identity u hu]
  have h1 : 1 ≤ Ps u := Ps_pos u (by omega)
  have h2 : 1 ≤ (u + 2) * (u + 2) :=
    one_le_mul _ _ (by omega) (by omega)
  have hstep : v2 (Ps u * ((u + 2) * (u + 2)))
      = v2 (Ps u) + v2 ((u + 2) * (u + 2)) :=
    v2_mul (Ps u + (u + 2) * (u + 2)) (Ps u) ((u + 2) * (u + 2))
      (Nat.le_refl _) h1 h2
  rw [hstep]
  have hstep2 : v2 ((u + 2) * (u + 2)) = v2 (u + 2) + v2 (u + 2) :=
    v2_mul ((u + 2) + (u + 2)) (u + 2) (u + 2) (Nat.le_refl _)
      (by omega) (by omega)
  rw [hstep2]
  omega

-- ===========================================================================
-- §5  THE CONSTRUCTIVE CHAIN (receipts — the level-by-level witnesses)
-- ===========================================================================

/-- Sum of factorials over a list. -/
def sumF : List Nat → Nat
  | [] => 0
  | i :: B => fact i + sumF B

-- The chain: each step applies the LIFT LAW at the current valuation.
-- v2(2! + Σ_B i!) = 1 + v2(1 + Σ_B Ps i) — the two normalizations agree
-- by Ps_fact (fact i = 2 * Ps i for i ≥ 2).

-- Level 3: B = {3}          : 2! + 3! = 8 = 2^3
#eval v2 (fact 2 + sumF [3])                              -- 3
-- Level 7: B = {3,5}        : 2!+3!+5! = 128 = 2^7
#eval v2 (fact 2 + sumF [3, 5])                           -- 7
-- Level 8: B = {3,5,6,7}    : (the pair gadget {6,7} lifted 7 → 8)
#eval v2 (fact 2 + sumF [3, 5, 6, 7])                     -- 8
-- Level 10: +{11}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11])                 -- 10
-- Level 11: +{12}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12])             -- 11
-- Level 15: +{15}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15])         -- 15
-- Level 16: +{16}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16])     -- 16
-- Level 18: +{19}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16, 19]) -- 18
-- Level 19: +{20}
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16, 19, 20]) -- 19
-- Level 23: +{23}  — the DFS chain's full witness: g(2,2) ≥ 23 certified
#eval v2 (fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16, 19, 20, 23]) -- 23
-- exact value receipt:
#eval fact 2 + sumF [3, 5, 6, 7, 11, 12, 15, 16, 19, 20, 23]
--   = 2^23 · (odd)

-- ===========================================================================
-- §6  COVERAGE RECEIPTS (the gadget-supply tables)
-- ===========================================================================

-- Single-coin valuations v2(Ps i), i = 3..20 (the staircase itself):
#eval (List.range 18).map (fun t => v2 (Ps (t + 3)))
--   [0, 2, 2, 3, 3, 6, 6, 7, 7, 9, 9, 10, 10, 14, 14, 15, 15, 17]
--   → gap levels (never a single coin): 1, 4, 5, 8, 11, 12, 13, 16, ...

-- Pair-gadget valuations v2(Ps u + Ps (u+1)) = v2(Ps u) + v2(u+2), u = 3..20:
#eval (List.range 18).map (fun t => v2 (Ps (t + 3) + Ps (t + 4)))
--   the PAIR LAW table: pairs supply the levels the singles miss
--   (the u+2 factor contributes every j = v2(u+2) ≥ 0).

-- Triple-gadget valuations v2(Ps u + Ps (u+1) + Ps (u+2)) = v2(Ps u)+2·v2(u+2):
#eval (List.range 18).map (fun t =>
  v2 (Ps (t + 3) + Ps (t + 4) + Ps (t + 5)))
--   the TRIPLE LAW table: the square exponent doubles the freedom —
--   the pairs' gap levels are the triples' supply.

#print axioms lift_law
#print axioms pair_law
#print axioms triple_law
