/-
# ERDŐS #404 — THE LEFT-FACTORIAL KERNEL LAW (2-ADIC FORM)

For every u and every N ≥ u + 3,

    v₂ ( Σ_{a=u}^{N} a! )  =  v₂ (u!) + v₂ (u + 2).

## The mathematics (the kernel factorization)

Factor u! out of the sum:  Σ_{a=u}^{N} a! = u! · K(u, N−u), where the
partial left-factorial kernel is

    K(u, M) = Σ_{j=0}^{M} (u+1)(u+2)···(u+j)     (empty product = 1).

The whole law collapses to ONE algebraic identity plus parity:

    K(u, 3) = 1 + (u+1) + (u+1)(u+2) + (u+1)(u+2)(u+3)
            = (u+2) + (u+1)(u+2)(u+4)
            = (u+2) · (1 + (u+1)(u+4)),

and the cofactor 1 + (u+1)(u+4) is ODD because (u+1)(u+4) is even
(u+1 and u+4 have opposite parity).  Every further summand j ≥ 4 is
(u+2) times an EVEN number, since the product (u+1)···(u+j) contains
the opposite-parity pair u+1, u+4 outside the u+2 factor.  Hence

    K(u, M) = (u+2) · (odd)   for every M ≥ 3,

and v₂(Σ) = v₂(u!) + v₂(u+2) + v₂(odd) = v₂(u!) + v₂(u+2).

## Architecture

* §1  `fact`, `pt` (product tails), `kern` (partial kernels), `sumFactFrom`.
* §2  parity lemmas (opposite-parity pair u+1, u+4).
* §3  the closed form `kern u 3 = (u+2) * (1 + (u+1)*(u+4))` (factored
  Nat.mul_add/mul_comm surgery — no ring tactic).
* §4  tail evenness: for j ≥ 4, `pt u j = (u+2) * even`.
* §5  `kern u M = (u+2) * odd` for M ≥ 3 (fuel induction on M).
* §6  `sumFactFrom u k = fact u * kern u k` (factorial-tail split).
* §7  `v2` (binary valuation), additivity `v2 (a*b) = v2 a + v2 b`
  (fuel induction), odd-vanishing.
* §8  Headline: `kernel_law`.

Core Lean 4 only.  No Mathlib.  No `sorry`.  No custom axioms.
-/

-- ===========================================================================
-- §1  FACTORIALS, PRODUCT TAILS, KERNELS, SUMS
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `pt u j = (u+1)(u+2)···(u+j)`, the j-fold product tail. -/
def pt : Nat → Nat → Nat
  | _, 0 => 1
  | u, j + 1 => pt u j * (u + j + 1)

/-- `kern u M = Σ_{j=0}^{M} pt u j`, the partial left-factorial kernel. -/
def kern : Nat → Nat → Nat
  | _, 0 => 1
  | u, M + 1 => kern u M + pt u (M + 1)

/-- `sumFactFrom u k = Σ_{j=0}^{k} (u+j)!`. -/
def sumFactFrom : Nat → Nat → Nat
  | u, 0 => fact u
  | u, k + 1 => sumFactFrom u k + fact (u + k + 1)

-- ===========================================================================
-- §2  PARITY LEMMAS
-- ===========================================================================

theorem even_mul_left (a b : Nat) (h : a % 2 = 0) : a * b % 2 = 0 := by
  rw [Nat.mul_mod, h]
  simp

/-- u+1 and u+4 have opposite parity, so their product is even. -/
theorem even_u14 (u : Nat) : (u + 1) * (u + 4) % 2 = 0 := by
  cases hp : u % 2 with
  | zero =>
    have he : (u + 1) * (u + 4) = (u + 4) * (u + 1) := Nat.mul_comm _ _
    rw [he]
    exact even_mul_left _ _ (by omega)
  | succ k =>
    exact even_mul_left _ _ (by omega)

/-- The tail cofactor (u+1)(u+3)(u+4) is even. -/
theorem even_u134 (u : Nat) : (u + 1) * (u + 3) * (u + 4) % 2 = 0 := by
  cases hp : u % 2 with
  | zero =>
    have he : (u + 1) * (u + 3) * (u + 4) = (u + 4) * ((u + 1) * (u + 3)) := by
      rw [Nat.mul_comm ((u + 1) * (u + 3)) (u + 4)]
    rw [he]
    exact even_mul_left _ _ (by omega)
  | succ k =>
    have he : (u + 1) * (u + 3) * (u + 4) = (u + 1) * ((u + 3) * (u + 4)) :=
      Nat.mul_assoc _ _ _
    rw [he]
    exact even_mul_left _ _ (by omega)

-- ===========================================================================
-- §3  THE CLOSED FORM OF THE 3-KERNEL
-- ===========================================================================

/-- AC-shuffle: a·b·c·d = b·(a·c·d). -/
theorem ac4 (a b c d : Nat) : a * b * c * d = b * (a * c * d) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b, ← Nat.mul_assoc, Nat.mul_assoc]

theorem kern3 (u : Nat) :
    kern u 3 = (u + 2) * (1 + (u + 1) * (u + 4)) := by
  have h1 : kern u 3 = 1 + (u + 1) + (u + 1) * (u + 2)
      + (u + 1) * (u + 2) * (u + 3) := by
    simp [kern, pt]
  have hu2 : 1 + (u + 1) = u + 2 := by omega
  have hu4 : 1 + (u + 3) = u + 4 := by omega
  have key1 : (u + 1) * (u + 2) + (u + 1) * (u + 2) * (u + 3)
      = (u + 1) * (u + 2) * (u + 4) := by
    have e : (u + 1) * (u + 2) + (u + 1) * (u + 2) * (u + 3)
        = (u + 1) * (u + 2) * 1 + (u + 1) * (u + 2) * (u + 3) := by
      rw [Nat.mul_one]
    rw [e, ← Nat.mul_add, hu4]
  have ac : (u + 2) * ((u + 1) * (u + 4)) = (u + 1) * (u + 2) * (u + 4) := by
    rw [Nat.mul_comm (u + 2) ((u + 1) * (u + 4)), Nat.mul_assoc,
      Nat.mul_comm (u + 4) (u + 2), ← Nat.mul_assoc]
  rw [h1, hu2, Nat.add_assoc, key1]
  rw [Nat.mul_add (u + 2) 1 ((u + 1) * (u + 4)), Nat.mul_one (u + 2), ac]

/-- The 3-kernel cofactor is odd. -/
theorem kern3_odd (u : Nat) : (1 + (u + 1) * (u + 4)) % 2 = 1 := by
  rw [Nat.add_mod, even_u14]

-- ===========================================================================
-- §4  TAIL EVENNESS (j ≥ 4)
-- ===========================================================================

/-- For j ≥ 4 the product tail factors as (u+2) times an even number. -/
theorem pt_tail : ∀ (k u : Nat), ∃ r, pt u (k + 4) = (u + 2) * r ∧ r % 2 = 0
  | 0, u => by
    refine ⟨(u + 1) * (u + 3) * (u + 4), ?_, even_u134 u⟩
    have hpt : pt u 4 = (u + 1) * (u + 2) * (u + 3) * (u + 4) := by
      simp [pt]
    rw [hpt, ac4]
  | k + 1, u => by
    have ⟨r, hr1, hr2⟩ := pt_tail k u
    have he : k + 1 + 4 = (k + 4) + 1 := by omega
    refine ⟨r * (u + (k + 4) + 1), ?_, ?_⟩
    · show pt u (k + 1 + 4) = _
      rw [he]
      show pt u (k + 4) * (u + (k + 4) + 1) = _
      rw [hr1, Nat.mul_assoc]
    · exact even_mul_left _ _ hr2

-- ===========================================================================
-- §5  THE KERNEL LAW (fuel induction on M)
-- ===========================================================================

/-- For every M ≥ 3 the kernel is (u+2) times an ODD number. -/
theorem kern_odd : ∀ (k u : Nat), ∃ w, kern u (k + 3) = (u + 2) * w ∧ w % 2 = 1
  | 0, u => by
    refine ⟨1 + (u + 1) * (u + 4), kern3 u, kern3_odd u⟩
  | k + 1, u => by
    have ⟨w, hw1, hw2⟩ := kern_odd k u
    have ⟨r, hr1, hr2⟩ := pt_tail k u
    have he : k + 1 + 3 = (k + 3) + 1 := by omega
    have he2 : k + 3 + 1 = (k + 4) := by omega
    refine ⟨w + r, ?_, ?_⟩
    · show kern u (k + 1 + 3) = _
      rw [he]
      show kern u (k + 3) + pt u (k + 3 + 1) = _
      rw [he2, hr1, hw1, Nat.mul_add]
    · omega

-- ===========================================================================
-- §6  THE FACTORIAL-TAIL SPLIT
-- ===========================================================================

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

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

theorem sumFact_kern : ∀ (k u : Nat), sumFactFrom u k = fact u * kern u k
  | 0, u => by simp [sumFactFrom, kern]
  | k + 1, u => by
    show sumFactFrom u k + fact (u + k + 1) = fact u * (kern u k + pt u (k + 1))
    rw [sumFact_kern k u, Nat.add_assoc, fact_pt (k + 1) u, Nat.mul_add]

-- ===========================================================================
-- §7  THE 2-ADIC VALUATION
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
  have h2 : (2 * x) % 2 = 0 := by
    rw [Nat.mul_mod]
    simp
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

-- ===========================================================================
-- §8  THE HEADLINE
-- ===========================================================================

/-- **Erdős #404 (left-factorial kernel law)**: for N ≥ u + 3,
`v₂ (Σ_{a=u}^{N} a!) = v₂ (u!) + v₂ (u + 2)`. -/
theorem kernel_law (u k : Nat) (hk : 3 ≤ k) :
    v2 (sumFactFrom u k) = v2 (fact u) + v2 (u + 2) := by
  have ⟨w, hw1, hw2⟩ := kern_odd (k - 3) u
  have hk3 : (k - 3) + 3 = k := by omega
  have hwk : kern u k = (u + 2) * w := by rw [← hk3]; exact hw1
  have hwge : 1 ≤ w := by omega
  have hsf : sumFactFrom u k = fact u * ((u + 2) * w) := by
    rw [sumFact_kern k u, hwk]
  rw [hsf]
  rw [v2_mul (fact u + ((u + 2) * w)) (fact u) ((u + 2) * w) (Nat.le_refl _)
    (fact_pos u) (one_le_mul _ _ (by omega) hwge)]
  rw [v2_mul ((u + 2) + w) (u + 2) w (Nat.le_refl _) (by omega) hwge,
    v2_odd w hw2]
  omega

-- ===========================================================================
-- RECEIPTS
-- ===========================================================================

-- u = 2:  v₂(Σ_{a=2}^{N} a!) = 3 for N = 5, 6, 7.
#eval (List.range 3).map (fun k => v2 (sumFactFrom 2 (k + 3)))
-- expected: [3, 3, 3]

-- u = 6:  v₂ = 7 for N = 9, 10.
#eval (List.range 2).map (fun k => v2 (sumFactFrom 6 (k + 3)))
-- expected: [7, 7]

-- u = 10: v₂ = 10 for N = 13, 14.
#eval (List.range 2).map (fun k => v2 (sumFactFrom 10 (k + 3)))
-- expected: [10, 10]

-- The right-hand sides: v₂(2!) + v₂(4) = 3, v₂(6!) + v₂(8) = 7,
-- v₂(10!) + v₂(12) = 10.
#eval (v2 (fact 2) + v2 4, v2 (fact 6) + v2 8, v2 (fact 10) + v2 12)
-- expected: (3, 7, 10)

#print axioms kernel_law
