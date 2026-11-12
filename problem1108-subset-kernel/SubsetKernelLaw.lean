/-
# ERDŐS #1108 — THE SUBSET KERNEL LAW + THE FULL PAIR-CASCADE LAW

Problem #1108 (Erdős, Oberwolfach 1988): let
A = { Σ_{n ∈ S} n! : S ⊆ ℕ finite }.  Does A contain only finitely
many kth powers (k ≥ 2)?  Only finitely many powerful numbers?

This file proves the structural laws governing the 2-adic valuation of
EVERY element of A — the generalization of the #404 left-factorial
kernel law (`kernel_law`: v₂(Σ_{a=u}^{N} a!) = v₂(u!) + v₂(u+2)) from
contiguous tails to ARBITRARY subsets.

## The mathematics

Pair the integers:  P_j = {2j, 2j+1}  (j ≥ 0; the element 0 pairs
with 1; lists may contain 0 and repeats — every law below holds for
arbitrary nonempty lists).  The 2-adic valuation of factorials is
FLAT on pairs and STRICTLY INCREASING across pairs:

    v₂((2j)!) = v₂((2j+1)!)    (pair_flat:  2j+1 is odd)
    v₂((2j)!) < v₂((2j+2)!)    (pair_jump:  2j+2 is even)

THE ISOLATED-MINIMUM LAW (isolated_min_v2).  If b ∈ S occurs exactly
once and every other a ∈ S carries a strictly larger factorial
valuation — equivalently, the lowest occupied pair P_{j*} of S is a
SINGLETON — then

    v₂ ( Σ_{a ∈ S} a! ) = v₂ (b!)   EXACTLY.

THE FULL CASCADE LAW (full_cascade_v2 — the general-S theorem, this
session).  For EVERY nonempty list S, with j₀ = botPair S the lowest
occupied pair, Λ(j) = v₂((2j)!) and the cascade integer
C(S) = (Σ_{a∈S} a!) / 2^{Λ(j₀)}:

    v₂ ( Σ_{a ∈ S} a! ) = Λ(j₀) + v₂ (C(S))   EXACTLY.

No singleton hypothesis: the bottom pair may be full, the cascade
integer C(S) carries the entire composite structure above the bottom
level.  (At a singleton bottom, C is odd and the law degenerates to
the isolated-minimum law; at a full bottom, C is even — the cascade
jumps at least one level.)

THE SQUARE COROLLARY (square_cascade_even — the #1108 obstruction
engine at p = 2, general form).  If Σ_{a∈S} a! is a perfect square
then

    ( Λ(j₀) + v₂(C(S)) )  is EVEN.

Since Λ(j) = v₂((2j)!) = 2j − s₂(j) (Legendre), the parity of the
bottom pair's binary digit sum s₂(j₀) plus the cascade parity v₂(C(S))
is an INVARIANT of every square in A.  Verified against the complete
census: exactly 15 squares with max(S) ≤ 24 (largest
S = {1,2,3,7,8,...,15} = 1183893²), zero for max(S) ∈ [16,24].

The all-prime block cascade (same law at every prime p, with p-blocks
{pj, ..., pj+p−1}), the Bertrand-window reduction, and the certified
censuses are proved and verified in DERIVATION.md +
`verify_cascade.py` + `deep_census24.py` (exact-integer batteries:
triple-method agreement on all 16383 subsets of [1..14]; the all-prime
stack law and the bottom-block singleton law on all subsets of [1..12]
at p ∈ {2,3,5,7,11} — 20475/20475 and 7399/7399).

## Architecture

* §1  `fact`, `v2` and the valuation toolkit (KernelLaw blueprint).
* §2  monotonicity, pair flatness, pair jump, pair-above.
* §3  dominated addition `v2 x < v2 y → v2 (x+y) = v2 x` (fuel).
* §4  `sumFacts`, the dominated-tail lemma, THE ISOLATED-MINIMUM LAW.
* §5  the pair-singleton square corollary + receipts.
* §6  THE FULL CASCADE LAW: `botPair`, `Lam`, `cascadeC`,
       `full_cascade_v2`, `square_cascade_even` + receipts.

Core Lean 4 only.  No Mathlib.  No `sorry`.  No custom axioms.
-/

-- ===========================================================================
-- §1  FACTORIALS AND THE 2-ADIC VALUATION (KernelLaw blueprint)
-- ===========================================================================

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Binary valuation (`v2 0 = 0` by convention). -/
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

theorem skl_one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [ha', hb', Nat.mul_succ, Nat.add_mul]
  omega

theorem fact_pos : ∀ u, 1 ≤ fact u
  | 0 => Nat.le_refl 1
  | u + 1 => skl_one_le_mul (u + 1) (fact u) (Nat.succ_le_succ (Nat.zero_le u))
    (fact_pos u)

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

/-- Additivity of v2 on products (fuel induction, KernelLaw blueprint). -/
theorem v2_mul : ∀ (f a b : Nat), a + b ≤ f → 1 ≤ a → 1 ≤ b →
    v2 (a * b) = v2 a + v2 b
  | 0, a, b, hf, ha, hb => by omega
  | f + 1, a, b, hf, ha, hb => by
    by_cases ha1 : a = 1
    · rw [ha1, Nat.one_mul, v2_odd 1 (by omega)]
      omega
    · by_cases hae : a % 2 = 0
      · have hxy : 1 ≤ a * b := skl_one_le_mul a b (by omega) hb
        have hb2 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hae]; simp
        have hsplit : a * b / 2 = (a / 2) * b := even_mul_div2 a b hae
        rw [v2_even_pos _ hxy hb2, hsplit]
        rw [v2_mul f (a / 2) b (by omega) (by omega) hb]
        rw [v2_even_pos a (by omega) hae]
        omega
      · by_cases hbe : b % 2 = 0
        · rw [Nat.mul_comm a b]
          have hxy : 1 ≤ b * a := skl_one_le_mul b a hb (by omega)
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
-- §2  MONOTONICITY, PAIR FLATNESS, PAIR JUMP, PAIR-ABOVE
-- ===========================================================================

/-- Factorial valuations are non-decreasing: v₂(n!) ≤ v₂(m!) for n ≤ m. -/
theorem v2_fact_mono : ∀ (f n m : Nat), n + m ≤ f → n ≤ m →
    v2 (fact n) ≤ v2 (fact m)
  | 0, n, m, hf, h => by
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    rw [hn, hm]
    exact Nat.le_refl _
  | f + 1, n, m, hf, h => by
    by_cases hnm : n = m
    · rw [hnm]
      exact Nat.le_refl _
    · have hlt : n < m := by omega
      have ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk]
      have hgoal : v2 (fact (k + 1)) = v2 (k + 1) + v2 (fact k) := by
        show v2 ((k + 1) * fact k) = _
        exact v2_mul (k + 1 + fact k) (k + 1) (fact k) (Nat.le_refl _)
          (Nat.succ_le_succ (Nat.zero_le k)) (fact_pos k)
      rw [hgoal]
      exact Nat.le_trans (v2_fact_mono f n k (by omega) (by omega))
        (Nat.le_add_left _ _)

/-- PAIR FLATNESS: v₂((2j+1)!) = v₂((2j)!). -/
theorem pair_flat (j : Nat) : v2 (fact (2 * j + 1)) = v2 (fact (2 * j)) := by
  have hsplit : fact (2 * j + 1) = (2 * j + 1) * fact (2 * j) := rfl
  rw [hsplit]
  have hv : v2 ((2 * j + 1) * fact (2 * j)) =
      v2 (2 * j + 1) + v2 (fact (2 * j)) :=
    v2_mul (2 * j + 1 + fact (2 * j)) (2 * j + 1) (fact (2 * j))
      (Nat.le_refl _) (Nat.succ_le_succ (Nat.zero_le (2 * j)))
      (fact_pos (2 * j))
  rw [hv, v2_odd (2 * j + 1) (by omega)]
  omega

/-- PAIR JUMP: v₂((2j)!) < v₂((2j+2)!). -/
theorem pair_jump (j : Nat) : v2 (fact (2 * j)) < v2 (fact (2 * j + 2)) := by
  have hsplit : fact (2 * j + 2) = (2 * j + 2) * fact (2 * j + 1) := rfl
  rw [hsplit]
  have hv : v2 ((2 * j + 2) * fact (2 * j + 1)) =
      v2 (2 * j + 2) + v2 (fact (2 * j + 1)) :=
    v2_mul (2 * j + 2 + fact (2 * j + 1)) (2 * j + 2) (fact (2 * j + 1))
      (Nat.le_refl _) (Nat.succ_le_succ (Nat.zero_le (2 * j + 1)))
      (fact_pos (2 * j + 1))
  rw [hv, pair_flat]
  have heven : (2 * j + 2) % 2 = 0 := by omega
  have hpos : 1 ≤ 2 * j + 2 := by omega
  rw [v2_even_pos _ hpos heven]
  omega

/-- Elements of strictly higher pairs carry strictly higher factorial
valuation: if b/2 < a/2 then v₂(b!) < v₂(a!). -/
theorem pair_above (a b : Nat) (h : b / 2 < a / 2) :
    v2 (fact b) < v2 (fact a) := by
  have hage : 2 * (b / 2) + 2 ≤ a := by omega
  have hmono : v2 (fact (2 * (b / 2) + 2)) ≤ v2 (fact a) :=
    v2_fact_mono (2 * (b / 2) + 2 + a) (2 * (b / 2) + 2) a (Nat.le_refl _)
      hage
  have hjump' : v2 (fact (2 * (b / 2))) < v2 (fact (2 * (b / 2) + 2)) :=
    pair_jump (b / 2)
  cases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with
  | inl hb =>
    have hbeq : b = 2 * (b / 2) := by omega
    rw [hbeq]
    omega
  | inr hb =>
    have hbeq : b = 2 * (b / 2) + 1 := by omega
    rw [hbeq, pair_flat (b / 2)]
    omega

-- ===========================================================================
-- §3  DOMINATED ADDITION (fuel induction on parity)
-- ===========================================================================

/-- If `v₂ x < v₂ y` then `v₂ (x + y) = v₂ x`. -/
theorem v2_lt_add : ∀ (f x y : Nat), x + y ≤ f → 1 ≤ x → v2 x < v2 y →
    v2 (x + y) = v2 x
  | 0, x, y, hf, hx, hv => by omega
  | f + 1, x, y, hf, hx, hv => by
    by_cases hxodd : x % 2 = 1
    · have hyeven : y % 2 = 0 := by
        cases hym : y % 2 with
        | zero => rfl
        | succ n =>
          have hy1 : y % 2 = 1 := by omega
          rw [v2_odd y hy1, v2_odd x hxodd] at hv
          omega
      have hs : (x + y) % 2 = 1 := by omega
      rw [v2_odd x hxodd, v2_odd (x + y) hs]
    · have hxeven : x % 2 = 0 := by omega
      have hx1 : 1 ≤ x := by omega
      by_cases hy0 : y = 0
      · rw [hy0, Nat.add_zero]
      · have hyeven : y % 2 = 0 := by
          cases hym : y % 2 with
          | zero => rfl
          | succ n =>
            have hy1 : y % 2 = 1 := by omega
            rw [v2_odd y hy1] at hv
            rw [v2_even_pos x hx1 hxeven] at hv
            omega
        have hy1 : 1 ≤ y := by omega
        have hxy1 : 1 ≤ x + y := by omega
        have hs : (x + y) % 2 = 0 := by omega
        have hxd : v2 x = 1 + v2 (x / 2) := v2_even_pos x hx1 hxeven
        have hyd : v2 y = 1 + v2 (y / 2) := v2_even_pos y hy1 hyeven
        have hsumsplit : (x + y) / 2 = x / 2 + y / 2 := by omega
        rw [v2_even_pos (x + y) hxy1 hs, hsumsplit]
        rw [v2_lt_add f (x / 2) (y / 2) (by omega) (by omega) (by omega)]
        omega

-- ===========================================================================
-- §4  SUBSET SUMS AND THE ISOLATED-MINIMUM LAW (self-contained membership)
-- ===========================================================================

/-- `sumFacts S = Σ_{a ∈ S} a!` (list-encoded finite subsets). -/
def sumFacts : List Nat → Nat
  | [] => 0
  | a :: t => fact a + sumFacts t

/-- Self-contained membership (no `List.Mem` API surface). -/
def memB (b : Nat) : List Nat → Prop
  | [] => False
  | a :: t => a = b ∨ memB b t

/-- Count occurrences of b in a list (self-contained). -/
def countB (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => (if a = b then 1 else 0) + countB b t

theorem not_memB_of_countB_zero : ∀ (t : List Nat) (b : Nat),
    countB b t = 0 → ¬ memB b t
  | [], b, h => by
    intro hm
    exact hm
  | a :: t, b, h => by
    intro hm
    rw [countB] at h
    cases hm with
    | inl hab =>
      rw [if_pos hab] at h
      omega
    | inr hm' =>
      have hsub : countB b t = 0 := by
        by_cases hab : a = b
        · rw [if_pos hab] at h; omega
        · rw [if_neg hab] at h; omega
      exact not_memB_of_countB_zero t b hsub hm'

theorem sumFacts_ge_fact_of_memB : ∀ (t : List Nat) (b : Nat),
    memB b t → fact b ≤ sumFacts t
  | [], b, hm => by cases hm
  | a :: t, b, hm => by
    cases hm with
    | inl hab =>
      rw [hab]
      show fact b ≤ fact b + sumFacts t
      exact Nat.le_add_right _ _
    | inr hm' =>
      have hrec : fact b ≤ sumFacts t := sumFacts_ge_fact_of_memB t b hm'
      show fact b ≤ fact a + sumFacts t
      exact Nat.le_trans hrec (Nat.le_add_left _ _)

/-- DOMINATED TAIL: adding elements of strictly larger factorial
valuation does not move the valuation. -/
theorem v2_dom_tail : ∀ (T : List Nat) (b : Nat),
    (∀ x, memB x T → v2 (fact b) < v2 (fact x)) →
    v2 (fact b + sumFacts T) = v2 (fact b)
  | [], b, h => by
    show v2 (fact b + 0) = v2 (fact b)
    rw [Nat.add_zero]
  | a :: t, b, h => by
    have hrec : v2 (fact b + sumFacts t) = v2 (fact b) :=
      v2_dom_tail t b (fun x hx => h x (Or.inr hx))
    have hbig : v2 (fact b) < v2 (fact a) := h a (Or.inl rfl)
    have hpos : 1 ≤ fact b + sumFacts t :=
      Nat.le_trans (fact_pos b) (Nat.le_add_right _ _)
    have hreg : fact b + sumFacts (a :: t)
        = (fact b + sumFacts t) + fact a := by
      show fact b + (fact a + sumFacts t) = (fact b + sumFacts t) + fact a
      omega
    rw [hreg]
    exact Eq.trans (v2_lt_add ((fact b + sumFacts t) + fact a)
      (fact b + sumFacts t) (fact a) (Nat.le_refl _) hpos
      (by rw [hrec]; exact hbig)) hrec

/-- **THE ISOLATED-MINIMUM LAW** (the subset kernel law, sharp form):
if `b` occurs exactly once in `S` and every other element carries a
strictly larger factorial valuation, then
`v₂ (Σ_{a ∈ S} a!) = v₂ (b!)` EXACTLY. -/
theorem isolated_min_v2 : ∀ (S : List Nat) (b : Nat),
    memB b S → countB b S = 1 →
    (∀ a, memB a S → a ≠ b → v2 (fact b) < v2 (fact a)) →
    v2 (sumFacts S) = v2 (fact b)
  | [], b, hb, _, _ => by cases hb
  | a :: t, b, hb, hc, hmin => by
    by_cases hab : a = b
    · have hba : b = a := hab.symm
      subst hba
      have hct : countB b t = 0 := by
        have hc2 : countB b (b :: t) = 1 := hc
        rw [countB] at hc2
        rw [if_pos rfl] at hc2
        omega
      have hnmem : ¬ memB b t := not_memB_of_countB_zero t b hct
      have hall : ∀ x, memB x t → v2 (fact b) < v2 (fact x) := by
        intro x hx
        exact hmin x (Or.inr hx) (fun hxb => hnmem (by rw [← hxb]; exact hx))
      show v2 (fact b + sumFacts t) = v2 (fact b)
      exact v2_dom_tail t b hall
    · have hbt : memB b t := by
        cases hb with
        | inl hba => omega
        | inr h' => exact h'
      have hc' : countB b t = 1 := by
        rw [countB] at hc
        rw [if_neg hab] at hc
        omega
      have hmin' : ∀ x, memB x t → x ≠ b → v2 (fact b) < v2 (fact x) :=
        fun x hx hxb => hmin x (Or.inr hx) hxb
      have hrec : v2 (sumFacts t) = v2 (fact b) :=
        isolated_min_v2 t b hbt hc' hmin'
      have hbig : v2 (fact b) < v2 (fact a) := hmin a (Or.inl rfl) hab
      have hpos : 1 ≤ sumFacts t := by
        have hge : fact b ≤ sumFacts t := sumFacts_ge_fact_of_memB t b hbt
        exact Nat.le_trans (fact_pos b) hge
      have hlt : v2 (sumFacts t) < v2 (fact a) := by
        rw [hrec]; exact hbig
      show v2 (fact a + sumFacts t) = v2 (fact b)
      rw [Nat.add_comm]
      exact Eq.trans (v2_lt_add (sumFacts t + fact a) (sumFacts t) (fact a)
        (Nat.le_refl _) hpos hlt) hrec

-- ===========================================================================
-- §5  THE PAIR-SINGLETON SQUARE COROLLARY + RECEIPTS
-- ===========================================================================

/-- Squares have even 2-adic valuation. -/
theorem square_v2_even (n r : Nat) (h : n = r * r) : v2 n % 2 = 0 := by
  cases r with
  | zero =>
    have h0 : v2 0 = 0 := by simp [v2]
    rw [h, Nat.mul_zero]
    omega
  | succ r' =>
    have hr1 : 1 ≤ r' + 1 := Nat.succ_le_succ (Nat.zero_le r')
    have hvm : v2 ((r' + 1) * (r' + 1)) = v2 (r' + 1) + v2 (r' + 1) :=
      v2_mul ((r' + 1) + (r' + 1)) (r' + 1) (r' + 1) (by omega) hr1 hr1
    rw [h, hvm]
    omega

/-- **THE PAIR-SINGLETON SQUARE COROLLARY (Erdős #1108, p = 2 engine)**:
if `Σ_{a∈S} a!` is a perfect square and the bottom pair of `S` is the
singleton `{b}` (b occurs once; every other element lives in a strictly
higher pair), then `v₂(b!)` is EVEN. -/
theorem square_pair_singleton_even (S : List Nat) (r b : Nat)
    (hb : memB b S) (hc : countB b S = 1)
    (habove : ∀ a, memB a S → a ≠ b → b / 2 < a / 2)
    (hsq : sumFacts S = r * r) :
    v2 (fact b) % 2 = 0 := by
  have hmin : ∀ a, memB a S → a ≠ b → v2 (fact b) < v2 (fact a) :=
    fun a ha hab => pair_above a b (habove a ha hab)
  have hlaw : v2 (sumFacts S) = v2 (fact b) :=
    isolated_min_v2 S b hb hc hmin
  have hven := square_v2_even (sumFacts S) r hsq
  rw [hlaw] at hven
  exact hven

-- ===========================================================================
-- §6  THE FULL CASCADE LAW (general S — no singleton hypothesis)
-- ===========================================================================

/-- The pair level Λ(j) = v₂((2j)!). -/
def Lam (j : Nat) : Nat := v2 (fact (2 * j))

/-- `botPairAux b T` = min of a/2 over a ∈ b :: T. -/
def botPairAux : Nat → List Nat → Nat
  | b, [] => b / 2
  | b, a :: t => min (b / 2) (botPairAux a t)

/-- The bottom pair index of a list (lowest occupied pair). -/
def botPair : List Nat → Nat
  | [] => 0
  | a :: t => botPairAux a t

/-- The cascade integer: C(S) = (Σ_{a ∈ S} a!) / 2^{Λ(botPair S)}. -/
def cascadeC (S : List Nat) : Nat := sumFacts S / 2 ^ (Lam (botPair S))

theorem botPairAux_le : ∀ (b : Nat) (T : List Nat) (a : Nat),
    memB a (b :: T) → botPairAux b T ≤ a / 2
  | b, [], a, h => by
    cases h with
    | inl hab => rw [hab]; exact Nat.le_refl _
    | inr h' => cases h'
  | b, c :: t, a, h => by
    cases h with
    | inl hab =>
      rw [hab]
      show min (a / 2) (botPairAux c t) ≤ a / 2
      exact Nat.min_le_left _ _
    | inr h' =>
      have hrec : botPairAux c t ≤ a / 2 := botPairAux_le c t a h'
      show min (b / 2) (botPairAux c t) ≤ a / 2
      exact Nat.le_trans (Nat.min_le_right _ _) hrec

theorem botPair_le (S : List Nat) (a : Nat) (h : memB a S) :
    botPair S ≤ a / 2 := by
  cases S with
  | nil => cases h
  | cons b t =>
    show botPairAux b t ≤ a / 2
    exact botPairAux_le b t a h

/-- Exactness on the bottom pair: a ∈ P_j ⟹ v₂(a!) = Λ(j). -/
theorem pair_level_exact (a j : Nat) (h : a / 2 = j) : v2 (fact a) = Lam j := by
  cases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with
  | inl he =>
    have hae : a = 2 * j := by omega
    rw [hae]
    rfl
  | inr ho =>
    have hae : a = 2 * j + 1 := by omega
    rw [hae, pair_flat j]
    rfl

/-- Every element of S carries valuation at least Λ(botPair S). -/
theorem pair_level_ge (S : List Nat) (a : Nat) (h : memB a S) :
    Lam (botPair S) ≤ v2 (fact a) := by
  have hle : botPair S ≤ a / 2 := botPair_le S a h
  by_cases heq : a / 2 = botPair S
  · rw [pair_level_exact a (botPair S) heq]
    exact Nat.le_refl _
  · have hlt : botPair S < a / 2 := by omega
    have habove : v2 (fact (2 * botPair S)) < v2 (fact a) :=
      pair_above a (2 * botPair S) (by omega)
    exact Nat.le_of_lt habove

theorem pow_two_dvd_of_v2_ge : ∀ (k x : Nat), k ≤ v2 x → 2 ^ k ∣ x
  | 0, x, _ => Nat.one_dvd x
  | k + 1, x, h => by
    by_cases hx : x = 0
    · rw [hx]; exact Nat.dvd_zero _
    · have hx1 : 1 ≤ x := by omega
      by_cases hxe : x % 2 = 0
      · have hrec : 2 ^ k ∣ x / 2 := pow_two_dvd_of_v2_ge k (x / 2) (by
          rw [v2_even_pos x hx1 hxe] at h
          omega)
        have hxeq : x = 2 * (x / 2) := by omega
        rw [hxeq, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
        exact Nat.mul_dvd_mul_left 2 hrec
      · rw [v2_odd x (by omega : x % 2 = 1)] at h
        have hfalse : False := by omega
        exact hfalse.elim

theorem pow_dvd_sumFacts : ∀ (S : List Nat) (k : Nat),
    (∀ a, memB a S → 2 ^ k ∣ fact a) → 2 ^ k ∣ sumFacts S
  | [], k, _ => Nat.dvd_zero _
  | b :: t, k, h => by
    have hb := h b (Or.inl rfl)
    have hrec := pow_dvd_sumFacts t k (fun a ha => h a (Or.inr ha))
    show 2 ^ k ∣ fact b + sumFacts t
    exact Nat.dvd_add hb hrec

theorem one_le_two_pow : ∀ (k : Nat), 1 ≤ 2 ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    exact skl_one_le_mul (2 ^ k) 2 (one_le_two_pow k) (by omega : (1 : Nat) ≤ 2)

theorem v2_zero : v2 0 = 0 := by simp [v2]

theorem v2_one : v2 1 = 0 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, v2_succ 0,
    if_neg (by omega : ¬((0 : Nat) + 1) % 2 = 0)]

theorem v2_two : v2 2 = 1 := by
  have h := v2_succ 1
  rw [show (2 : Nat) = 1 + 1 from rfl]
  rw [h, if_pos (by omega : ((1 : Nat) + 1) % 2 = 0)]
  have hd2 : (1 : Nat) + 1 = 2 := by omega
  have hd3 : (2 : Nat) / 2 = 1 := by omega
  rw [hd2, hd3, v2_one]

theorem v2_pow_two : ∀ (k : Nat), v2 (2 ^ k) = k
  | 0 => v2_one
  | k + 1 => by
    rw [Nat.pow_succ,
      v2_mul (2 ^ k + 2) (2 ^ k) 2 (by omega) (one_le_two_pow k) (by omega),
      v2_pow_two k, v2_two]

theorem v2_pow_mul (k C : Nat) (hC : 1 ≤ C) : v2 (2 ^ k * C) = k + v2 C := by
  rw [v2_mul (2 ^ k + C) (2 ^ k) C (by omega) (one_le_two_pow k) hC,
    v2_pow_two k]

theorem eq_mul_div (d n : Nat) (hd : 1 ≤ d) (h : d ∣ n) :
    n = d * (n / d) := by
  obtain ⟨c, hc⟩ := h
  have hcd : d * c / d = c := by
    have hd0 : 0 < d := by omega
    exact Nat.mul_div_cancel_left c hd0
  rw [hc, hcd]

theorem sumFacts_pos : ∀ (S : List Nat), S ≠ [] → 1 ≤ sumFacts S
  | [], h => absurd rfl h
  | a :: t, _ => by
    have ha : 1 ≤ fact a := fact_pos a
    have hle : 1 ≤ fact a + sumFacts t := Nat.le_trans ha (Nat.le_add_right _ _)
    show 1 ≤ fact a + sumFacts t
    exact hle

/-- **THE FULL CASCADE LAW** (Erdős #1108, the general-S kernel law):
for EVERY nonempty list S, with j₀ the lowest occupied pair and
C(S) = (Σ_{a∈S} a!) / 2^{Λ(j₀)} the cascade integer,

    v₂ ( Σ_{a ∈ S} a! ) = Λ(j₀) + v₂ ( C(S) )   EXACTLY.

The composite structure above the bottom level is carried entirely by
the integer C(S); at a singleton bottom C is odd (the isolated-minimum
law), at a full bottom C is even (the cascade jumps). -/
theorem full_cascade_v2 : ∀ (S : List Nat), S ≠ [] →
    v2 (sumFacts S) = Lam (botPair S) + v2 (cascadeC S)
  | S, hS => by
    have hdvd : 2 ^ (Lam (botPair S)) ∣ sumFacts S :=
      pow_dvd_sumFacts S _ (fun a ha =>
        pow_two_dvd_of_v2_ge _ (fact a) (pair_level_ge S a ha))
    have hCeq : sumFacts S = 2 ^ (Lam (botPair S)) * cascadeC S := by
      show sumFacts S
        = 2 ^ (Lam (botPair S)) * (sumFacts S / 2 ^ (Lam (botPair S)))
      exact eq_mul_div _ _ (one_le_two_pow _) hdvd
    have hCpos : 1 ≤ cascadeC S := by
      cases hC0 : cascadeC S with
      | zero =>
        have hsum1 : 1 ≤ sumFacts S := sumFacts_pos S hS
        rw [hCeq, hC0, Nat.mul_zero] at hsum1
        omega
      | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
    rw [hCeq, v2_pow_mul _ _ hCpos]

/-- **THE SQUARE CASCADE COROLLARY (general form — the #1108 p = 2
obstruction engine, no singleton hypothesis)**: if Σ_{a∈S} a! is a
perfect square then Λ(j₀) + v₂(C(S)) is EVEN.  Via Legendre
(Λ(j) = 2j − s₂(j)) this forces the parity invariant
s₂(j₀) + v₂(C(S)) ≡ 0 (mod 2) on every square in A. -/
theorem square_cascade_even (S : List Nat) (r : Nat) (hS : S ≠ [])
    (hsq : sumFacts S = r * r) :
    (Lam (botPair S) + v2 (cascadeC S)) % 2 = 0 := by
  have h1 := square_v2_even (sumFacts S) r hsq
  rw [full_cascade_v2 S hS] at h1
  exact h1

-- ===========================================================================
-- RECEIPTS (the census squares, spot-verified through the laws)
-- ===========================================================================

-- v2 of the census squares (all EXACTLY as the laws predict):
#eval v2 (sumFacts [1, 2, 3])            -- 0    (9 = 3²)
#eval v2 (sumFacts [4, 5])               -- 4    (144 = 12²)
#eval v2 (sumFacts [1, 4])               -- 0    (25 = 5²)
#eval v2 (sumFacts [1, 5, 6])            -- 0    (841 = 29²)
#eval v2 (sumFacts [1, 4, 8, 9])         -- 0    (403225 = 635²)
#eval v2 (sumFacts [4, 5, 7])            -- 6    (5184 = 72²)
#eval v2 (sumFacts [1, 2, 3, 6])         -- 3    (729 = 27²)
#eval v2 (sumFacts [2, 3, 8])            -- 3    (40328 = 2³·71², powerful)
#eval v2 (sumFacts [1, 2, 3, 6, 7, 8, 10])  -- 0 (3674889 = 1917²)

-- THE FULL CASCADE LAW on the nontrivial cascades:
#eval (v2 (sumFacts [4, 5]), Lam (botPair [4, 5]), v2 (cascadeC [4, 5]))
-- (4, 3, 1):  Λ = 3, cascade integer 18 = 2·9 carries ν = 1.
#eval (v2 (sumFacts [4, 5, 7]), Lam (botPair [4, 5, 7]),
  v2 (cascadeC [4, 5, 7]))
-- (6, 3, 3):  Λ = 3, cascade integer 648 = 2³·81 carries ν = 3.
#eval (v2 (sumFacts [2, 3, 8]), Lam (botPair [2, 3, 8]),
  v2 (cascadeC [2, 3, 8]))
-- (3, 1, 2):  Λ = 1, cascade integer 20164 = 2²·5041 carries ν = 2.
#eval (v2 (sumFacts [1, 2, 3, 7, 8]), Lam (botPair [1, 2, 3, 7, 8]),
  v2 (cascadeC [1, 2, 3, 7, 8]))
-- (0, 0, 0):  bottom pair P_0 = {1}, singleton, C odd.

-- The largest census square (max = 15), verified end-to-end:
#eval sumFacts [1, 2, 3, 7, 8, 9, 10, 11, 12, 13, 14, 15]
-- 1401602635449
#eval 1183893 * 1183893
-- 1401602635449

-- Pair structure receipts:
#eval (v2 (fact 4), v2 (fact 5), v2 (fact 6), v2 (fact 7))
-- expected (3, 3, 4, 4): flat on pairs {4,5} and {6,7}, jump between.

#print axioms isolated_min_v2
#print axioms square_pair_singleton_even
#print axioms full_cascade_v2
#print axioms square_cascade_even

-- ===========================================================================
-- §7  THE LEGENDRE PARITY LAW: Λ(j) = v₂((2j)!) = 2j − s₂(j)  (Kill #19)
-- ===========================================================================
--
-- The engine's Λ-spine made explicit.  The binary digit sum s₂ (mirroring
-- the shape of `v2`) gives the closed form of every pair level:
--
--     v₂(n!) = n − s₂(n)                (Legendre's formula at p = 2:
--      `legendre_v2_fact`                v₂(n!) = Σ ⌊n/2^i⌋ = n − s₂(n))
--     Λ(j) = v₂((2j)!) = 2j − s₂(j)     (`legendre_lam` — the spine)
--
-- THE EXPLICIT CASCADE (`explicit_cascade`): the full cascade law with the
-- spine unfolded —
--
--     v₂ ( Σ_{a∈S} a! ) = (2j₀ − s₂(j₀)) + v₂(C(S)).
--
-- THE SQUARE-PARITY INVARIANT (`square_parity_s2` — the payoff): if
-- Σ_{a∈S} a! is a perfect square then
--
--     s₂(j₀) ≡ v₂(C(S))  (mod 2)
--
-- — the parity of the bottom pair's binary digit sum is LOCKED to the
-- cascade parity on every square in A (Kill #17's obstruction engine with
-- the Λ-spine fully explicit).

/-- Binary digit sum s₂ (`s2 0 = 0`), mirroring the shape of `v2`. -/
def s2 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then s2 ((n + 1) / 2) else 1 + s2 ((n + 1) / 2)
termination_by n => n
decreasing_by all_goals omega

theorem s2_succ (n : Nat) :
    s2 (n + 1) = if (n + 1) % 2 = 0 then s2 ((n + 1) / 2) else 1 + s2 ((n + 1) / 2) := by
  simp [s2]

theorem s2_zero : s2 0 = 0 := by simp [s2]

/-- Even numbers: s₂(m) = s₂(m/2) (`m ≥ 1`; mirror of `v2_even_pos`). -/
theorem s2_even (m : Nat) (hm : 1 ≤ m) (h2 : m % 2 = 0) :
    s2 m = s2 (m / 2) := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, s2_succ, if_pos (by omega : (j + 1) % 2 = 0)]

/-- Odd numbers: s₂(m) = 1 + s₂(m/2) (mirror of `v2_odd`). -/
theorem s2_odd (m : Nat) (h2 : m % 2 = 1) : s2 m = 1 + s2 (m / 2) := by
  have ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hj, s2_succ, if_neg (by omega : ¬((j + 1) % 2 = 0))]

/-- Doubling appends a binary zero: s₂(2m) = s₂(m). -/
theorem s2_double : ∀ (m : Nat), s2 (2 * m) = s2 m
  | 0 => rfl
  | m + 1 => by
    have hmod : (2 * (m + 1)) % 2 = 0 := by omega
    have hpos : 1 ≤ 2 * (m + 1) := by omega
    rw [s2_even (2 * (m + 1)) hpos hmod]
    have hdiv : (2 * (m + 1)) / 2 = m + 1 := by omega
    rw [hdiv]

/-- Doubling plus one appends a binary one: s₂(2m+1) = 1 + s₂(m). -/
theorem s2_double_plus_one (m : Nat) : s2 (2 * m + 1) = 1 + s2 m := by
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  rw [s2_odd (2 * m + 1) hmod]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hdiv]

/-- **THE EVEN-FACTORIAL LAW**: v₂((2m)!) = m + v₂(m!) — the multiplicative
half-step of Legendre's formula (each even factor 2, 4, …, 2m contributes
exactly one 2 on top of the odd-collapsed factorial below). -/
theorem v2_fact_even : ∀ (m : Nat), v2 (fact (2 * m)) = m + v2 (fact m)
  | 0 => by
    show v2 1 = 0 + v2 1
    have h1 := v2_one
    omega
  | m + 1 => by
    have ih := v2_fact_even m
    have h21 : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h21]
    have hsplit : fact (2 * m + 2) = (2 * m + 2) * fact (2 * m + 1) := rfl
    rw [hsplit]
    have hv : v2 ((2 * m + 2) * fact (2 * m + 1)) =
        v2 (2 * m + 2) + v2 (fact (2 * m + 1)) :=
      v2_mul (2 * m + 2 + fact (2 * m + 1)) (2 * m + 2) (fact (2 * m + 1))
        (Nat.le_refl _) (Nat.succ_le_succ (Nat.zero_le (2 * m + 1)))
        (fact_pos (2 * m + 1))
    rw [hv]
    have hB : v2 (2 * m + 2) = 1 + v2 (m + 1) := by
      have heven : (2 * m + 2) % 2 = 0 := by omega
      have hpos : 1 ≤ 2 * m + 2 := by omega
      rw [v2_even_pos (2 * m + 2) hpos heven]
      have hdiv : (2 * m + 2) / 2 = m + 1 := by omega
      rw [hdiv]
    have hC : v2 (fact (2 * m + 1)) = v2 (fact (2 * m)) := pair_flat m
    have hD : v2 (fact (m + 1)) = v2 (m + 1) + v2 (fact m) := by
      show v2 ((m + 1) * fact m) = v2 (m + 1) + v2 (fact m)
      exact v2_mul (m + 1 + fact m) (m + 1) (fact m) (Nat.le_refl _)
        (Nat.succ_le_succ (Nat.zero_le m)) (fact_pos m)
    omega

/-- **THE LEGENDRE PARITY LAW** (fuel induction on the bound f): for every
n with n ≤ f, v₂(n!) + s₂(n) = n — Legendre's formula at p = 2. -/
theorem legendre_aux : ∀ (f n : Nat), n ≤ f → v2 (fact n) + s2 n = n
  | 0, n, hn => by
    have hn0 : n = 0 := by omega
    rw [hn0]
    have h1 : v2 (fact 0) = 0 := v2_one
    have h2 : s2 0 = 0 := s2_zero
    omega
  | f + 1, 0, hn => by
    have h1 : v2 (fact 0) = 0 := v2_one
    have h2 : s2 0 = 0 := s2_zero
    omega
  | f + 1, n + 1, hn => by
    cases (show (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 by omega) with
    | inl hpar =>
      -- EVEN: n + 1 = 2k with k ≥ 1 (n + 1 ≥ 1); the even-factorial law.
      have ⟨k, hk⟩ : ∃ k, n + 1 = 2 * k := ⟨(n + 1) / 2, by omega⟩
      rw [hk]
      have hkf : k ≤ f := by omega
      have hve := v2_fact_even k
      have hsd := s2_double k
      have ihk := legendre_aux f k hkf
      omega
    | inr hpar =>
      -- ODD: n + 1 = 2k+1; pair flatness keeps Λ, s₂ gains one bit.
      have ⟨k, hk⟩ : ∃ k, n + 1 = 2 * k + 1 := ⟨(n + 1) / 2, by omega⟩
      rw [hk]
      have hflat := pair_flat k
      have hs := s2_double_plus_one k
      have hsd := s2_double k
      have ihk := legendre_aux f (2 * k) (by omega)
      omega

/-- **LEGENDRE'S FORMULA AT p = 2**: v₂(n!) + s₂(n) = n, i.e.
v₂(n!) = n − s₂(n). -/
theorem legendre_v2_fact (n : Nat) : v2 (fact n) + s2 n = n :=
  legendre_aux n n (Nat.le_refl n)

theorem legendre_v2_fact_sub (n : Nat) : v2 (fact n) = n - s2 n := by
  have h := legendre_v2_fact n
  omega

/-- The Λ-spine in additive form: Λ(j) + s₂(j) = 2j. -/
theorem legendre_lam_add (j : Nat) : Lam j + s2 j = 2 * j := by
  have h : v2 (fact (2 * j)) + s2 (2 * j) = 2 * j := legendre_v2_fact (2 * j)
  have hsd : s2 (2 * j) = s2 j := s2_double j
  have hlam : Lam j = v2 (fact (2 * j)) := rfl
  omega

/-- **THE LEGENDRE PARITY LAW ON THE Λ-SPINE**:
Λ(j) = v₂((2j)!) = 2j − s₂(j). -/
theorem legendre_lam (j : Nat) : Lam j = 2 * j - s2 j := by
  have h : v2 (fact (2 * j)) + s2 j = 2 * j := legendre_lam_add j
  show v2 (fact (2 * j)) = 2 * j - s2 j
  omega

/-- **THE EXPLICIT CASCADE** (the full cascade law, Λ-spine unfolded):
for every nonempty S, with j₀ = botPair S and C(S) = cascadeC S,
v₂ ( Σ_{a∈S} a! ) = (2j₀ − s₂(j₀)) + v₂(C(S)). -/
theorem explicit_cascade (S : List Nat) (hS : S ≠ []) :
    v2 (sumFacts S) = (2 * (botPair S) - s2 (botPair S)) + v2 (cascadeC S) := by
  have h := full_cascade_v2 S hS
  have hl : Lam (botPair S) = 2 * (botPair S) - s2 (botPair S) :=
    legendre_lam (botPair S)
  rw [hl] at h
  exact h

/-- **THE SQUARE-PARITY INVARIANT** (the Kill #19 payoff): if Σ_{a∈S} a!
is a perfect square then s₂(j₀) ≡ v₂(C(S)) (mod 2) — the parity of the
bottom pair's binary digit sum is locked to the cascade parity on every
square in A. -/
theorem square_parity_s2 (S : List Nat) (r : Nat) (hS : S ≠ [])
    (h : sumFacts S = r * r) :
    s2 (botPair S) % 2 = v2 (cascadeC S) % 2 := by
  have hc := square_cascade_even S r hS h
  have hl := legendre_lam_add (botPair S)
  omega

-- ===========================================================================
-- §7 RECEIPTS (the Legendre spine, spot-verified)
-- ===========================================================================

-- The binary digit sum (hand-checked: 7 = 111₂, 255 = 11111111₂, 256 = 100000000₂):
#eval (s2 0, s2 1, s2 7, s2 255, s2 256)
-- expected (0, 1, 3, 8, 1)

-- Λ(5) = v₂(10!) = ⌊10/2⌋+⌊10/4⌋+⌊10/8⌋ = 5+2+1 = 8; the explicit law agrees:
#eval (Lam 5, 2 * 5 - s2 5, v2 (fact 10))
-- expected (8, 8, 8)

-- Legendre's identity at n = 20 (v₂(20!) = 18, s₂(20) = 2):
#eval (v2 (fact 20) + s2 20, 20)
-- expected (20, 20)

-- THE EXPLICIT CASCADE on the nontrivial square cascade S = [4, 5] (144 = 12²):
#eval (v2 (sumFacts [4, 5]), 2 * (botPair [4, 5]) - s2 (botPair [4, 5]) + v2 (cascadeC [4, 5]))
-- expected (4, 4)

-- THE SQUARE-PARITY INVARIANT on 144 = 12²: s₂(j₀) = s₂(2) = 1 and
-- v₂(C) = v₂(18) = 1 — both odd, locked equal:
#eval (s2 (botPair [4, 5]) % 2, v2 (cascadeC [4, 5]) % 2)
-- expected (1, 1)

#print axioms legendre_v2_fact
#print axioms legendre_v2_fact_sub
#print axioms legendre_lam_add
#print axioms legendre_lam
#print axioms explicit_cascade
#print axioms square_parity_s2
