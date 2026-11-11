import Init
/-
# ERDŐS #261 — THE AP RATIONALITY ENGINE (the Q3 bridge's kernel), CORE-ONLY

THE PROBLEM (verbatim, erdosproblems.com/261, as recorded in the campaign's
problem261-* PROBLEM.md files — the NEW RULE verbatim statement):

    Are there infinitely many n such that there exists some t ≥ 2 and
    distinct integers a_1, …, a_t ≥ 1 such that

        n / 2^n  =  Σ_{k=1}^{t} a_k / 2^{a_k} ?

    Is this true for all n?  Is there a rational x such that

        x  =  Σ_{k=1}^{∞} a_k / 2^{a_k}

    has at least 2^{ℵ₀} solutions?

Sub-question status on this campaign: sub-Q1 KILLED (Borwein–Loring family,
formalized as `bl_family` in problem261-q3bridge/BlockIdentity.lean, CI-green);
the weakened [Er88c] two-solution question KILLED (x = 1/2, three
representations, zero axioms, bulldoze/problem261-two-solutions/TwoSolutions.lean);
the REAL-x continuum question KILLED (THE TOWER,
bulldoze/problem261-continuum-tower/Erdos261Tower.lean, [propext, Quot.sound]);
sub-Q2 (all n) and sub-Q3 (rational x) remain the open cores.

## THIS KERNEL — the one cited-but-unformalized engine of the Q3 BRIDGE

The rational-x bridge (problem261-q3bridge/DERIVATION.tex, Theorem `bridge`)
reduces sub-Q3 to the bounded-room variant of sub-Q2.  Its rationality half
rests on the arithmetic-progression sum lemma:

    Σ_{k ≥ 0} (r + kT)/2^{r+kT}  =  2^{-r}·[ r/(1−q) + T·q/(1−q)² ],   q = 2^{-T}

— a RATIONAL number ("the finite engine … is the kernel identity
`jpow_sum_eq` + `pow_sum_eq`; the infinite form follows by dividing by 2^K and
taking K → ∞" — DERIVATION.tex, Lemma `ap`).  That finite engine — verified
exact by the batteries (verify_complete_proof.py V5: the pairs (1,1), (9,24),
(5,12), K ≤ 29) and by Theorem 1 of the periodic-tower analysis
(bulldoze/problem261-rational-x) — was NOT formalized until this file:

    **THE AP KERNEL IDENTITY (this kernel's headline, `ap_sum_kernel`):**
    for ALL r, T, K ∈ Nat:

        Σ_{k=0}^{K} (r + kT)·2^{K−k}  =  r·(2^{K+1} − 1) + T·(2^{K+1} − K − 2).

    Dividing by 2^K (every exponent K−k ≥ 0) is the closed form of the partial
    value Σ_{k=0}^{K} (r + kT)/2^k = 2r + 2T − (r + T·(K+2))/2^K, whose limit
    K → ∞ is the rational 2r + 2T.  Degenerate points: (r, T) = (0, 1) IS
    `jpow_sum_eq`; T = 0 IS the r-scaled `pow_sum_eq` — the two CI-green
    engines of Kill #8 are two points of this one law.

## DISCIPLINE (the campaign's Lean law)

Core Lean 4 only (import Init; no Mathlib); zero sorry; no custom axioms
(expected gates: at most [propext, Classical.choice, Quot.sound]); fuel-free
structural definitions; NO OOM surface (general induction proofs + tiny #eval
receipts — no boundedForall, no decide over ranges > 501, no tactic bombs);
statement-first comments; no Arsenal import (the vendored arsenal is
ternary-digit/carry machinery — not applicable to this dyadic kernel; the
#261 kernels 3/4/6/8 of kills.yml carry none either).

## §-MAP

* §1  the two sum engines (jpow_sum, pow_sum + their identities — the
       CI-green Kill #8 proofs, verbatim copies)
* §2  the AP engine apSum + the split theorem apSum_split
* §3  THE HEADLINE: ap_sum_kernel (the AP rationality engine)
* §4  receipts (#eval, exact) + axiom gates
-/

-- ===========================================================================
-- §1  THE TWO SUM ENGINES  (verbatim from problem261-q3bridge/BlockIdentity.lean,
--      CI-green: kills.yml "Kernel 6 - Erdos 261 Q3 bridge")
-- ===========================================================================

/-- `jpow_sum m = Σ_{j=1}^{m} j · 2^{m-j}` (recursion: double and add m). -/
def jpow_sum : Nat → Nat
  | 0 => 0
  | m + 1 => 2 * jpow_sum m + (m + 1)

/-- `pow_sum m = Σ_{j=1}^{m} 2^{m-j}` (recursion: double and add 1). -/
def pow_sum : Nat → Nat
  | 0 => 0
  | m + 1 => 2 * pow_sum m + 1

theorem one_le_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  induction a with
  | zero => omega
  | succ a' =>
    have hsm : (a' + 1) * b = a' * b + b := Nat.succ_mul a' b
    omega

theorem one_le_two_pow : ∀ (k : Nat), 1 ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
    rw [Nat.pow_succ]
    exact one_le_mul (2 ^ k) 2 (one_le_two_pow k) (by decide)

/-- **The geometric engine.** `Σ_{j=1}^{m} 2^{m-j} = 2^m − 1`. -/
theorem pow_sum_eq (m : Nat) : pow_sum m = 2 ^ m - 1 := by
  induction m with
  | zero => simp [pow_sum]
  | succ m ih =>
    show 2 * pow_sum m + 1 = 2 ^ (m + 1) - 1
    rw [ih, Nat.pow_succ]
    have key : ∀ t : Nat, 1 ≤ t → 2 * (t - 1) + 1 = t * 2 - 1 := by
      intro t ht; omega
    exact key (2 ^ m) (one_le_two_pow m)

theorem two_pow_big : ∀ (k : Nat), k + 2 ≤ 2 ^ (k + 1)
  | 0 => by decide
  | k + 1 => by
    have ih := two_pow_big k
    have h1 : 1 ≤ 2 ^ (k + 1) := one_le_two_pow (k + 1)
    have hrel : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := Nat.pow_succ 2 (k + 1)
    have key : ∀ a : Nat, 1 ≤ a → k + 2 ≤ a → k + 3 ≤ a * 2 := by
      intro a ha hk; omega
    rw [hrel]
    exact key (2 ^ (k + 1)) h1 ih

/-- **The kernel identity.** `Σ_{j=1}^{m} j·2^{m−j} = 2^{m+1} − m − 2`. -/
theorem jpow_sum_eq (m : Nat) : jpow_sum m = 2 ^ (m + 1) - m - 2 := by
  induction m with
  | zero => simp [jpow_sum]
  | succ m ih =>
    show 2 * jpow_sum m + (m + 1) = 2 ^ (m + 2) - (m + 1) - 2
    have hbig : m + 2 ≤ 2 ^ (m + 1) := two_pow_big m
    have hrel : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := Nat.pow_succ 2 (m + 1)
    rw [ih, hrel]
    have key : ∀ t : Nat, m + 2 ≤ t →
        2 * (t - m - 2) + (m + 1) = t * 2 - (m + 1) - 2 := by
      intro t ht; omega
    exact key (2 ^ (m + 1)) hbig

-- ===========================================================================
-- §2  THE AP ENGINE  (Σ_{k=0}^{K} (r + kT)·2^{K−k}, fuel-free structural)
-- ===========================================================================

/-- `apSum r T K = Σ_{k=0}^{K} (r + k·T) · 2^{K−k}` — the scaled partial sum
of the arithmetic-progression summands (recursion: double the previous partial
and add the next AP term r + (K+1)·T at scale 2^0). -/
def apSum (r T : Nat) : Nat → Nat
  | 0 => r
  | K + 1 => 2 * apSum r T K + (r + (K + 1) * T)

/-- **The AP split.** The AP partial sum splits into its constant part and its
slope part:  Σ_{k=0}^{K} (r+kT)·2^{K−k} = r·(Σ_{k=0}^{K} 2^{K−k}) +
T·(Σ_{k=0}^{K} k·2^{K−k}) = r·pow_sum (K+1) + T·jpow_sum K. -/
theorem apSum_split (r T : Nat) : ∀ (K : Nat),
    apSum r T K = r * pow_sum (K + 1) + T * jpow_sum K
  | 0 => by simp [apSum, pow_sum, jpow_sum]
  | K + 1 => by
    have ih := apSum_split r T K
    show 2 * apSum r T K + (r + (K + 1) * T)
        = r * (2 * pow_sum (K + 1) + 1) + T * (2 * jpow_sum K + (K + 1))
    rw [ih,
        Nat.mul_add 2 (r * pow_sum (K + 1)) (T * jpow_sum K),
        Nat.mul_add r (2 * pow_sum (K + 1)) 1, Nat.mul_one r,
        Nat.mul_add T (2 * jpow_sum K) (K + 1),
        Nat.mul_left_comm r 2 (pow_sum (K + 1)),
        Nat.mul_left_comm T 2 (jpow_sum K),
        Nat.mul_comm T (K + 1)]
    omega

-- ===========================================================================
-- §3  THE HEADLINE — THE AP RATIONALITY ENGINE
-- ===========================================================================

/-- **THE AP KERNEL IDENTITY (the Q3 bridge's rationality engine).**
For ALL r, T, K ∈ Nat:

    Σ_{k=0}^{K} (r + kT)·2^{K−k}  =  r·(2^{K+1} − 1) + T·(2^{K+1} − K − 2).

Dividing by 2^K (every exponent K−k ≥ 0) is the closed form of the partial
value of the arithmetic-progression summands; the K → ∞ limit is the RATIONAL
2r + 2T.  This is the finite engine cited by the Q3 bridge (DERIVATION.tex,
Lemma `ap` — "the kernel identity jpow_sum_eq + pow_sum_eq") and Theorem 1 of
the periodic-tower analysis (the ONLY clean rationality source for gadget
towers, by the Fatou dichotomy).  Degenerate points: (r,T) = (0,1) is
`jpow_sum_eq`; T = 0 is the r-scaled `pow_sum_eq`. -/
theorem ap_sum_kernel (r T K : Nat) :
    apSum r T K = r * (2 ^ (K + 1) - 1) + T * (2 ^ (K + 1) - K - 2) := by
  have hs := apSum_split r T K
  rw [hs, pow_sum_eq, jpow_sum_eq]

-- ===========================================================================
-- §4  RECEIPTS (compiler-evaluated, exact) + AXIOM GATES
-- ===========================================================================

-- The T = 1, r = 1 partial:  Σ_{k=0}^{5}(1+k)·2^{5−k} = 32+32+24+16+10+6 = 120
--   = 1·(2^6 − 1) + 1·(2^6 − 5 − 2) = 63 + 57.
#eval (apSum 1 1 5, 1 * (2 ^ 6 - 1) + 1 * (2 ^ 6 - 5 - 2))          -- (120, 120)

-- The campaign's AP anchor (r, T) = (9, 24) at K = 3 (the periodic-tower /
-- bridge receipt pair; Σ = 9·8 + 33·4 + 57·2 + 81·1 = 399 = 9·15 + 24·11):
#eval (apSum 9 24 3, 9 * (2 ^ 4 - 1) + 24 * (2 ^ 4 - 3 - 2))        -- (399, 399)

-- (r, T) = (5, 12) at K = 7:  Σ_{k=0}^{7}(5+12k)·2^{7−k} = 4239
--   = 5·(2^8 − 1) + 12·(2^8 − 7 − 2) = 1275 + 2964.
#eval (apSum 5 12 7, 5 * (2 ^ 8 - 1) + 12 * (2 ^ 8 - 7 - 2))        -- (4239, 4239)

-- Degenerate point T = 0 (the r-scaled geometric engine):
--   Σ_{k=0}^{4} 7·2^{4−k} = 7·31 = 217 = 7·(2^5 − 1).
#eval (apSum 7 0 4, 7 * (2 ^ 5 - 1) + 0 * (2 ^ 5 - 4 - 2))          -- (217, 217)

-- Degenerate point (r, T) = (0, 1) — IS jpow_sum (Σ k·2^{6−k} = 120 = 2^7−6−2):
#eval (apSum 0 1 6, 0 * (2 ^ 7 - 1) + 1 * (2 ^ 7 - 6 - 2))          -- (120, 120)

-- The rational partial-value mirror of DERIVATION.tex Lemma `ap`'s engine:
--   Σ_{k=0}^{5}(1+k)/2^k = (apSum 1 1 5)/2^5 = 120/32 = 15/4 (exact Rat).
#eval ((Nat.cast (apSum 1 1 5) : Rat) / (Nat.cast 32 : Rat))         -- 15/4

#eval "AP261_KERNEL_GREEN"
#print axioms ap_sum_kernel
#print axioms apSum_split
#print axioms jpow_sum_eq
#print axioms pow_sum_eq
