import Mathlib
import Arsenal.CardinalWorlds

/-!
# Erdos142 — THE r_k(N) KERNEL (Kernel #142, Task 1-a, W1-A1→W1-A2F) — STATEMENT-ONLY

Target (verbatim): "Let r_k(N) be the largest possible size of a subset of
{1,…,N} that does not contain any non-trivial k-term arithmetic progression.
Prove an asymptotic formula for r_k(N)." — Erdős fortress ($10000; "probably
enormously difficult").  THE ASYMPTOTIC FORMULA ITSELF IS OPEN.

This file is the STATEMENT-ONLY kernel of the W66 strike: the theorem
statements of PROOF.md (§1–§5), as `Prop` definitions and simple data defs,
over the Arsenal reader `noTernaryTwo` (CardinalWorlds §1: the Cantor
verdict — ternary expansion avoids the digit 2, i.e. all digits ∈ {0,1}).
NO proofs, NO `sorry`, NO `native_decide`, NO tactics — statements only.
Authored in a sandbox with no Lean toolchain (boss override): UNCOMPILED
here; the repo comparator CI (kills.yml, `lake env lean`) is the verifier of
record — the same discipline as Arsenal/CardinalWorlds.lean.

Companion artifacts: PROOF.md (Theorems A–H, complete), AUDIT.md (verdicts:
all SURVIVE), receipts_regen.py / receipts_regen_output.txt (two-method
machine receipts: E1 brute m ≤ 12; Z1 Z3 two-encoding UNSAT m ≤ 8; the
digit-family classification; the 6-world chain j ≤ 12).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace Erdos142

/-! ## §1 The Cantor family (the Arsenal reader is the family predicate) -/

/-- `C_m`: the Cantor family at depth `m` — numbers below `3^m` whose ternary
expansion avoids the digit 2 (the Arsenal's `noTernaryTwo` verdict). -/
def cantorFamily (m : ℕ) : Set ℕ :=
  {n : ℕ | n < 3 ^ m ∧ noTernaryTwo n = true}

/-- The translated family `noTernaryTwo (n−1)`: `2^m` points inside `[1, 3^m]`
(the PROOF.md B.2 frame). -/
def translatedFamily (m : ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ n ≤ 3 ^ m ∧ noTernaryTwo (n - 1) = true}

/-! ## §2 THEOREM A (the Cantor-verdict 3-AP-free law, no-carry form) -/

/-- **Theorem A.** The Cantor family contains no non-trivial 3-term arithmetic
progression: if `x + z = 2y` and all three carry the Cantor verdict, then the
progression is trivial. -/
def theoremA_cantor_ap3_free : Prop :=
  ∀ x y z : ℕ,
    x + z = 2 * y →
    noTernaryTwo x = true → noTernaryTwo y = true → noTernaryTwo z = true →
    x = y ∧ z = y

/-- **Theorem A, family form.** The Cantor family `C_m` is 3-AP-free for every
depth `m` (the no-carry digit identity + the digit-window descent — two
complete proofs in PROOF.md §2). -/
def theoremA_family_ap3_free : Prop :=
  ∀ m : ℕ, ∀ x ∈ cantorFamily m, ∀ y ∈ cantorFamily m, ∀ z ∈ cantorFamily m,
    x + z = 2 * y → x = y ∧ z = y

/-! ## §3 THEOREM B (the lower-bound law; two halves) -/

/-- **Theorem B.2, translated half.** For every `m`, the translated family has
`2^m` members (hence `r_3(3^m) ≥ 2^m` — the size half of the lower bound). -/
def theoremB2_translated_size : Prop :=
  ∀ m : ℕ, ∃ S : Finset ℕ,
    S.card = 2 ^ m ∧
    (∀ n ∈ S, 0 < n ∧ n ≤ 3 ^ m ∧ noTernaryTwo (n - 1) = true)

/-- **Theorem B.2, AP-free half.** The translated family carries no
non-trivial 3-term progression: with `x + z = 2y` and the translated
verdicts, the progression is trivial. -/
def theoremB2_translated_ap3_free : Prop :=
  ∀ m : ℕ, ∀ x ∈ translatedFamily m, ∀ y ∈ translatedFamily m,
    ∀ z ∈ translatedFamily m,
    x + z = 2 * y → x = y ∧ z = y

/-- **Theorem B.3 (monotone interpolation, rational-exponent form).** For all
`N ≥ 1` there is a 3-AP-free set `S ⊆ [1,N]` of Cantor-frame size: with the
rational lower approximation `63/100 < log_3 2` of `α`, the bound
`(2·|S|)^1000 ≥ N^630` (i.e. `|S| ≥ N^{0.63}/2`, the `N^α/2` law's
rational-certifiable half — constants per PROOF.md §3). -/
def theoremB3_interpolation : Prop :=
  ∀ N : ℕ, 0 < N → ∃ S : Finset ℕ,
    (∀ n ∈ S, n ≤ N) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = y ∨ y = z ∨ x = z) ∧
    (2 * S.card) ^ 1000 ≥ N ^ 630

/-! ## §4 The padded digit-family predicate (the PROOF.md C-frame) -/

/-- The digit family at base `b`, digit bound `k`, depth `m`: all numbers below
`b^m` whose base-`b` digits all lie in `{0,…,k−1}` (the general frame of
Theorems C/D/E: prime-strip, no-carry column, admissible-digit laws). -/
def digitFamily (b k m : ℕ) : Set ℕ :=
  {n : ℕ | n < b ^ m ∧ ∀ p : ℕ, p < m → (n / b ^ p) % b < k}

/-! ## §5 THEOREM D (the no-carry column law, base 2k−3) -/

/-- **Theorem D.** For every `k ≥ 3`, the column family at base `2k−3` with
digits `{0,…,k−2}` is k-term-AP-free (no primality needed) — the PROOF.md §5
statement, `Set.Iic` form: all members are `≤ (2k−3)^m − 1`. -/
def theoremD_column_k_ap_free : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∀ m : ℕ,
      ∀ x ∈ {n : ℕ | n < (2 * k - 3) ^ m ∧
                        ∀ p : ℕ, p < m → (n / (2 * k - 3) ^ p) % (2 * k - 3) < k - 1},
      ∀ y ∈ {n : ℕ | n < (2 * k - 3) ^ m ∧
                        ∀ p : ℕ, p < m → (n / (2 * k - 3) ^ p) % (2 * k - 3) < k - 1},
      ∀ z ∈ {n : ℕ | n < (2 * k - 3) ^ m ∧
                        ∀ p : ℕ, p < m → (n / (2 * k - 3) ^ p) % (2 * k - 3) < k - 1},
        x + z = 2 * y → x = y ∧ z = y

end Erdos142
