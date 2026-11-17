import Mathlib
import Arsenal.CardinalWorlds

/-!
# AUDIT KERNEL 142 — the audit-critical lemma (Wave-1 agent W1-A2, DOUBTER lane)

Target: Erdős #142, `r_k(N)` asymptotic (fortress).  This is the kernel of the
adversarial-audit lane (see AUDIT.md in this directory).  It formalizes, in
Arsenal-native language, the law that the Cantor-frame lower bound
`r_3(N) ≥ N^(log_3 2)` rests on:

**THE CANTOR-VERDICT FAMILY IS 3-AP-FREE.**
For all `x, y, z` with `x + z = 2 * y`, if all three survive the Cantor reader
`noTernaryTwo` (Arsenal.CardinalWorlds §1: the ternary expansion avoids the
digit 2, i.e. all ternary digits lie in `{0,1}`), then `x = y` and `z = y`.
Equivalently: the only 3-term arithmetic progressions inside the Cantor family
are the trivial ones.

The proof lane (the digit-window descent): with digits in `{0,1}`,
`2 * (y % 3) - x % 3 - z % 3` lies in `[-2, 2]` and is a multiple of `3`,
hence `0`; the mixed case `0 + 1` has no half in `{0,1}` (it would force
`y % 3 = 2`), so all three position-0 digits agree, the carry is exactly `0`,
and the equation descends to `x/3 + z/3 = 2 * (y/3)`.

Machine-verified by two independent methods in this directory:
`receipts_regen.py` E1 (pure-python brute force, m ≤ 12) and Z1 (Z3 SMT, two
encodings — digit-sum and div/mod reader — UNSAT m ≤ 8), extended to the
mixed sigma-worlds (AUDIT.md §B: subset sums of `{σ_p · 3^p}`, `3 ∤ σ_p` —
the Arsenal §12 mixed 6-world `6^j = 2^j·3^j` is the specialization
`σ_p = 2^p`).

STATUS: **STATEMENT-ONLY kernel** (the campaign's statement-first discipline:
statements frozen, proofs are the next kernel wave's work — no `sorry`, no
`tactics`, `Prop` definitions only).  UNCOMPILED — this sandbox has no Lean
toolchain (boss override); the repo comparator CI (`kills.yml`, `lake env
lean`) is the verifier of record.  NO PUSH from the audit lane: the commander
pushes.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace AuditKernel142

/-! ## §1 The Cantor-verdict AP-free law (the audit-critical lemma) -/

/-- **The audit-critical statement.** The Cantor family (the `noTernaryTwo`
verdict family) is 3-AP-free: the only 3-term progressions inside it are
trivial. -/
def noTernaryTwo_ap3_free : Prop :=
  ∀ x y z : ℕ,
    x + z = 2 * y →
    noTernaryTwo x = true → noTernaryTwo y = true → noTernaryTwo z = true →
    x = y ∧ z = y

/-- **Family form.** At every depth `m`, the Cantor family `C_m` carries no
non-trivial 3-term progression (the digit-window descent closes at the
`3^m` boundary). -/
def cantor_family_no_nontrivial_ap3 : Prop :=
  ∀ m : ℕ,
    ∀ x ∈ {n : ℕ | n < 3 ^ m ∧ noTernaryTwo n = true},
    ∀ y ∈ {n : ℕ | n < 3 ^ m ∧ noTernaryTwo n = true},
    ∀ z ∈ {n : ℕ | n < 3 ^ m ∧ noTernaryTwo n = true},
      x + z = 2 * y → x = y ∧ z = y

/-! ## §2 The mixed sigma-worlds law (the audit extension; Arsenal §12) -/

/-- **The sigma-worlds statement.** For every `m` and every sequence
`σ : ℕ → ℕ` of multipliers with `3 ∤ σ p` for all `p < m`, the mixed family
`{Σ σ_p · 3^p (p < m)}` is 3-AP-free.  The Arsenal §12 mixed 6-world
`6^j = 2^j · 3^j` is the specialization `σ_p = 2^p` (the Z5 receipts:
all σ ∈ {1,2}^m worlds UNSAT m ≤ 6; negative control σ₀ = 3 SAT (6,9,12) —
the `3 ∤ σ` condition is load-bearing). -/
def sigma_worlds_ap3_free : Prop :=
  ∀ m : ℕ, ∀ σ : ℕ → ℕ,
    (∀ p : ℕ, p < m → σ p % 3 ≠ 0) →
    ∀ f g h : ℕ → ℕ,
      (∀ p : ℕ, p < m → f p < 2 ∧ g p < 2 ∧ h p < 2) →
      (∑ p ∈ Finset.range m, f p * σ p * 3 ^ p)
        + (∑ p ∈ Finset.range m, h p * σ p * 3 ^ p)
          = 2 * (∑ p ∈ Finset.range m, g p * σ p * 3 ^ p) →
      (∑ p ∈ Finset.range m, f p * σ p * 3 ^ p)
        = (∑ p ∈ Finset.range m, g p * σ p * 3 ^ p) ∧
      (∑ p ∈ Finset.range m, h p * σ p * 3 ^ p)
        = (∑ p ∈ Finset.range m, g p * σ p * 3 ^ p)

end AuditKernel142
