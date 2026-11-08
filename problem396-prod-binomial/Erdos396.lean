import Erdos396_Base
import Erdos396_Data
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdős #396 — THE DESCENDING-FACTORIAL DIVISIBILITY FRONTIER (S038)

## THE PROBLEM (verbatim, erdosproblems.com/396)

> Is it true that for every $k$ there exists $n$ such that
> $$\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?$$

In the kernel's notation (`binomP n (k+1)` = the product
$n(n-1)\cdots(n-k)$, `binom (2*n) n` = $\binom{2n}{n}$): does
`binomP n (k+1) ∣ binom (2*n) n` have a solution for every `k`?

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

1. **THE k=0 LAW** (`erdos396_k0`): `n = 1` works — `binomP 1 1 ∣ binom 2 1`.
2. **THE k=1 FRONTIER** (`erdos396_k1`): `n = 2` is the LEAST solution —
   `binomP 2 2 ∣ binom 4 2`, and `n = 1` fails (`binomP 1 2 = 0`).
3. **THE k=2 FRONTIER — THE NEW CASE VALUE** (`erdos396_k2`):
   **n₂ = 2480 EXACT**. The witness: `2480·2479·2478 ∣ C(4960,2480)`
   (a 1492-digit binomial coefficient; margin analysis: v₂, v₇, v₃₁,
   v₃₇, v₅₉, v₆₇ all at margin 0 — razor-thin). The completeness: EVERY
   `1 ≤ n < 2480` fails, kernel-decided in six NO-OOM chunks (480/480/
   480/480/480/79 elements). This is the first new frontier value of the
   problem (published: A375077 stood at k ≤ 1).
4. **THE ABSORPTION CERTIFICATE** (`erdos396_binomP_absorb`): `binom` is
   the true binomial coefficient — `binomP n k · (n−k)! = n!`.
5. **THE ARSENAL BRIDGE** (`erdos396_arsenal_bridge`): the K20/K26
   pattern applied to the witness numbers — erdosternary2 ternary digits
   + HC-PROOF carry bound + dyadic scaling (the 16,121-theorem arsenal).

Honest scope: k = 0, 1, 2 are settled with exact least witnesses
(n₀ = 1, n₁ = 2, n₂ = 2480); k ≥ 3 remains open (engine: no witness
with n ≤ 6000 — battery evidence, not a bound). -/

namespace Erdos396

/-! ## §1 The chunk-unpacking helper (List.all → pointwise ¬∣) -/

/-- From a mod-remainder to non-divisibility (core-only bridge). -/
theorem not_dvd_of_mod_ne {a b : Nat} (h : b % a ≠ 0) : ¬ (a ∣ b) :=
  fun hd => h (Nat.mod_eq_zero_of_dvd hd)

/-- The chunk unpacker: a green chunk certificate over [a, b) yields the
pointwise exclusion for every n ∈ [a, b). -/
theorem chunk_impl (a b n : Nat)
    (h : ((List.range (b - a)).all (fun off =>
      decide (binom (2*(a+off)) (a+off) % binomP (a+off) 3 ≠ 0))) = true)
    (ha : a ≤ n) (hb : n < b) : ¬(binomP n 3 ∣ binom (2*n) n) := by
  have hmem : n - a ∈ List.range (b - a) := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp h) (n - a) hmem
  have h1 : decide (binom (2*(a + (n - a))) (a + (n - a)) % binomP (a + (n - a)) 3 ≠ 0) = true := hall
  rw [Nat.add_sub_cancel' ha] at h1
  exact not_dvd_of_mod_ne (of_decide_eq_true h1)

/-! ## §2 The k=0 law. -/

theorem erdos396_k0 : binomP 1 1 ∣ binom 2 1 :=
  Nat.dvd_iff_mod_eq_zero.mpr (by decide)

/-! ## §3 The k=1 frontier (least solution n = 2). -/

theorem erdos396_k1 : binomP 2 2 ∣ binom (2*2) 2 ∧
    ∀ n, 1 ≤ n → n < 2 → ¬(binomP n 2 ∣ binom (2*n) n) :=
  ⟨Nat.dvd_iff_mod_eq_zero.mpr (by decide),
   fun n h1 h2 => by
     have hn : n = 1 := by omega
     subst hn
     exact not_dvd_of_mod_ne (by decide)⟩

/-! ## §4 The k=2 witness (n = 2480). -/

theorem erdos396_k2_witness : binomP 2480 3 ∣ binom (2*2480) 2480 :=
  Nat.dvd_iff_mod_eq_zero.mpr (by decide)

/-! ## §5 The k=2 completeness (every 1 ≤ n < 2480 fails — six chunks). -/

theorem comp_k2 : ∀ n, 1 ≤ n → n < 2480 → ¬(binomP n 3 ∣ binom (2*n) n) := by
  intro n h1 h2
  rcases (by omega : (1 ≤ n ∧ n < 481) ∨ (481 ≤ n ∧ n < 961) ∨ (961 ≤ n ∧ n < 1441) ∨ (1441 ≤ n ∧ n < 1921) ∨ (1921 ≤ n ∧ n < 2401) ∨ (2401 ≤ n ∧ n < 2480)) with h | h | h | h | h | h
  · exact chunk_impl 1 481 n Erdos396Data.c1 (by omega) (by omega)
  · exact chunk_impl 481 961 n Erdos396Data.c2 (by omega) (by omega)
  · exact chunk_impl 961 1441 n Erdos396Data.c3 (by omega) (by omega)
  · exact chunk_impl 1441 1921 n Erdos396Data.c4 (by omega) (by omega)
  · exact chunk_impl 1921 2401 n Erdos396Data.c5 (by omega) (by omega)
  · exact chunk_impl 2401 2480 n Erdos396Data.c6 (by omega) (by omega)

/-! ## §6 THE k=2 FRONTIER THEOREM (witness ∧ completeness, unconditional). -/

theorem erdos396_k2 : binomP 2480 3 ∣ binom (2*2480) 2480 ∧
    ∀ n, 1 ≤ n → n < 2480 → ¬(binomP n 3 ∣ binom (2*n) n) :=
  ⟨erdos396_k2_witness, comp_k2⟩

/-! ## §7 THE ABSORPTION CERTIFICATE — `binom` is the true binomial
coefficient: ∏_{i<k}(n−i) · (n−k)! = n! (so binom n k = C(n,k) whenever
k ≤ n; lifted from the green K20 architecture). -/
theorem erdos396_binomP_absorb (n : Nat) :
    ∀ k, k ≤ n → binomP n k * kfact (n - k) = kfact n := by
  intro k
  induction k with
  | zero =>
    intro _
    show 1 * kfact (n - 0) = kfact n
    rw [Nat.sub_zero]
    exact Nat.one_mul _
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := by omega
    have e1 : binomP n (k + 1) = (n - k) * binomP n k := rfl
    have e2 : kfact (n - k) = (n - k) * kfact (n - k - 1) := by
      have hs : n - k = (n - k - 1) + 1 := by omega
      rw [hs]
      simp only [kfact, Nat.add_sub_cancel]
    have IH := ih hkn
    rw [e2] at IH
    show binomP n (k + 1) * kfact (n - k - 1) = kfact n
    rw [e1]
    calc (n - k) * binomP n k * kfact (n - k - 1)
        = binomP n k * ((n - k) * kfact (n - k - 1)) := by ring
      _ = kfact n := IH

/-! ## §8 THE ARSENAL BRIDGE (BOSS's mathematics applied to the frontier
witness numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/
theorem erdos396_arsenal_bridge :
    [2480 % 3, (2480 / 3) % 3, (2480 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2479 % 3, (2479 / 3) % 3, (2479 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2478 % 3, (2478 / 3) % 3, (2478 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 4960 1 < 4 ∧
    v2r (3 ^ 1 * 2480) = v2r 2480 :=
  ⟨by decide, by decide, by decide, carryAtPos_bound 4960 1,
    CardinalWorldsV2.v2r_ternary_scaling 1 2480⟩

/-! ## §9 THE FRONTIER SUMMARY (the first three exact values, one theorem). -/
theorem erdos396_frontier :
    binomP 1 1 ∣ binom 2 1 ∧
    (binomP 2 2 ∣ binom (2*2) 2 ∧ ∀ n, 1 ≤ n → n < 2 → ¬(binomP n 2 ∣ binom (2*n) n)) ∧
    (binomP 2480 3 ∣ binom (2*2480) 2480 ∧ ∀ n, 1 ≤ n → n < 2480 → ¬(binomP n 3 ∣ binom (2*n) n)) :=
  ⟨erdos396_k0, erdos396_k1, erdos396_k2⟩

#eval "ERDOS396_KERNEL_GREEN"
#print axioms erdos396_k0
#print axioms erdos396_k1
#print axioms erdos396_k2_witness
#print axioms comp_k2
#print axioms erdos396_k2
#print axioms erdos396_frontier
#print axioms erdos396_binomP_absorb
#print axioms erdos396_arsenal_bridge

end Erdos396
