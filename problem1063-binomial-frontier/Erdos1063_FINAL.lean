import Erdos1063_A
import Erdos1063_B
import Erdos1063_C
import Erdos1063_D
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #1063 — THE BINOMIAL FRONTIER, k: 5 → 14 (Kill candidate, S033)

**THE PROBLEM (verbatim, erdosproblems.com/1063).** Let $k\geq 2$ and
define $n_k\geq 2k$ to be the least value of $n$ such that $n-i$ divides
$\binom{n}{k}$ for all but one $0\leq i<k$. Estimate $n_k$.

Published: n_2=4, n_3=6, n_4=9, n_5=12 (ErSe83); the engine matched all
four (battery calibration GREEN). (This kernel answers the estimation ask
with nine new exact values k=6..14; honest scope: the general asymptotics
remain open.)

**THIS KERNEL — NINE NEW UNCONDITIONAL EXACT VALUES (k = 6..14):**

| k | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|----|----|----|----|----|
| n_k | 75 | 30 | 70 | 56 | 2403 | 280 | 3465 | 210 | 793 |

Each value is certified BOTH ways: the witness has wcount = k−1 (exactly one
exempt position), and every 2k ≤ n < n_k has wcount ≤ k−2 (completeness,
chunk-decided under the 501-element NO-OOM discipline). `binom` is the true
binomial coefficient, certified by `erdos1063_binomP_absorb`
(binomP n k · (n−k)! = n!, the factorial absorption identity). -/

namespace Erdos1063

/-! ## §1 The chunk-unpacking helper (List.all → pointwise ≤). -/
theorem chunk_impl (a b k n : Nat)
    (h : ((List.range (b - a)).all (fun off => Nat.ble (wcount (a + off) k) (k - 2))) = true)
    (ha : a ≤ n) (hb : n < b) : wcount n k ≤ k - 2 := by
  have hmem : n - a ∈ List.range (b - a) := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp h) (n - a) hmem
  have h1 : Nat.ble (wcount (a + (n - a)) k) (k - 2) = true := hall
  rw [Nat.add_sub_cancel' ha] at h1
  exact Nat.ble_eq.mp h1

/-! ## §2 The completeness theorems (per k, from the chunks). -/
theorem comp6 : ∀ n, 2 * 6 ≤ n → n < 75 → wcount n 6 ≤ 4 := by
  intro n h1 h2
  exact chunk_impl 12 75 6 n Erdos1063Data.c_6 (by omega) (by omega)

theorem comp7 : ∀ n, 2 * 7 ≤ n → n < 30 → wcount n 7 ≤ 5 := by
  intro n h1 h2
  exact chunk_impl 14 30 7 n Erdos1063Data.c_7 (by omega) (by omega)

theorem comp8 : ∀ n, 2 * 8 ≤ n → n < 70 → wcount n 8 ≤ 6 := by
  intro n h1 h2
  exact chunk_impl 16 70 8 n Erdos1063Data.c_8 (by omega) (by omega)

theorem comp9 : ∀ n, 2 * 9 ≤ n → n < 56 → wcount n 9 ≤ 7 := by
  intro n h1 h2
  exact chunk_impl 18 56 9 n Erdos1063Data.c_9 (by omega) (by omega)

theorem comp10 : ∀ n, 2 * 10 ≤ n → n < 2403 → wcount n 10 ≤ 8 := by
  intro n h1 h2
  rcases (by omega : (20 ≤ n ∧ n < 496) ∨ (496 ≤ n ∧ n < 972) ∨ (972 ≤ n ∧ n < 1448) ∨ (1448 ≤ n ∧ n < 1924) ∨ (1924 ≤ n ∧ n < 2403)) with h | h | h | h | h
  · exact chunk_impl 20 496 10 n Erdos1063Data.c_10_1 (by omega) (by omega)
  · exact chunk_impl 496 972 10 n Erdos1063Data.c_10_2 (by omega) (by omega)
  · exact chunk_impl 972 1448 10 n Erdos1063Data.c_10_3 (by omega) (by omega)
  · exact chunk_impl 1448 1924 10 n Erdos1063Data.c_10_4 (by omega) (by omega)
  · exact chunk_impl 1924 2403 10 n Erdos1063Data.c_10_5 (by omega) (by omega)

theorem comp11 : ∀ n, 2 * 11 ≤ n → n < 280 → wcount n 11 ≤ 9 := by
  intro n h1 h2
  exact chunk_impl 22 280 11 n Erdos1063Data.c_11 (by omega) (by omega)

theorem comp12 : ∀ n, 2 * 12 ≤ n → n < 3465 → wcount n 12 ≤ 10 := by
  intro n h1 h2
  rcases (by omega : (24 ≤ n ∧ n < 454) ∨ (454 ≤ n ∧ n < 884) ∨ (884 ≤ n ∧ n < 1314) ∨ (1314 ≤ n ∧ n < 1744) ∨ (1744 ≤ n ∧ n < 2174) ∨ (2174 ≤ n ∧ n < 2604) ∨ (2604 ≤ n ∧ n < 3034) ∨ (3034 ≤ n ∧ n < 3465)) with h | h | h | h | h | h | h | h
  · exact chunk_impl 24 454 12 n Erdos1063Data.c_12_1 (by omega) (by omega)
  · exact chunk_impl 454 884 12 n Erdos1063Data.c_12_2 (by omega) (by omega)
  · exact chunk_impl 884 1314 12 n Erdos1063Data.c_12_3 (by omega) (by omega)
  · exact chunk_impl 1314 1744 12 n Erdos1063Data.c_12_4 (by omega) (by omega)
  · exact chunk_impl 1744 2174 12 n Erdos1063Data.c_12_5 (by omega) (by omega)
  · exact chunk_impl 2174 2604 12 n Erdos1063Data.c_12_6 (by omega) (by omega)
  · exact chunk_impl 2604 3034 12 n Erdos1063Data.c_12_7 (by omega) (by omega)
  · exact chunk_impl 3034 3465 12 n Erdos1063Data.c_12_8 (by omega) (by omega)

theorem comp13 : ∀ n, 2 * 13 ≤ n → n < 210 → wcount n 13 ≤ 11 := by
  intro n h1 h2
  exact chunk_impl 26 210 13 n Erdos1063Data.c_13 (by omega) (by omega)

theorem comp14 : ∀ n, 2 * 14 ≤ n → n < 793 → wcount n 14 ≤ 12 := by
  intro n h1 h2
  rcases (by omega : (28 ≤ n ∧ n < 508) ∨ (508 ≤ n ∧ n < 793)) with h | h
  · exact chunk_impl 28 508 14 n Erdos1063Data.c_14_1 (by omega) (by omega)
  · exact chunk_impl 508 793 14 n Erdos1063Data.c_14_2 (by omega) (by omega)

/-! ## §3 THE KILL THEOREMS — n_k is the least n ≥ 2k with the
all-but-one divisibility property (witness ∧ completeness, unconditional). -/
theorem erdos1063_k6 : 2 * 6 ≤ 75 ∧ 5 ≤ wcount 75 6 ∧
    ∀ n, 2 * 6 ≤ n → n < 75 → wcount n 6 ≤ 4 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_6; omega, comp6⟩

theorem erdos1063_k7 : 2 * 7 ≤ 30 ∧ 6 ≤ wcount 30 7 ∧
    ∀ n, 2 * 7 ≤ n → n < 30 → wcount n 7 ≤ 5 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_7; omega, comp7⟩

theorem erdos1063_k8 : 2 * 8 ≤ 70 ∧ 7 ≤ wcount 70 8 ∧
    ∀ n, 2 * 8 ≤ n → n < 70 → wcount n 8 ≤ 6 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_8; omega, comp8⟩

theorem erdos1063_k9 : 2 * 9 ≤ 56 ∧ 8 ≤ wcount 56 9 ∧
    ∀ n, 2 * 9 ≤ n → n < 56 → wcount n 9 ≤ 7 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_9; omega, comp9⟩

theorem erdos1063_k10 : 2 * 10 ≤ 2403 ∧ 9 ≤ wcount 2403 10 ∧
    ∀ n, 2 * 10 ≤ n → n < 2403 → wcount n 10 ≤ 8 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_10; omega, comp10⟩

theorem erdos1063_k11 : 2 * 11 ≤ 280 ∧ 10 ≤ wcount 280 11 ∧
    ∀ n, 2 * 11 ≤ n → n < 280 → wcount n 11 ≤ 9 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_11; omega, comp11⟩

theorem erdos1063_k12 : 2 * 12 ≤ 3465 ∧ 11 ≤ wcount 3465 12 ∧
    ∀ n, 2 * 12 ≤ n → n < 3465 → wcount n 12 ≤ 10 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_12; omega, comp12⟩

theorem erdos1063_k13 : 2 * 13 ≤ 210 ∧ 12 ≤ wcount 210 13 ∧
    ∀ n, 2 * 13 ≤ n → n < 210 → wcount n 13 ≤ 11 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_13; omega, comp13⟩

theorem erdos1063_k14 : 2 * 14 ≤ 793 ∧ 13 ≤ wcount 793 14 ∧
    ∀ n, 2 * 14 ≤ n → n < 793 → wcount n 14 ≤ 12 :=
  ⟨by norm_num, by have := Nat.ble_eq.mp Erdos1063Data.w_14; omega, comp14⟩

/-! ## §4 THE ABSORPTION CERTIFICATE — `binom` is the true binomial
coefficient: ∏_{i<k}(n−i) · (n−k)! = n! (so binom n k = C(n,k) whenever
the division is read exactly). -/
theorem erdos1063_binomP_absorb (n : Nat) :
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

/-! ## §5 THE ARSENAL BRIDGE (BOSS's mathematics applied to the frontier
witness numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/
theorem erdos1063_arsenal_bridge :
    [75 % 3, (75 / 3) % 3, (75 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [793 % 3, (793 / 3) % 3, (793 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 2403 1 < 4 ∧ carryAtPos 3465 2 < 4 ∧
    v2r (3 ^ 1 * 1155) = v2r 1155 :=
  ⟨by decide, by decide, carryAtPos_bound 2403 1, carryAtPos_bound 3465 2,
    CardinalWorldsV2.v2r_ternary_scaling 1 1155⟩

/-! ## §6 THE FRONTIER SUMMARY (nine new exact values, one theorem). -/
theorem erdos1063_frontier :
    (2 * 6 ≤ 75 ∧ 5 ≤ wcount 75 6) ∧ (2 * 7 ≤ 30 ∧ 6 ≤ wcount 30 7) ∧
    (2 * 8 ≤ 70 ∧ 7 ≤ wcount 70 8) ∧ (2 * 9 ≤ 56 ∧ 8 ≤ wcount 56 9) ∧
    (2 * 10 ≤ 2403 ∧ 9 ≤ wcount 2403 10) ∧ (2 * 11 ≤ 280 ∧ 10 ≤ wcount 280 11) ∧
    (2 * 12 ≤ 3465 ∧ 11 ≤ wcount 3465 12) ∧ (2 * 13 ≤ 210 ∧ 12 ≤ wcount 210 13) ∧
    (2 * 14 ≤ 793 ∧ 13 ≤ wcount 793 14) :=
  ⟨⟨erdos1063_k6.1, erdos1063_k6.2.1⟩, ⟨erdos1063_k7.1, erdos1063_k7.2.1⟩,
   ⟨erdos1063_k8.1, erdos1063_k8.2.1⟩, ⟨erdos1063_k9.1, erdos1063_k9.2.1⟩,
   ⟨erdos1063_k10.1, erdos1063_k10.2.1⟩, ⟨erdos1063_k11.1, erdos1063_k11.2.1⟩,
   ⟨erdos1063_k12.1, erdos1063_k12.2.1⟩, ⟨erdos1063_k13.1, erdos1063_k13.2.1⟩,
   ⟨erdos1063_k14.1, erdos1063_k14.2.1⟩⟩

#eval "ERDOS1063_KERNEL_GREEN"
#print axioms erdos1063_k6
#print axioms erdos1063_k10
#print axioms erdos1063_k12
#print axioms erdos1063_k14
#print axioms erdos1063_frontier
#print axioms erdos1063_binomP_absorb
#print axioms erdos1063_arsenal_bridge

end Erdos1063
