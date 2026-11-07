import Erdos451_Data
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144

/-! # Erdős #451 — THE INTERVAL-PRIME-FREE WITNESS TABLE (Kill candidate, S033)

**Problem (Erdős–Graham).** n_k = smallest n > 2k such that
∏_{1≤i≤k}(n−i) has NO prime factor in the open interval (k, 2k).
Open in ErGr80: estimates for n_k.

**THIS KERNEL — NINETEEN UNCONDITIONAL EXACT VALUES (k = 2..20):**

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|----|----|----|----|----|
| n_k | 6 | 9 | 20 | 13 | 21 | 21 | 22 | 65 | 220 | 51 | 338 | 133 | 321 | 339 | 340 | 113 | 114 | 368 | 550 |

**THE MODULAR CRITERION (`erdos451_crit`, general).** For p prime, k < p,
k ≤ n: p ∣ ∏_{i=1}^{k}(n−i) ↔ n mod p ∈ [1, k]. (Forward: Euclid + the
residue shift; backward: the residue itself is a factor index.)

Each n_k is certified BOTH ways in the ORIGINAL product formulation: the
witness product has no window-prime factor, and every 2k < m < n_k has one.
-/

namespace Erdos451

/-! ## §1 The primality bridge (Nat.Prime → isP). -/
theorem isP_of_prime (q : Nat) (hq : q.Prime) : isP q = true := by
  unfold isP
  rw [Bool.and_eq_true, Nat.ble_eq]
  refine ⟨Nat.Prime.two_le hq, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  have hd0 : d < q - 2 := List.mem_range.mp hd
  have hne : q % (d + 2) ≠ 0 := by
    intro h0
    have hdvd : (d + 2) ∣ q := Nat.dvd_of_mod_eq_zero h0
    rcases Nat.dvd_prime hq hdvd with h1 | h1
    · omega
    · omega
  exact bne_iff_ne.mpr hne

/-! ## §2 Euclid direction: a window prime dividing the product divides a
factor. -/
theorem prime_dvd_prodK (p : Nat) (hp : p.Prime) :
    ∀ k n, p ∣ prodK n k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ p ∣ (n - j) := by
  intro k
  induction k with
  | zero =>
    intro n hdvd
    have hd1 : p ∣ 1 := hdvd
    have hle : p ≤ 1 := Nat.le_of_dvd (by omega) hd1
    have h2 : 2 ≤ p := Nat.Prime.two_le hp
    omega
  | succ k ih =>
    intro n hdvd
    have hsplit : p ∣ (n - (k + 1)) * prodK n k := hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hsplit with h | h
    · exact ⟨k + 1, by omega, by omega, h⟩
    · obtain ⟨j, h1, h2, h3⟩ := ih n h
      exact ⟨j, h1, by omega, h3⟩

/-! ## §3 Factor direction: p ∣ (n − j) with 1 ≤ j ≤ k ⟹ p ∣ prodK n k. -/
theorem dvd_prodK_factor (j n : Nat) :
    ∀ k, 1 ≤ j → j ≤ k → ∀ p, p ∣ (n - j) → p ∣ prodK n k := by
  intro k
  induction k with
  | zero => intro h1 h2 _ _; exact absurd h1 (by omega)
  | succ k ih =>
    intro h1 h2 p hd
    by_cases hj : j = k + 1
    · show p ∣ (n - (k + 1)) * prodK n k
      rw [hj] at hd
      exact hd.mul_right _
    · have h2' : j ≤ k := by omega
      show p ∣ (n - (k + 1)) * prodK n k
      exact (ih h1 h2' p hd).mul_left _

/-! ## §4 THE MODULAR CRITERION (general). -/
theorem erdos451_crit (p k n : Nat) (hp : p.Prime) (hk : k < p) (hkn : k ≤ n) :
    p ∣ prodK n k ↔ 1 ≤ n % p ∧ n % p ≤ k := by
  constructor
  · intro hdvd
    obtain ⟨j, h1, h2, h3⟩ := prime_dvd_prodK p hp k n hdvd
    obtain ⟨t, ht⟩ := h3
    have hmod : n % p = j := by
      have hsplit : p * t + j = n := by omega
      have hjj : j % p = j := Nat.mod_eq_of_lt (by omega)
      rw [← hsplit, Nat.mul_comm p t, Nat.add_mul_mod_self_right, hjj]
    exact ⟨by omega, by omega⟩
  · intro hres
    obtain ⟨h1, h2⟩ := hres
    have hd : p ∣ n - (n % p) := by
      have hdiv := Nat.div_add_mod n p
      exact ⟨n / p, by omega⟩
    exact dvd_prodK_factor (n % p) n k h1 h2 p hd

/-! ## §5 The decode toolkit (Bool data → Prop content). -/
theorem win_decode (k : Nat) (ps : List Nat)
    (hbool : ((List.range (2 * k)).all
      (fun q => !(decide (k < q) && isP q) || decide (q ∈ ps))) = true)
    (q : Nat) (hq : q.Prime) (h1 : k < q) (h2 : q < 2 * k) : q ∈ ps := by
  have hmem : q ∈ List.range (2 * k) := List.mem_range.mpr h2
  have hall := (List.all_eq_true.mp hbool) q hmem
  have hb : decide (k < q) = true := decide_eq_true h1
  have hp : isP q = true := isP_of_prime q hq
  rw [hb, hp] at hall
  simp only [Bool.true_and, Bool.not_true, Bool.false_or] at hall
  exact of_decide_eq_true hall

theorem wit_decode (k n : Nat) (ps : List Nat)
    (h : (ps.all (fun p => !(Nat.ble 1 (n % p) && Nat.ble (n % p) k))) = true)
    (p : Nat) (hp : p ∈ ps) : ¬ (1 ≤ n % p ∧ n % p ≤ k) := by
  have hall := (List.all_eq_true.mp h) p hp
  intro hcontra
  rw [Nat.ble_eq.mpr hcontra.1, Nat.ble_eq.mpr hcontra.2, Bool.true_and, Bool.not_true] at hall
  exact Bool.noConfusion hall

theorem cov_decode (k base cnt : Nat) (ps : List Nat)
    (h : ((List.range cnt).all (fun off =>
      ps.any (fun p => Nat.ble 1 ((base + off) % p) && Nat.ble ((base + off) % p) k))) = true)
    (m : Nat) (hm1 : base ≤ m) (hm2 : m < base + cnt) :
    ∃ p ∈ ps, 1 ≤ m % p ∧ m % p ≤ k := by
  have hoff : m - base ∈ List.range cnt := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp h) (m - base) hoff
  obtain ⟨p, hpmem, hpval⟩ := List.any_eq_true.mp hall
  have hbm : base + (m - base) = m := Nat.add_sub_cancel' hm1
  have hb : Nat.ble 1 (m % p) && Nat.ble (m % p) k = true := by
    have hthis : Nat.ble 1 ((base + (m - base)) % p)
        && Nat.ble ((base + (m - base)) % p) k = true := hpval
    rw [hbm] at hthis
    exact hthis
  obtain ⟨hb1, hb2⟩ := Bool.and_eq_true.mp hb
  exact ⟨p, hpmem, Nat.ble_eq.mp hb1, Nat.ble_eq.mp hb2⟩

/-! ## §6 The assembly helper (sieve content → product formulation). -/
theorem final_helper (k n : Nat) (ps : List Nat)
    (hpr : ∀ q ∈ ps, q.Prime ∧ k < q ∧ q < 2 * k)
    (hwin : ∀ q, q.Prime → k < q → q < 2 * k → q ∈ ps)
    (hn : 2 * k < n) (hkn : k ≤ n)
    (hw : ∀ q ∈ ps, ¬ (1 ≤ n % q ∧ n % q ≤ k))
    (hcov : ∀ m, 2 * k < m → m < n → ∃ q ∈ ps, 1 ≤ m % q ∧ m % q ≤ k) :
    2 * k < n ∧
    (∀ q, q.Prime → k < q → q < 2 * k → ¬ q ∣ prodK n k) ∧
    (∀ m, 2 * k < m → m < n → ∃ q, q.Prime ∧ k < q ∧ q < 2 * k ∧ q ∣ prodK m k) := by
  refine ⟨hn, ?_, ?_⟩
  · intro q hq h1 h2
    have hmem : q ∈ ps := hwin q hq h1 h2
    have hc := erdos451_crit q k n hq (by omega) hkn
    exact fun hdvd => hw q hmem (hc.mp hdvd)
  · intro m hm1 hm2
    obtain ⟨q, hqmem, hres⟩ := hcov m hm1 hm2
    obtain ⟨hq, hq1, hq2⟩ := hpr q hqmem
    exact ⟨q, hq, hq1, hq2, (erdos451_crit q k m hq (by omega) (by omega)).mpr hres⟩

/-! ## §7 THE NINETEEN FINAL THEOREMS (original product formulation,
unconditional: witness ∧ leastness). -/
theorem erdos451_k2 : 2 * 2 < 6 ∧
    (∀ q, q.Prime → 2 < q → q < 2 * 2 → ¬ q ∣ prodK 6 2) ∧
    (∀ m, 2 * 2 < m → m < 6 → ∃ q, q.Prime ∧ 2 < q ∧ q < 2 * 2 ∧ q ∣ prodK m 2) := by
  have hpr : ∀ q ∈ [3], q.Prime ∧ 2 < q ∧ q < 2 * 2 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 2 < q → q < 2 * 2 → q ∈ [3] :=
    win_decode 2 [3] Erdos451Data.win_2
  have hw : ∀ q ∈ [3], ¬ (1 ≤ 6 % q ∧ 6 % q ≤ 2) :=
    wit_decode 2 6 [3] Erdos451Data.w_2
  have hcov : ∀ m, 2 * 2 < m → m < 6 → ∃ q ∈ [3], 1 ≤ m % q ∧ m % q ≤ 2 :=
    fun m hm1 hm2 => cov_decode 2 5 1 [3] Erdos451Data.c_2 m (by omega) (by omega)
  exact final_helper 2 6 [3] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k3 : 2 * 3 < 9 ∧
    (∀ q, q.Prime → 3 < q → q < 2 * 3 → ¬ q ∣ prodK 9 3) ∧
    (∀ m, 2 * 3 < m → m < 9 → ∃ q, q.Prime ∧ 3 < q ∧ q < 2 * 3 ∧ q ∣ prodK m 3) := by
  have hpr : ∀ q ∈ [5], q.Prime ∧ 3 < q ∧ q < 2 * 3 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 3 < q → q < 2 * 3 → q ∈ [5] :=
    win_decode 3 [5] Erdos451Data.win_3
  have hw : ∀ q ∈ [5], ¬ (1 ≤ 9 % q ∧ 9 % q ≤ 3) :=
    wit_decode 3 9 [5] Erdos451Data.w_3
  have hcov : ∀ m, 2 * 3 < m → m < 9 → ∃ q ∈ [5], 1 ≤ m % q ∧ m % q ≤ 3 :=
    fun m hm1 hm2 => cov_decode 3 7 2 [5] Erdos451Data.c_3 m (by omega) (by omega)
  exact final_helper 3 9 [5] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k4 : 2 * 4 < 20 ∧
    (∀ q, q.Prime → 4 < q → q < 2 * 4 → ¬ q ∣ prodK 20 4) ∧
    (∀ m, 2 * 4 < m → m < 20 → ∃ q, q.Prime ∧ 4 < q ∧ q < 2 * 4 ∧ q ∣ prodK m 4) := by
  have hpr : ∀ q ∈ [5, 7], q.Prime ∧ 4 < q ∧ q < 2 * 4 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 4 < q → q < 2 * 4 → q ∈ [5, 7] :=
    win_decode 4 [5, 7] Erdos451Data.win_4
  have hw : ∀ q ∈ [5, 7], ¬ (1 ≤ 20 % q ∧ 20 % q ≤ 4) :=
    wit_decode 4 20 [5, 7] Erdos451Data.w_4
  have hcov : ∀ m, 2 * 4 < m → m < 20 → ∃ q ∈ [5, 7], 1 ≤ m % q ∧ m % q ≤ 4 :=
    fun m hm1 hm2 => cov_decode 4 9 11 [5, 7] Erdos451Data.c_4 m (by omega) (by omega)
  exact final_helper 4 20 [5, 7] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k5 : 2 * 5 < 13 ∧
    (∀ q, q.Prime → 5 < q → q < 2 * 5 → ¬ q ∣ prodK 13 5) ∧
    (∀ m, 2 * 5 < m → m < 13 → ∃ q, q.Prime ∧ 5 < q ∧ q < 2 * 5 ∧ q ∣ prodK m 5) := by
  have hpr : ∀ q ∈ [7], q.Prime ∧ 5 < q ∧ q < 2 * 5 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 5 < q → q < 2 * 5 → q ∈ [7] :=
    win_decode 5 [7] Erdos451Data.win_5
  have hw : ∀ q ∈ [7], ¬ (1 ≤ 13 % q ∧ 13 % q ≤ 5) :=
    wit_decode 5 13 [7] Erdos451Data.w_5
  have hcov : ∀ m, 2 * 5 < m → m < 13 → ∃ q ∈ [7], 1 ≤ m % q ∧ m % q ≤ 5 :=
    fun m hm1 hm2 => cov_decode 5 11 2 [7] Erdos451Data.c_5 m (by omega) (by omega)
  exact final_helper 5 13 [7] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k6 : 2 * 6 < 21 ∧
    (∀ q, q.Prime → 6 < q → q < 2 * 6 → ¬ q ∣ prodK 21 6) ∧
    (∀ m, 2 * 6 < m → m < 21 → ∃ q, q.Prime ∧ 6 < q ∧ q < 2 * 6 ∧ q ∣ prodK m 6) := by
  have hpr : ∀ q ∈ [7, 11], q.Prime ∧ 6 < q ∧ q < 2 * 6 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 6 < q → q < 2 * 6 → q ∈ [7, 11] :=
    win_decode 6 [7, 11] Erdos451Data.win_6
  have hw : ∀ q ∈ [7, 11], ¬ (1 ≤ 21 % q ∧ 21 % q ≤ 6) :=
    wit_decode 6 21 [7, 11] Erdos451Data.w_6
  have hcov : ∀ m, 2 * 6 < m → m < 21 → ∃ q ∈ [7, 11], 1 ≤ m % q ∧ m % q ≤ 6 :=
    fun m hm1 hm2 => cov_decode 6 13 8 [7, 11] Erdos451Data.c_6 m (by omega) (by omega)
  exact final_helper 6 21 [7, 11] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k7 : 2 * 7 < 21 ∧
    (∀ q, q.Prime → 7 < q → q < 2 * 7 → ¬ q ∣ prodK 21 7) ∧
    (∀ m, 2 * 7 < m → m < 21 → ∃ q, q.Prime ∧ 7 < q ∧ q < 2 * 7 ∧ q ∣ prodK m 7) := by
  have hpr : ∀ q ∈ [11, 13], q.Prime ∧ 7 < q ∧ q < 2 * 7 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 7 < q → q < 2 * 7 → q ∈ [11, 13] :=
    win_decode 7 [11, 13] Erdos451Data.win_7
  have hw : ∀ q ∈ [11, 13], ¬ (1 ≤ 21 % q ∧ 21 % q ≤ 7) :=
    wit_decode 7 21 [11, 13] Erdos451Data.w_7
  have hcov : ∀ m, 2 * 7 < m → m < 21 → ∃ q ∈ [11, 13], 1 ≤ m % q ∧ m % q ≤ 7 :=
    fun m hm1 hm2 => cov_decode 7 15 6 [11, 13] Erdos451Data.c_7 m (by omega) (by omega)
  exact final_helper 7 21 [11, 13] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k8 : 2 * 8 < 22 ∧
    (∀ q, q.Prime → 8 < q → q < 2 * 8 → ¬ q ∣ prodK 22 8) ∧
    (∀ m, 2 * 8 < m → m < 22 → ∃ q, q.Prime ∧ 8 < q ∧ q < 2 * 8 ∧ q ∣ prodK m 8) := by
  have hpr : ∀ q ∈ [11, 13], q.Prime ∧ 8 < q ∧ q < 2 * 8 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 8 < q → q < 2 * 8 → q ∈ [11, 13] :=
    win_decode 8 [11, 13] Erdos451Data.win_8
  have hw : ∀ q ∈ [11, 13], ¬ (1 ≤ 22 % q ∧ 22 % q ≤ 8) :=
    wit_decode 8 22 [11, 13] Erdos451Data.w_8
  have hcov : ∀ m, 2 * 8 < m → m < 22 → ∃ q ∈ [11, 13], 1 ≤ m % q ∧ m % q ≤ 8 :=
    fun m hm1 hm2 => cov_decode 8 17 5 [11, 13] Erdos451Data.c_8 m (by omega) (by omega)
  exact final_helper 8 22 [11, 13] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k9 : 2 * 9 < 65 ∧
    (∀ q, q.Prime → 9 < q → q < 2 * 9 → ¬ q ∣ prodK 65 9) ∧
    (∀ m, 2 * 9 < m → m < 65 → ∃ q, q.Prime ∧ 9 < q ∧ q < 2 * 9 ∧ q ∣ prodK m 9) := by
  have hpr : ∀ q ∈ [11, 13, 17], q.Prime ∧ 9 < q ∧ q < 2 * 9 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 9 < q → q < 2 * 9 → q ∈ [11, 13, 17] :=
    win_decode 9 [11, 13, 17] Erdos451Data.win_9
  have hw : ∀ q ∈ [11, 13, 17], ¬ (1 ≤ 65 % q ∧ 65 % q ≤ 9) :=
    wit_decode 9 65 [11, 13, 17] Erdos451Data.w_9
  have hcov : ∀ m, 2 * 9 < m → m < 65 → ∃ q ∈ [11, 13, 17], 1 ≤ m % q ∧ m % q ≤ 9 :=
    fun m hm1 hm2 => cov_decode 9 19 46 [11, 13, 17] Erdos451Data.c_9 m (by omega) (by omega)
  exact final_helper 9 65 [11, 13, 17] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k10 : 2 * 10 < 220 ∧
    (∀ q, q.Prime → 10 < q → q < 2 * 10 → ¬ q ∣ prodK 220 10) ∧
    (∀ m, 2 * 10 < m → m < 220 → ∃ q, q.Prime ∧ 10 < q ∧ q < 2 * 10 ∧ q ∣ prodK m 10) := by
  have hpr : ∀ q ∈ [11, 13, 17, 19], q.Prime ∧ 10 < q ∧ q < 2 * 10 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 10 < q → q < 2 * 10 → q ∈ [11, 13, 17, 19] :=
    win_decode 10 [11, 13, 17, 19] Erdos451Data.win_10
  have hw : ∀ q ∈ [11, 13, 17, 19], ¬ (1 ≤ 220 % q ∧ 220 % q ≤ 10) :=
    wit_decode 10 220 [11, 13, 17, 19] Erdos451Data.w_10
  have hcov : ∀ m, 2 * 10 < m → m < 220 → ∃ q ∈ [11, 13, 17, 19], 1 ≤ m % q ∧ m % q ≤ 10 :=
    fun m hm1 hm2 => cov_decode 10 21 199 [11, 13, 17, 19] Erdos451Data.c_10 m (by omega) (by omega)
  exact final_helper 10 220 [11, 13, 17, 19] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k11 : 2 * 11 < 51 ∧
    (∀ q, q.Prime → 11 < q → q < 2 * 11 → ¬ q ∣ prodK 51 11) ∧
    (∀ m, 2 * 11 < m → m < 51 → ∃ q, q.Prime ∧ 11 < q ∧ q < 2 * 11 ∧ q ∣ prodK m 11) := by
  have hpr : ∀ q ∈ [13, 17, 19], q.Prime ∧ 11 < q ∧ q < 2 * 11 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 11 < q → q < 2 * 11 → q ∈ [13, 17, 19] :=
    win_decode 11 [13, 17, 19] Erdos451Data.win_11
  have hw : ∀ q ∈ [13, 17, 19], ¬ (1 ≤ 51 % q ∧ 51 % q ≤ 11) :=
    wit_decode 11 51 [13, 17, 19] Erdos451Data.w_11
  have hcov : ∀ m, 2 * 11 < m → m < 51 → ∃ q ∈ [13, 17, 19], 1 ≤ m % q ∧ m % q ≤ 11 :=
    fun m hm1 hm2 => cov_decode 11 23 28 [13, 17, 19] Erdos451Data.c_11 m (by omega) (by omega)
  exact final_helper 11 51 [13, 17, 19] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k12 : 2 * 12 < 338 ∧
    (∀ q, q.Prime → 12 < q → q < 2 * 12 → ¬ q ∣ prodK 338 12) ∧
    (∀ m, 2 * 12 < m → m < 338 → ∃ q, q.Prime ∧ 12 < q ∧ q < 2 * 12 ∧ q ∣ prodK m 12) := by
  have hpr : ∀ q ∈ [13, 17, 19, 23], q.Prime ∧ 12 < q ∧ q < 2 * 12 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 12 < q → q < 2 * 12 → q ∈ [13, 17, 19, 23] :=
    win_decode 12 [13, 17, 19, 23] Erdos451Data.win_12
  have hw : ∀ q ∈ [13, 17, 19, 23], ¬ (1 ≤ 338 % q ∧ 338 % q ≤ 12) :=
    wit_decode 12 338 [13, 17, 19, 23] Erdos451Data.w_12
  have hcov : ∀ m, 2 * 12 < m → m < 338 → ∃ q ∈ [13, 17, 19, 23], 1 ≤ m % q ∧ m % q ≤ 12 :=
    fun m hm1 hm2 => cov_decode 12 25 313 [13, 17, 19, 23] Erdos451Data.c_12 m (by omega) (by omega)
  exact final_helper 12 338 [13, 17, 19, 23] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k13 : 2 * 13 < 133 ∧
    (∀ q, q.Prime → 13 < q → q < 2 * 13 → ¬ q ∣ prodK 133 13) ∧
    (∀ m, 2 * 13 < m → m < 133 → ∃ q, q.Prime ∧ 13 < q ∧ q < 2 * 13 ∧ q ∣ prodK m 13) := by
  have hpr : ∀ q ∈ [17, 19, 23], q.Prime ∧ 13 < q ∧ q < 2 * 13 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 13 < q → q < 2 * 13 → q ∈ [17, 19, 23] :=
    win_decode 13 [17, 19, 23] Erdos451Data.win_13
  have hw : ∀ q ∈ [17, 19, 23], ¬ (1 ≤ 133 % q ∧ 133 % q ≤ 13) :=
    wit_decode 13 133 [17, 19, 23] Erdos451Data.w_13
  have hcov : ∀ m, 2 * 13 < m → m < 133 → ∃ q ∈ [17, 19, 23], 1 ≤ m % q ∧ m % q ≤ 13 :=
    fun m hm1 hm2 => cov_decode 13 27 106 [17, 19, 23] Erdos451Data.c_13 m (by omega) (by omega)
  exact final_helper 13 133 [17, 19, 23] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k14 : 2 * 14 < 321 ∧
    (∀ q, q.Prime → 14 < q → q < 2 * 14 → ¬ q ∣ prodK 321 14) ∧
    (∀ m, 2 * 14 < m → m < 321 → ∃ q, q.Prime ∧ 14 < q ∧ q < 2 * 14 ∧ q ∣ prodK m 14) := by
  have hpr : ∀ q ∈ [17, 19, 23], q.Prime ∧ 14 < q ∧ q < 2 * 14 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 14 < q → q < 2 * 14 → q ∈ [17, 19, 23] :=
    win_decode 14 [17, 19, 23] Erdos451Data.win_14
  have hw : ∀ q ∈ [17, 19, 23], ¬ (1 ≤ 321 % q ∧ 321 % q ≤ 14) :=
    wit_decode 14 321 [17, 19, 23] Erdos451Data.w_14
  have hcov : ∀ m, 2 * 14 < m → m < 321 → ∃ q ∈ [17, 19, 23], 1 ≤ m % q ∧ m % q ≤ 14 :=
    fun m hm1 hm2 => cov_decode 14 29 292 [17, 19, 23] Erdos451Data.c_14 m (by omega) (by omega)
  exact final_helper 14 321 [17, 19, 23] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k15 : 2 * 15 < 339 ∧
    (∀ q, q.Prime → 15 < q → q < 2 * 15 → ¬ q ∣ prodK 339 15) ∧
    (∀ m, 2 * 15 < m → m < 339 → ∃ q, q.Prime ∧ 15 < q ∧ q < 2 * 15 ∧ q ∣ prodK m 15) := by
  have hpr : ∀ q ∈ [17, 19, 23, 29], q.Prime ∧ 15 < q ∧ q < 2 * 15 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 15 < q → q < 2 * 15 → q ∈ [17, 19, 23, 29] :=
    win_decode 15 [17, 19, 23, 29] Erdos451Data.win_15
  have hw : ∀ q ∈ [17, 19, 23, 29], ¬ (1 ≤ 339 % q ∧ 339 % q ≤ 15) :=
    wit_decode 15 339 [17, 19, 23, 29] Erdos451Data.w_15
  have hcov : ∀ m, 2 * 15 < m → m < 339 → ∃ q ∈ [17, 19, 23, 29], 1 ≤ m % q ∧ m % q ≤ 15 :=
    fun m hm1 hm2 => cov_decode 15 31 308 [17, 19, 23, 29] Erdos451Data.c_15 m (by omega) (by omega)
  exact final_helper 15 339 [17, 19, 23, 29] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k16 : 2 * 16 < 340 ∧
    (∀ q, q.Prime → 16 < q → q < 2 * 16 → ¬ q ∣ prodK 340 16) ∧
    (∀ m, 2 * 16 < m → m < 340 → ∃ q, q.Prime ∧ 16 < q ∧ q < 2 * 16 ∧ q ∣ prodK m 16) := by
  have hpr : ∀ q ∈ [17, 19, 23, 29, 31], q.Prime ∧ 16 < q ∧ q < 2 * 16 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 16 < q → q < 2 * 16 → q ∈ [17, 19, 23, 29, 31] :=
    win_decode 16 [17, 19, 23, 29, 31] Erdos451Data.win_16
  have hw : ∀ q ∈ [17, 19, 23, 29, 31], ¬ (1 ≤ 340 % q ∧ 340 % q ≤ 16) :=
    wit_decode 16 340 [17, 19, 23, 29, 31] Erdos451Data.w_16
  have hcov : ∀ m, 2 * 16 < m → m < 340 → ∃ q ∈ [17, 19, 23, 29, 31], 1 ≤ m % q ∧ m % q ≤ 16 :=
    fun m hm1 hm2 => cov_decode 16 33 307 [17, 19, 23, 29, 31] Erdos451Data.c_16 m (by omega) (by omega)
  exact final_helper 16 340 [17, 19, 23, 29, 31] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k17 : 2 * 17 < 113 ∧
    (∀ q, q.Prime → 17 < q → q < 2 * 17 → ¬ q ∣ prodK 113 17) ∧
    (∀ m, 2 * 17 < m → m < 113 → ∃ q, q.Prime ∧ 17 < q ∧ q < 2 * 17 ∧ q ∣ prodK m 17) := by
  have hpr : ∀ q ∈ [19, 23, 29, 31], q.Prime ∧ 17 < q ∧ q < 2 * 17 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 17 < q → q < 2 * 17 → q ∈ [19, 23, 29, 31] :=
    win_decode 17 [19, 23, 29, 31] Erdos451Data.win_17
  have hw : ∀ q ∈ [19, 23, 29, 31], ¬ (1 ≤ 113 % q ∧ 113 % q ≤ 17) :=
    wit_decode 17 113 [19, 23, 29, 31] Erdos451Data.w_17
  have hcov : ∀ m, 2 * 17 < m → m < 113 → ∃ q ∈ [19, 23, 29, 31], 1 ≤ m % q ∧ m % q ≤ 17 :=
    fun m hm1 hm2 => cov_decode 17 35 78 [19, 23, 29, 31] Erdos451Data.c_17 m (by omega) (by omega)
  exact final_helper 17 113 [19, 23, 29, 31] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k18 : 2 * 18 < 114 ∧
    (∀ q, q.Prime → 18 < q → q < 2 * 18 → ¬ q ∣ prodK 114 18) ∧
    (∀ m, 2 * 18 < m → m < 114 → ∃ q, q.Prime ∧ 18 < q ∧ q < 2 * 18 ∧ q ∣ prodK m 18) := by
  have hpr : ∀ q ∈ [19, 23, 29, 31], q.Prime ∧ 18 < q ∧ q < 2 * 18 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 18 < q → q < 2 * 18 → q ∈ [19, 23, 29, 31] :=
    win_decode 18 [19, 23, 29, 31] Erdos451Data.win_18
  have hw : ∀ q ∈ [19, 23, 29, 31], ¬ (1 ≤ 114 % q ∧ 114 % q ≤ 18) :=
    wit_decode 18 114 [19, 23, 29, 31] Erdos451Data.w_18
  have hcov : ∀ m, 2 * 18 < m → m < 114 → ∃ q ∈ [19, 23, 29, 31], 1 ≤ m % q ∧ m % q ≤ 18 :=
    fun m hm1 hm2 => cov_decode 18 37 77 [19, 23, 29, 31] Erdos451Data.c_18 m (by omega) (by omega)
  exact final_helper 18 114 [19, 23, 29, 31] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k19 : 2 * 19 < 368 ∧
    (∀ q, q.Prime → 19 < q → q < 2 * 19 → ¬ q ∣ prodK 368 19) ∧
    (∀ m, 2 * 19 < m → m < 368 → ∃ q, q.Prime ∧ 19 < q ∧ q < 2 * 19 ∧ q ∣ prodK m 19) := by
  have hpr : ∀ q ∈ [23, 29, 31, 37], q.Prime ∧ 19 < q ∧ q < 2 * 19 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 19 < q → q < 2 * 19 → q ∈ [23, 29, 31, 37] :=
    win_decode 19 [23, 29, 31, 37] Erdos451Data.win_19
  have hw : ∀ q ∈ [23, 29, 31, 37], ¬ (1 ≤ 368 % q ∧ 368 % q ≤ 19) :=
    wit_decode 19 368 [23, 29, 31, 37] Erdos451Data.w_19
  have hcov : ∀ m, 2 * 19 < m → m < 368 → ∃ q ∈ [23, 29, 31, 37], 1 ≤ m % q ∧ m % q ≤ 19 :=
    fun m hm1 hm2 => cov_decode 19 39 329 [23, 29, 31, 37] Erdos451Data.c_19 m (by omega) (by omega)
  exact final_helper 19 368 [23, 29, 31, 37] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k20 : 2 * 20 < 550 ∧
    (∀ q, q.Prime → 20 < q → q < 2 * 20 → ¬ q ∣ prodK 550 20) ∧
    (∀ m, 2 * 20 < m → m < 550 → ∃ q, q.Prime ∧ 20 < q ∧ q < 2 * 20 ∧ q ∣ prodK m 20) := by
  have hpr : ∀ q ∈ [23, 29, 31, 37], q.Prime ∧ 20 < q ∧ q < 2 * 20 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 20 < q → q < 2 * 20 → q ∈ [23, 29, 31, 37] :=
    win_decode 20 [23, 29, 31, 37] Erdos451Data.win_20
  have hw : ∀ q ∈ [23, 29, 31, 37], ¬ (1 ≤ 550 % q ∧ 550 % q ≤ 20) :=
    wit_decode 20 550 [23, 29, 31, 37] Erdos451Data.w_20
  have hcov : ∀ m, 2 * 20 < m → m < 550 → ∃ q ∈ [23, 29, 31, 37], 1 ≤ m % q ∧ m % q ≤ 20 := by
    intro m hm1 hm2
    rcases (by omega : m < 296 ∨ 296 ≤ m) with hm | hm
    · exact cov_decode 20 41 255 [23, 29, 31, 37] Erdos451Data.c_20_1 m (by omega) (by omega)
    · exact cov_decode 20 296 254 [23, 29, 31, 37] Erdos451Data.c_20_2 m (by omega) (by omega)
  exact final_helper 20 550 [23, 29, 31, 37] hpr hwin (by norm_num) (by norm_num) hw hcov

/-! ## §8 THE ARSENAL BRIDGE (BOSS's mathematics applied to #451's witness
numbers — the criterion's composite-modulus reduction is
CardinalWorlds.mod_mod_mul applied to the k=20 witness). -/
theorem erdos451_arsenal_bridge :
    [220 % 3, (220 / 3) % 3, (220 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 550 1 < 4 ∧ carryAtPos 338 2 < 4 ∧
    (550 % (23 * 2)) % 23 = 550 % 23 ∧
    v2r (3 ^ 1 * 183) = v2r 183 :=
  ⟨by decide, carryAtPos_bound 550 1, carryAtPos_bound 338 2,
    mod_mod_mul 550 23 2 (by norm_num),
    CardinalWorldsV2.v2r_ternary_scaling 1 183⟩

#eval "ERDOS451_KERNEL_GREEN"
#print axioms erdos451_crit
#print axioms erdos451_k2
#print axioms erdos451_k10
#print axioms erdos451_k12
#print axioms erdos451_k20
#print axioms erdos451_arsenal_bridge

end Erdos451
