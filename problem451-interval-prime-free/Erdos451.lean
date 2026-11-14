import Erdos451_Data
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144

/-! # Erdős #451 — THE INTERVAL-PRIME-FREE WITNESS TABLE (Kill candidate, S033)

**THE PROBLEM (verbatim, erdosproblems.com/451).** Estimate $n_k$, the
smallest integer $>2k$ such that $\prod_{1\leq i\leq k}(n_k-i)$ has no
prime factor in $(k,2k)$.

(This kernel answers the estimation ask at machine precision: nineteen
exact values $k=2..20$ + the general modular criterion; honest scope in
the registry: the general asymptotics remain open.)

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
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
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
      rw [← hsplit, Nat.add_comm, Nat.add_mul_mod_self_left, hjj]
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
  have hb : (Nat.ble 1 (m % p) && Nat.ble (m % p) k) = true := by
    have hthis : (Nat.ble 1 ((base + (m - base)) % p)
        && Nat.ble ((base + (m - base)) % p) k) = true := hpval
    rw [hbm] at hthis
    exact hthis
  obtain ⟨hb1, hb2⟩ : (Nat.ble 1 (m % p) = true ∧ Nat.ble (m % p) k = true) := by
    rw [← Bool.and_eq_true]
    exact hb
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

/-! ## §7b THE EIGHT EXTENSION THEOREMS (k = 21..28, W62 + W63 volleys;
original product formulation, unconditional: witness ∧ leastness). The
certified frontier of this kernel is now k = 2..28: n_21 = 805,
n_22 = 2691, n_23 = 1884, n_24 = 2664, n_25 = 7653, n_26 = 7654,
n_27 = 36887, n_28 = 36888. Same §6 assembly machinery, same §5 decode
toolkit, same dual-method machine certificate (battery451_ext_w63.py,
triple-route GREEN). -/

theorem erdos451_k21 : 2 * 21 < 805 ∧
    (∀ q, q.Prime → 21 < q → q < 2 * 21 → ¬ q ∣ prodK 805 21) ∧
    (∀ m, 2 * 21 < m → m < 805 → ∃ q, q.Prime ∧ 21 < q ∧ q < 2 * 21 ∧ q ∣ prodK m 21) := by
  have hpr : ∀ q ∈ [23, 29, 31, 37, 41], q.Prime ∧ 21 < q ∧ q < 2 * 21 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 21 < q → q < 2 * 21 → q ∈ [23, 29, 31, 37, 41] :=
    win_decode 21 [23, 29, 31, 37, 41] Erdos451Data.win_21
  have hw : ∀ q ∈ [23, 29, 31, 37, 41], ¬ (1 ≤ 805 % q ∧ 805 % q ≤ 21) :=
    wit_decode 21 805 [23, 29, 31, 37, 41] Erdos451Data.w_21
  have hcov : ∀ m, 2 * 21 < m → m < 805 → ∃ q ∈ [23, 29, 31, 37, 41], 1 ≤ m % q ∧ m % q ≤ 21 := by
    intro m hm1 hm2
    rcases (by omega : m < 543 ∨ 543 ≤ m) with h0 | h0
    · exact cov_decode 21 43 500 [23, 29, 31, 37, 41] Erdos451Data.c_21_1 m (by omega) (by omega)
    · exact cov_decode 21 543 262 [23, 29, 31, 37, 41] Erdos451Data.c_21_2 m (by omega) (by omega)
  exact final_helper 21 805 [23, 29, 31, 37, 41] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k22 : 2 * 22 < 2691 ∧
    (∀ q, q.Prime → 22 < q → q < 2 * 22 → ¬ q ∣ prodK 2691 22) ∧
    (∀ m, 2 * 22 < m → m < 2691 → ∃ q, q.Prime ∧ 22 < q ∧ q < 2 * 22 ∧ q ∣ prodK m 22) := by
  have hpr : ∀ q ∈ [23, 29, 31, 37, 41, 43], q.Prime ∧ 22 < q ∧ q < 2 * 22 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 22 < q → q < 2 * 22 → q ∈ [23, 29, 31, 37, 41, 43] :=
    win_decode 22 [23, 29, 31, 37, 41, 43] Erdos451Data.win_22
  have hw : ∀ q ∈ [23, 29, 31, 37, 41, 43], ¬ (1 ≤ 2691 % q ∧ 2691 % q ≤ 22) :=
    wit_decode 22 2691 [23, 29, 31, 37, 41, 43] Erdos451Data.w_22
  have hcov : ∀ m, 2 * 22 < m → m < 2691 → ∃ q ∈ [23, 29, 31, 37, 41, 43], 1 ≤ m % q ∧ m % q ≤ 22 := by
    intro m hm1 hm2
    rcases (by omega : m < 1545 ∨ 1545 ≤ m) with h0 | h0
    · rcases (by omega : m < 545 ∨ 545 ≤ m) with h1 | h1
      · exact cov_decode 22 45 500 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_1 m (by omega) (by omega)
      · rcases (by omega : m < 1045 ∨ 1045 ≤ m) with h2 | h2
        · exact cov_decode 22 545 500 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_2 m (by omega) (by omega)
        · exact cov_decode 22 1045 500 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_3 m (by omega) (by omega)
    · rcases (by omega : m < 2045 ∨ 2045 ≤ m) with h1 | h1
      · exact cov_decode 22 1545 500 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_4 m (by omega) (by omega)
      · rcases (by omega : m < 2545 ∨ 2545 ≤ m) with h2 | h2
        · exact cov_decode 22 2045 500 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_5 m (by omega) (by omega)
        · exact cov_decode 22 2545 146 [23, 29, 31, 37, 41, 43] Erdos451Data.c_22_6 m (by omega) (by omega)
  exact final_helper 22 2691 [23, 29, 31, 37, 41, 43] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k23 : 2 * 23 < 1884 ∧
    (∀ q, q.Prime → 23 < q → q < 2 * 23 → ¬ q ∣ prodK 1884 23) ∧
    (∀ m, 2 * 23 < m → m < 1884 → ∃ q, q.Prime ∧ 23 < q ∧ q < 2 * 23 ∧ q ∣ prodK m 23) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43], q.Prime ∧ 23 < q ∧ q < 2 * 23 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 23 < q → q < 2 * 23 → q ∈ [29, 31, 37, 41, 43] :=
    win_decode 23 [29, 31, 37, 41, 43] Erdos451Data.win_23
  have hw : ∀ q ∈ [29, 31, 37, 41, 43], ¬ (1 ≤ 1884 % q ∧ 1884 % q ≤ 23) :=
    wit_decode 23 1884 [29, 31, 37, 41, 43] Erdos451Data.w_23
  have hcov : ∀ m, 2 * 23 < m → m < 1884 → ∃ q ∈ [29, 31, 37, 41, 43], 1 ≤ m % q ∧ m % q ≤ 23 := by
    intro m hm1 hm2
    rcases (by omega : m < 1047 ∨ 1047 ≤ m) with h0 | h0
    · rcases (by omega : m < 547 ∨ 547 ≤ m) with h1 | h1
      · exact cov_decode 23 47 500 [29, 31, 37, 41, 43] Erdos451Data.c_23_1 m (by omega) (by omega)
      · exact cov_decode 23 547 500 [29, 31, 37, 41, 43] Erdos451Data.c_23_2 m (by omega) (by omega)
    · rcases (by omega : m < 1547 ∨ 1547 ≤ m) with h1 | h1
      · exact cov_decode 23 1047 500 [29, 31, 37, 41, 43] Erdos451Data.c_23_3 m (by omega) (by omega)
      · exact cov_decode 23 1547 337 [29, 31, 37, 41, 43] Erdos451Data.c_23_4 m (by omega) (by omega)
  exact final_helper 23 1884 [29, 31, 37, 41, 43] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k24 : 2 * 24 < 2664 ∧
    (∀ q, q.Prime → 24 < q → q < 2 * 24 → ¬ q ∣ prodK 2664 24) ∧
    (∀ m, 2 * 24 < m → m < 2664 → ∃ q, q.Prime ∧ 24 < q ∧ q < 2 * 24 ∧ q ∣ prodK m 24) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43, 47], q.Prime ∧ 24 < q ∧ q < 2 * 24 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 24 < q → q < 2 * 24 → q ∈ [29, 31, 37, 41, 43, 47] :=
    win_decode 24 [29, 31, 37, 41, 43, 47] Erdos451Data.win_24
  have hw : ∀ q ∈ [29, 31, 37, 41, 43, 47], ¬ (1 ≤ 2664 % q ∧ 2664 % q ≤ 24) :=
    wit_decode 24 2664 [29, 31, 37, 41, 43, 47] Erdos451Data.w_24
  have hcov : ∀ m, 2 * 24 < m → m < 2664 → ∃ q ∈ [29, 31, 37, 41, 43, 47], 1 ≤ m % q ∧ m % q ≤ 24 := by
    intro m hm1 hm2
    rcases (by omega : m < 1549 ∨ 1549 ≤ m) with h0 | h0
    · rcases (by omega : m < 549 ∨ 549 ≤ m) with h1 | h1
      · exact cov_decode 24 49 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_1 m (by omega) (by omega)
      · rcases (by omega : m < 1049 ∨ 1049 ≤ m) with h2 | h2
        · exact cov_decode 24 549 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_2 m (by omega) (by omega)
        · exact cov_decode 24 1049 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_3 m (by omega) (by omega)
    · rcases (by omega : m < 2049 ∨ 2049 ≤ m) with h1 | h1
      · exact cov_decode 24 1549 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_4 m (by omega) (by omega)
      · rcases (by omega : m < 2549 ∨ 2549 ≤ m) with h2 | h2
        · exact cov_decode 24 2049 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_5 m (by omega) (by omega)
        · exact cov_decode 24 2549 115 [29, 31, 37, 41, 43, 47] Erdos451Data.c_24_6 m (by omega) (by omega)
  exact final_helper 24 2664 [29, 31, 37, 41, 43, 47] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k25 : 2 * 25 < 7653 ∧
    (∀ q, q.Prime → 25 < q → q < 2 * 25 → ¬ q ∣ prodK 7653 25) ∧
    (∀ m, 2 * 25 < m → m < 7653 → ∃ q, q.Prime ∧ 25 < q ∧ q < 2 * 25 ∧ q ∣ prodK m 25) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43, 47], q.Prime ∧ 25 < q ∧ q < 2 * 25 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 25 < q → q < 2 * 25 → q ∈ [29, 31, 37, 41, 43, 47] :=
    win_decode 25 [29, 31, 37, 41, 43, 47] Erdos451Data.win_25
  have hw : ∀ q ∈ [29, 31, 37, 41, 43, 47], ¬ (1 ≤ 7653 % q ∧ 7653 % q ≤ 25) :=
    wit_decode 25 7653 [29, 31, 37, 41, 43, 47] Erdos451Data.w_25
  have hcov : ∀ m, 2 * 25 < m → m < 7653 → ∃ q ∈ [29, 31, 37, 41, 43, 47], 1 ≤ m % q ∧ m % q ≤ 25 := by
    intro m hm1 hm2
    rcases (by omega : m < 4051 ∨ 4051 ≤ m) with h0 | h0
    · rcases (by omega : m < 2051 ∨ 2051 ≤ m) with h1 | h1
      · rcases (by omega : m < 1051 ∨ 1051 ≤ m) with h2 | h2
        · rcases (by omega : m < 551 ∨ 551 ≤ m) with h3 | h3
          · exact cov_decode 25 51 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_1 m (by omega) (by omega)
          · exact cov_decode 25 551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_2 m (by omega) (by omega)
        · rcases (by omega : m < 1551 ∨ 1551 ≤ m) with h3 | h3
          · exact cov_decode 25 1051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_3 m (by omega) (by omega)
          · exact cov_decode 25 1551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_4 m (by omega) (by omega)
      · rcases (by omega : m < 3051 ∨ 3051 ≤ m) with h2 | h2
        · rcases (by omega : m < 2551 ∨ 2551 ≤ m) with h3 | h3
          · exact cov_decode 25 2051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_5 m (by omega) (by omega)
          · exact cov_decode 25 2551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_6 m (by omega) (by omega)
        · rcases (by omega : m < 3551 ∨ 3551 ≤ m) with h3 | h3
          · exact cov_decode 25 3051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_7 m (by omega) (by omega)
          · exact cov_decode 25 3551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_8 m (by omega) (by omega)
    · rcases (by omega : m < 6051 ∨ 6051 ≤ m) with h1 | h1
      · rcases (by omega : m < 5051 ∨ 5051 ≤ m) with h2 | h2
        · rcases (by omega : m < 4551 ∨ 4551 ≤ m) with h3 | h3
          · exact cov_decode 25 4051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_9 m (by omega) (by omega)
          · exact cov_decode 25 4551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_10 m (by omega) (by omega)
        · rcases (by omega : m < 5551 ∨ 5551 ≤ m) with h3 | h3
          · exact cov_decode 25 5051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_11 m (by omega) (by omega)
          · exact cov_decode 25 5551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_12 m (by omega) (by omega)
      · rcases (by omega : m < 7051 ∨ 7051 ≤ m) with h2 | h2
        · rcases (by omega : m < 6551 ∨ 6551 ≤ m) with h3 | h3
          · exact cov_decode 25 6051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_13 m (by omega) (by omega)
          · exact cov_decode 25 6551 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_14 m (by omega) (by omega)
        · rcases (by omega : m < 7551 ∨ 7551 ≤ m) with h3 | h3
          · exact cov_decode 25 7051 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_15 m (by omega) (by omega)
          · exact cov_decode 25 7551 102 [29, 31, 37, 41, 43, 47] Erdos451Data.c_25_16 m (by omega) (by omega)
  exact final_helper 25 7653 [29, 31, 37, 41, 43, 47] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k26 : 2 * 26 < 7654 ∧
    (∀ q, q.Prime → 26 < q → q < 2 * 26 → ¬ q ∣ prodK 7654 26) ∧
    (∀ m, 2 * 26 < m → m < 7654 → ∃ q, q.Prime ∧ 26 < q ∧ q < 2 * 26 ∧ q ∣ prodK m 26) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43, 47], q.Prime ∧ 26 < q ∧ q < 2 * 26 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 26 < q → q < 2 * 26 → q ∈ [29, 31, 37, 41, 43, 47] :=
    win_decode 26 [29, 31, 37, 41, 43, 47] Erdos451Data.win_26
  have hw : ∀ q ∈ [29, 31, 37, 41, 43, 47], ¬ (1 ≤ 7654 % q ∧ 7654 % q ≤ 26) :=
    wit_decode 26 7654 [29, 31, 37, 41, 43, 47] Erdos451Data.w_26
  have hcov : ∀ m, 2 * 26 < m → m < 7654 → ∃ q ∈ [29, 31, 37, 41, 43, 47], 1 ≤ m % q ∧ m % q ≤ 26 := by
    intro m hm1 hm2
    rcases (by omega : m < 4053 ∨ 4053 ≤ m) with h0 | h0
    · rcases (by omega : m < 2053 ∨ 2053 ≤ m) with h1 | h1
      · rcases (by omega : m < 1053 ∨ 1053 ≤ m) with h2 | h2
        · rcases (by omega : m < 553 ∨ 553 ≤ m) with h3 | h3
          · exact cov_decode 26 53 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_1 m (by omega) (by omega)
          · exact cov_decode 26 553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_2 m (by omega) (by omega)
        · rcases (by omega : m < 1553 ∨ 1553 ≤ m) with h3 | h3
          · exact cov_decode 26 1053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_3 m (by omega) (by omega)
          · exact cov_decode 26 1553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_4 m (by omega) (by omega)
      · rcases (by omega : m < 3053 ∨ 3053 ≤ m) with h2 | h2
        · rcases (by omega : m < 2553 ∨ 2553 ≤ m) with h3 | h3
          · exact cov_decode 26 2053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_5 m (by omega) (by omega)
          · exact cov_decode 26 2553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_6 m (by omega) (by omega)
        · rcases (by omega : m < 3553 ∨ 3553 ≤ m) with h3 | h3
          · exact cov_decode 26 3053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_7 m (by omega) (by omega)
          · exact cov_decode 26 3553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_8 m (by omega) (by omega)
    · rcases (by omega : m < 6053 ∨ 6053 ≤ m) with h1 | h1
      · rcases (by omega : m < 5053 ∨ 5053 ≤ m) with h2 | h2
        · rcases (by omega : m < 4553 ∨ 4553 ≤ m) with h3 | h3
          · exact cov_decode 26 4053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_9 m (by omega) (by omega)
          · exact cov_decode 26 4553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_10 m (by omega) (by omega)
        · rcases (by omega : m < 5553 ∨ 5553 ≤ m) with h3 | h3
          · exact cov_decode 26 5053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_11 m (by omega) (by omega)
          · exact cov_decode 26 5553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_12 m (by omega) (by omega)
      · rcases (by omega : m < 7053 ∨ 7053 ≤ m) with h2 | h2
        · rcases (by omega : m < 6553 ∨ 6553 ≤ m) with h3 | h3
          · exact cov_decode 26 6053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_13 m (by omega) (by omega)
          · exact cov_decode 26 6553 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_14 m (by omega) (by omega)
        · rcases (by omega : m < 7553 ∨ 7553 ≤ m) with h3 | h3
          · exact cov_decode 26 7053 500 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_15 m (by omega) (by omega)
          · exact cov_decode 26 7553 101 [29, 31, 37, 41, 43, 47] Erdos451Data.c_26_16 m (by omega) (by omega)
  exact final_helper 26 7654 [29, 31, 37, 41, 43, 47] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k27 : 2 * 27 < 36887 ∧
    (∀ q, q.Prime → 27 < q → q < 2 * 27 → ¬ q ∣ prodK 36887 27) ∧
    (∀ m, 2 * 27 < m → m < 36887 → ∃ q, q.Prime ∧ 27 < q ∧ q < 2 * 27 ∧ q ∣ prodK m 27) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43, 47, 53], q.Prime ∧ 27 < q ∧ q < 2 * 27 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 27 < q → q < 2 * 27 → q ∈ [29, 31, 37, 41, 43, 47, 53] :=
    win_decode 27 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.win_27
  have hw : ∀ q ∈ [29, 31, 37, 41, 43, 47, 53], ¬ (1 ≤ 36887 % q ∧ 36887 % q ≤ 27) :=
    wit_decode 27 36887 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.w_27
  have hcov : ∀ m, 2 * 27 < m → m < 36887 → ∃ q ∈ [29, 31, 37, 41, 43, 47, 53], 1 ≤ m % q ∧ m % q ≤ 27 := by
    intro m hm1 hm2
    rcases (by omega : m < 18555 ∨ 18555 ≤ m) with h0 | h0
    · rcases (by omega : m < 9055 ∨ 9055 ≤ m) with h1 | h1
      · rcases (by omega : m < 4555 ∨ 4555 ≤ m) with h2 | h2
        · rcases (by omega : m < 2055 ∨ 2055 ≤ m) with h3 | h3
          · rcases (by omega : m < 1055 ∨ 1055 ≤ m) with h4 | h4
            · rcases (by omega : m < 555 ∨ 555 ≤ m) with h5 | h5
              · exact cov_decode 27 55 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_1 m (by omega) (by omega)
              · exact cov_decode 27 555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_2 m (by omega) (by omega)
            · rcases (by omega : m < 1555 ∨ 1555 ≤ m) with h5 | h5
              · exact cov_decode 27 1055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_3 m (by omega) (by omega)
              · exact cov_decode 27 1555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_4 m (by omega) (by omega)
          · rcases (by omega : m < 3055 ∨ 3055 ≤ m) with h4 | h4
            · rcases (by omega : m < 2555 ∨ 2555 ≤ m) with h5 | h5
              · exact cov_decode 27 2055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_5 m (by omega) (by omega)
              · exact cov_decode 27 2555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_6 m (by omega) (by omega)
            · rcases (by omega : m < 3555 ∨ 3555 ≤ m) with h5 | h5
              · exact cov_decode 27 3055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_7 m (by omega) (by omega)
              · rcases (by omega : m < 4055 ∨ 4055 ≤ m) with h6 | h6
                · exact cov_decode 27 3555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_8 m (by omega) (by omega)
                · exact cov_decode 27 4055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_9 m (by omega) (by omega)
        · rcases (by omega : m < 6555 ∨ 6555 ≤ m) with h3 | h3
          · rcases (by omega : m < 5555 ∨ 5555 ≤ m) with h4 | h4
            · rcases (by omega : m < 5055 ∨ 5055 ≤ m) with h5 | h5
              · exact cov_decode 27 4555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_10 m (by omega) (by omega)
              · exact cov_decode 27 5055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_11 m (by omega) (by omega)
            · rcases (by omega : m < 6055 ∨ 6055 ≤ m) with h5 | h5
              · exact cov_decode 27 5555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_12 m (by omega) (by omega)
              · exact cov_decode 27 6055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_13 m (by omega) (by omega)
          · rcases (by omega : m < 7555 ∨ 7555 ≤ m) with h4 | h4
            · rcases (by omega : m < 7055 ∨ 7055 ≤ m) with h5 | h5
              · exact cov_decode 27 6555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_14 m (by omega) (by omega)
              · exact cov_decode 27 7055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_15 m (by omega) (by omega)
            · rcases (by omega : m < 8055 ∨ 8055 ≤ m) with h5 | h5
              · exact cov_decode 27 7555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_16 m (by omega) (by omega)
              · rcases (by omega : m < 8555 ∨ 8555 ≤ m) with h6 | h6
                · exact cov_decode 27 8055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_17 m (by omega) (by omega)
                · exact cov_decode 27 8555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_18 m (by omega) (by omega)
      · rcases (by omega : m < 13555 ∨ 13555 ≤ m) with h2 | h2
        · rcases (by omega : m < 11055 ∨ 11055 ≤ m) with h3 | h3
          · rcases (by omega : m < 10055 ∨ 10055 ≤ m) with h4 | h4
            · rcases (by omega : m < 9555 ∨ 9555 ≤ m) with h5 | h5
              · exact cov_decode 27 9055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_19 m (by omega) (by omega)
              · exact cov_decode 27 9555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_20 m (by omega) (by omega)
            · rcases (by omega : m < 10555 ∨ 10555 ≤ m) with h5 | h5
              · exact cov_decode 27 10055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_21 m (by omega) (by omega)
              · exact cov_decode 27 10555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_22 m (by omega) (by omega)
          · rcases (by omega : m < 12055 ∨ 12055 ≤ m) with h4 | h4
            · rcases (by omega : m < 11555 ∨ 11555 ≤ m) with h5 | h5
              · exact cov_decode 27 11055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_23 m (by omega) (by omega)
              · exact cov_decode 27 11555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_24 m (by omega) (by omega)
            · rcases (by omega : m < 12555 ∨ 12555 ≤ m) with h5 | h5
              · exact cov_decode 27 12055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_25 m (by omega) (by omega)
              · rcases (by omega : m < 13055 ∨ 13055 ≤ m) with h6 | h6
                · exact cov_decode 27 12555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_26 m (by omega) (by omega)
                · exact cov_decode 27 13055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_27 m (by omega) (by omega)
        · rcases (by omega : m < 16055 ∨ 16055 ≤ m) with h3 | h3
          · rcases (by omega : m < 14555 ∨ 14555 ≤ m) with h4 | h4
            · rcases (by omega : m < 14055 ∨ 14055 ≤ m) with h5 | h5
              · exact cov_decode 27 13555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_28 m (by omega) (by omega)
              · exact cov_decode 27 14055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_29 m (by omega) (by omega)
            · rcases (by omega : m < 15055 ∨ 15055 ≤ m) with h5 | h5
              · exact cov_decode 27 14555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_30 m (by omega) (by omega)
              · rcases (by omega : m < 15555 ∨ 15555 ≤ m) with h6 | h6
                · exact cov_decode 27 15055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_31 m (by omega) (by omega)
                · exact cov_decode 27 15555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_32 m (by omega) (by omega)
          · rcases (by omega : m < 17055 ∨ 17055 ≤ m) with h4 | h4
            · rcases (by omega : m < 16555 ∨ 16555 ≤ m) with h5 | h5
              · exact cov_decode 27 16055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_33 m (by omega) (by omega)
              · exact cov_decode 27 16555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_34 m (by omega) (by omega)
            · rcases (by omega : m < 17555 ∨ 17555 ≤ m) with h5 | h5
              · exact cov_decode 27 17055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_35 m (by omega) (by omega)
              · rcases (by omega : m < 18055 ∨ 18055 ≤ m) with h6 | h6
                · exact cov_decode 27 17555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_36 m (by omega) (by omega)
                · exact cov_decode 27 18055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_37 m (by omega) (by omega)
    · rcases (by omega : m < 27555 ∨ 27555 ≤ m) with h1 | h1
      · rcases (by omega : m < 23055 ∨ 23055 ≤ m) with h2 | h2
        · rcases (by omega : m < 20555 ∨ 20555 ≤ m) with h3 | h3
          · rcases (by omega : m < 19555 ∨ 19555 ≤ m) with h4 | h4
            · rcases (by omega : m < 19055 ∨ 19055 ≤ m) with h5 | h5
              · exact cov_decode 27 18555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_38 m (by omega) (by omega)
              · exact cov_decode 27 19055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_39 m (by omega) (by omega)
            · rcases (by omega : m < 20055 ∨ 20055 ≤ m) with h5 | h5
              · exact cov_decode 27 19555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_40 m (by omega) (by omega)
              · exact cov_decode 27 20055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_41 m (by omega) (by omega)
          · rcases (by omega : m < 21555 ∨ 21555 ≤ m) with h4 | h4
            · rcases (by omega : m < 21055 ∨ 21055 ≤ m) with h5 | h5
              · exact cov_decode 27 20555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_42 m (by omega) (by omega)
              · exact cov_decode 27 21055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_43 m (by omega) (by omega)
            · rcases (by omega : m < 22055 ∨ 22055 ≤ m) with h5 | h5
              · exact cov_decode 27 21555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_44 m (by omega) (by omega)
              · rcases (by omega : m < 22555 ∨ 22555 ≤ m) with h6 | h6
                · exact cov_decode 27 22055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_45 m (by omega) (by omega)
                · exact cov_decode 27 22555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_46 m (by omega) (by omega)
        · rcases (by omega : m < 25055 ∨ 25055 ≤ m) with h3 | h3
          · rcases (by omega : m < 24055 ∨ 24055 ≤ m) with h4 | h4
            · rcases (by omega : m < 23555 ∨ 23555 ≤ m) with h5 | h5
              · exact cov_decode 27 23055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_47 m (by omega) (by omega)
              · exact cov_decode 27 23555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_48 m (by omega) (by omega)
            · rcases (by omega : m < 24555 ∨ 24555 ≤ m) with h5 | h5
              · exact cov_decode 27 24055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_49 m (by omega) (by omega)
              · exact cov_decode 27 24555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_50 m (by omega) (by omega)
          · rcases (by omega : m < 26055 ∨ 26055 ≤ m) with h4 | h4
            · rcases (by omega : m < 25555 ∨ 25555 ≤ m) with h5 | h5
              · exact cov_decode 27 25055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_51 m (by omega) (by omega)
              · exact cov_decode 27 25555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_52 m (by omega) (by omega)
            · rcases (by omega : m < 26555 ∨ 26555 ≤ m) with h5 | h5
              · exact cov_decode 27 26055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_53 m (by omega) (by omega)
              · rcases (by omega : m < 27055 ∨ 27055 ≤ m) with h6 | h6
                · exact cov_decode 27 26555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_54 m (by omega) (by omega)
                · exact cov_decode 27 27055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_55 m (by omega) (by omega)
      · rcases (by omega : m < 32055 ∨ 32055 ≤ m) with h2 | h2
        · rcases (by omega : m < 29555 ∨ 29555 ≤ m) with h3 | h3
          · rcases (by omega : m < 28555 ∨ 28555 ≤ m) with h4 | h4
            · rcases (by omega : m < 28055 ∨ 28055 ≤ m) with h5 | h5
              · exact cov_decode 27 27555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_56 m (by omega) (by omega)
              · exact cov_decode 27 28055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_57 m (by omega) (by omega)
            · rcases (by omega : m < 29055 ∨ 29055 ≤ m) with h5 | h5
              · exact cov_decode 27 28555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_58 m (by omega) (by omega)
              · exact cov_decode 27 29055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_59 m (by omega) (by omega)
          · rcases (by omega : m < 30555 ∨ 30555 ≤ m) with h4 | h4
            · rcases (by omega : m < 30055 ∨ 30055 ≤ m) with h5 | h5
              · exact cov_decode 27 29555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_60 m (by omega) (by omega)
              · exact cov_decode 27 30055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_61 m (by omega) (by omega)
            · rcases (by omega : m < 31055 ∨ 31055 ≤ m) with h5 | h5
              · exact cov_decode 27 30555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_62 m (by omega) (by omega)
              · rcases (by omega : m < 31555 ∨ 31555 ≤ m) with h6 | h6
                · exact cov_decode 27 31055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_63 m (by omega) (by omega)
                · exact cov_decode 27 31555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_64 m (by omega) (by omega)
        · rcases (by omega : m < 34555 ∨ 34555 ≤ m) with h3 | h3
          · rcases (by omega : m < 33055 ∨ 33055 ≤ m) with h4 | h4
            · rcases (by omega : m < 32555 ∨ 32555 ≤ m) with h5 | h5
              · exact cov_decode 27 32055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_65 m (by omega) (by omega)
              · exact cov_decode 27 32555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_66 m (by omega) (by omega)
            · rcases (by omega : m < 33555 ∨ 33555 ≤ m) with h5 | h5
              · exact cov_decode 27 33055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_67 m (by omega) (by omega)
              · rcases (by omega : m < 34055 ∨ 34055 ≤ m) with h6 | h6
                · exact cov_decode 27 33555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_68 m (by omega) (by omega)
                · exact cov_decode 27 34055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_69 m (by omega) (by omega)
          · rcases (by omega : m < 35555 ∨ 35555 ≤ m) with h4 | h4
            · rcases (by omega : m < 35055 ∨ 35055 ≤ m) with h5 | h5
              · exact cov_decode 27 34555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_70 m (by omega) (by omega)
              · exact cov_decode 27 35055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_71 m (by omega) (by omega)
            · rcases (by omega : m < 36055 ∨ 36055 ≤ m) with h5 | h5
              · exact cov_decode 27 35555 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_72 m (by omega) (by omega)
              · rcases (by omega : m < 36555 ∨ 36555 ≤ m) with h6 | h6
                · exact cov_decode 27 36055 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_73 m (by omega) (by omega)
                · exact cov_decode 27 36555 332 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_27_74 m (by omega) (by omega)
  exact final_helper 27 36887 [29, 31, 37, 41, 43, 47, 53] hpr hwin (by norm_num) (by norm_num) hw hcov

theorem erdos451_k28 : 2 * 28 < 36888 ∧
    (∀ q, q.Prime → 28 < q → q < 2 * 28 → ¬ q ∣ prodK 36888 28) ∧
    (∀ m, 2 * 28 < m → m < 36888 → ∃ q, q.Prime ∧ 28 < q ∧ q < 2 * 28 ∧ q ∣ prodK m 28) := by
  have hpr : ∀ q ∈ [29, 31, 37, 41, 43, 47, 53], q.Prime ∧ 28 < q ∧ q < 2 * 28 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact hfalse.elim
  have hwin : ∀ q, q.Prime → 28 < q → q < 2 * 28 → q ∈ [29, 31, 37, 41, 43, 47, 53] :=
    win_decode 28 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.win_28
  have hw : ∀ q ∈ [29, 31, 37, 41, 43, 47, 53], ¬ (1 ≤ 36888 % q ∧ 36888 % q ≤ 28) :=
    wit_decode 28 36888 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.w_28
  have hcov : ∀ m, 2 * 28 < m → m < 36888 → ∃ q ∈ [29, 31, 37, 41, 43, 47, 53], 1 ≤ m % q ∧ m % q ≤ 28 := by
    intro m hm1 hm2
    rcases (by omega : m < 18557 ∨ 18557 ≤ m) with h0 | h0
    · rcases (by omega : m < 9057 ∨ 9057 ≤ m) with h1 | h1
      · rcases (by omega : m < 4557 ∨ 4557 ≤ m) with h2 | h2
        · rcases (by omega : m < 2057 ∨ 2057 ≤ m) with h3 | h3
          · rcases (by omega : m < 1057 ∨ 1057 ≤ m) with h4 | h4
            · rcases (by omega : m < 557 ∨ 557 ≤ m) with h5 | h5
              · exact cov_decode 28 57 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_1 m (by omega) (by omega)
              · exact cov_decode 28 557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_2 m (by omega) (by omega)
            · rcases (by omega : m < 1557 ∨ 1557 ≤ m) with h5 | h5
              · exact cov_decode 28 1057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_3 m (by omega) (by omega)
              · exact cov_decode 28 1557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_4 m (by omega) (by omega)
          · rcases (by omega : m < 3057 ∨ 3057 ≤ m) with h4 | h4
            · rcases (by omega : m < 2557 ∨ 2557 ≤ m) with h5 | h5
              · exact cov_decode 28 2057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_5 m (by omega) (by omega)
              · exact cov_decode 28 2557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_6 m (by omega) (by omega)
            · rcases (by omega : m < 3557 ∨ 3557 ≤ m) with h5 | h5
              · exact cov_decode 28 3057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_7 m (by omega) (by omega)
              · rcases (by omega : m < 4057 ∨ 4057 ≤ m) with h6 | h6
                · exact cov_decode 28 3557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_8 m (by omega) (by omega)
                · exact cov_decode 28 4057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_9 m (by omega) (by omega)
        · rcases (by omega : m < 6557 ∨ 6557 ≤ m) with h3 | h3
          · rcases (by omega : m < 5557 ∨ 5557 ≤ m) with h4 | h4
            · rcases (by omega : m < 5057 ∨ 5057 ≤ m) with h5 | h5
              · exact cov_decode 28 4557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_10 m (by omega) (by omega)
              · exact cov_decode 28 5057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_11 m (by omega) (by omega)
            · rcases (by omega : m < 6057 ∨ 6057 ≤ m) with h5 | h5
              · exact cov_decode 28 5557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_12 m (by omega) (by omega)
              · exact cov_decode 28 6057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_13 m (by omega) (by omega)
          · rcases (by omega : m < 7557 ∨ 7557 ≤ m) with h4 | h4
            · rcases (by omega : m < 7057 ∨ 7057 ≤ m) with h5 | h5
              · exact cov_decode 28 6557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_14 m (by omega) (by omega)
              · exact cov_decode 28 7057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_15 m (by omega) (by omega)
            · rcases (by omega : m < 8057 ∨ 8057 ≤ m) with h5 | h5
              · exact cov_decode 28 7557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_16 m (by omega) (by omega)
              · rcases (by omega : m < 8557 ∨ 8557 ≤ m) with h6 | h6
                · exact cov_decode 28 8057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_17 m (by omega) (by omega)
                · exact cov_decode 28 8557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_18 m (by omega) (by omega)
      · rcases (by omega : m < 13557 ∨ 13557 ≤ m) with h2 | h2
        · rcases (by omega : m < 11057 ∨ 11057 ≤ m) with h3 | h3
          · rcases (by omega : m < 10057 ∨ 10057 ≤ m) with h4 | h4
            · rcases (by omega : m < 9557 ∨ 9557 ≤ m) with h5 | h5
              · exact cov_decode 28 9057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_19 m (by omega) (by omega)
              · exact cov_decode 28 9557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_20 m (by omega) (by omega)
            · rcases (by omega : m < 10557 ∨ 10557 ≤ m) with h5 | h5
              · exact cov_decode 28 10057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_21 m (by omega) (by omega)
              · exact cov_decode 28 10557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_22 m (by omega) (by omega)
          · rcases (by omega : m < 12057 ∨ 12057 ≤ m) with h4 | h4
            · rcases (by omega : m < 11557 ∨ 11557 ≤ m) with h5 | h5
              · exact cov_decode 28 11057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_23 m (by omega) (by omega)
              · exact cov_decode 28 11557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_24 m (by omega) (by omega)
            · rcases (by omega : m < 12557 ∨ 12557 ≤ m) with h5 | h5
              · exact cov_decode 28 12057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_25 m (by omega) (by omega)
              · rcases (by omega : m < 13057 ∨ 13057 ≤ m) with h6 | h6
                · exact cov_decode 28 12557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_26 m (by omega) (by omega)
                · exact cov_decode 28 13057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_27 m (by omega) (by omega)
        · rcases (by omega : m < 16057 ∨ 16057 ≤ m) with h3 | h3
          · rcases (by omega : m < 14557 ∨ 14557 ≤ m) with h4 | h4
            · rcases (by omega : m < 14057 ∨ 14057 ≤ m) with h5 | h5
              · exact cov_decode 28 13557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_28 m (by omega) (by omega)
              · exact cov_decode 28 14057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_29 m (by omega) (by omega)
            · rcases (by omega : m < 15057 ∨ 15057 ≤ m) with h5 | h5
              · exact cov_decode 28 14557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_30 m (by omega) (by omega)
              · rcases (by omega : m < 15557 ∨ 15557 ≤ m) with h6 | h6
                · exact cov_decode 28 15057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_31 m (by omega) (by omega)
                · exact cov_decode 28 15557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_32 m (by omega) (by omega)
          · rcases (by omega : m < 17057 ∨ 17057 ≤ m) with h4 | h4
            · rcases (by omega : m < 16557 ∨ 16557 ≤ m) with h5 | h5
              · exact cov_decode 28 16057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_33 m (by omega) (by omega)
              · exact cov_decode 28 16557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_34 m (by omega) (by omega)
            · rcases (by omega : m < 17557 ∨ 17557 ≤ m) with h5 | h5
              · exact cov_decode 28 17057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_35 m (by omega) (by omega)
              · rcases (by omega : m < 18057 ∨ 18057 ≤ m) with h6 | h6
                · exact cov_decode 28 17557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_36 m (by omega) (by omega)
                · exact cov_decode 28 18057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_37 m (by omega) (by omega)
    · rcases (by omega : m < 27557 ∨ 27557 ≤ m) with h1 | h1
      · rcases (by omega : m < 23057 ∨ 23057 ≤ m) with h2 | h2
        · rcases (by omega : m < 20557 ∨ 20557 ≤ m) with h3 | h3
          · rcases (by omega : m < 19557 ∨ 19557 ≤ m) with h4 | h4
            · rcases (by omega : m < 19057 ∨ 19057 ≤ m) with h5 | h5
              · exact cov_decode 28 18557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_38 m (by omega) (by omega)
              · exact cov_decode 28 19057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_39 m (by omega) (by omega)
            · rcases (by omega : m < 20057 ∨ 20057 ≤ m) with h5 | h5
              · exact cov_decode 28 19557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_40 m (by omega) (by omega)
              · exact cov_decode 28 20057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_41 m (by omega) (by omega)
          · rcases (by omega : m < 21557 ∨ 21557 ≤ m) with h4 | h4
            · rcases (by omega : m < 21057 ∨ 21057 ≤ m) with h5 | h5
              · exact cov_decode 28 20557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_42 m (by omega) (by omega)
              · exact cov_decode 28 21057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_43 m (by omega) (by omega)
            · rcases (by omega : m < 22057 ∨ 22057 ≤ m) with h5 | h5
              · exact cov_decode 28 21557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_44 m (by omega) (by omega)
              · rcases (by omega : m < 22557 ∨ 22557 ≤ m) with h6 | h6
                · exact cov_decode 28 22057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_45 m (by omega) (by omega)
                · exact cov_decode 28 22557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_46 m (by omega) (by omega)
        · rcases (by omega : m < 25057 ∨ 25057 ≤ m) with h3 | h3
          · rcases (by omega : m < 24057 ∨ 24057 ≤ m) with h4 | h4
            · rcases (by omega : m < 23557 ∨ 23557 ≤ m) with h5 | h5
              · exact cov_decode 28 23057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_47 m (by omega) (by omega)
              · exact cov_decode 28 23557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_48 m (by omega) (by omega)
            · rcases (by omega : m < 24557 ∨ 24557 ≤ m) with h5 | h5
              · exact cov_decode 28 24057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_49 m (by omega) (by omega)
              · exact cov_decode 28 24557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_50 m (by omega) (by omega)
          · rcases (by omega : m < 26057 ∨ 26057 ≤ m) with h4 | h4
            · rcases (by omega : m < 25557 ∨ 25557 ≤ m) with h5 | h5
              · exact cov_decode 28 25057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_51 m (by omega) (by omega)
              · exact cov_decode 28 25557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_52 m (by omega) (by omega)
            · rcases (by omega : m < 26557 ∨ 26557 ≤ m) with h5 | h5
              · exact cov_decode 28 26057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_53 m (by omega) (by omega)
              · rcases (by omega : m < 27057 ∨ 27057 ≤ m) with h6 | h6
                · exact cov_decode 28 26557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_54 m (by omega) (by omega)
                · exact cov_decode 28 27057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_55 m (by omega) (by omega)
      · rcases (by omega : m < 32057 ∨ 32057 ≤ m) with h2 | h2
        · rcases (by omega : m < 29557 ∨ 29557 ≤ m) with h3 | h3
          · rcases (by omega : m < 28557 ∨ 28557 ≤ m) with h4 | h4
            · rcases (by omega : m < 28057 ∨ 28057 ≤ m) with h5 | h5
              · exact cov_decode 28 27557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_56 m (by omega) (by omega)
              · exact cov_decode 28 28057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_57 m (by omega) (by omega)
            · rcases (by omega : m < 29057 ∨ 29057 ≤ m) with h5 | h5
              · exact cov_decode 28 28557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_58 m (by omega) (by omega)
              · exact cov_decode 28 29057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_59 m (by omega) (by omega)
          · rcases (by omega : m < 30557 ∨ 30557 ≤ m) with h4 | h4
            · rcases (by omega : m < 30057 ∨ 30057 ≤ m) with h5 | h5
              · exact cov_decode 28 29557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_60 m (by omega) (by omega)
              · exact cov_decode 28 30057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_61 m (by omega) (by omega)
            · rcases (by omega : m < 31057 ∨ 31057 ≤ m) with h5 | h5
              · exact cov_decode 28 30557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_62 m (by omega) (by omega)
              · rcases (by omega : m < 31557 ∨ 31557 ≤ m) with h6 | h6
                · exact cov_decode 28 31057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_63 m (by omega) (by omega)
                · exact cov_decode 28 31557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_64 m (by omega) (by omega)
        · rcases (by omega : m < 34557 ∨ 34557 ≤ m) with h3 | h3
          · rcases (by omega : m < 33057 ∨ 33057 ≤ m) with h4 | h4
            · rcases (by omega : m < 32557 ∨ 32557 ≤ m) with h5 | h5
              · exact cov_decode 28 32057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_65 m (by omega) (by omega)
              · exact cov_decode 28 32557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_66 m (by omega) (by omega)
            · rcases (by omega : m < 33557 ∨ 33557 ≤ m) with h5 | h5
              · exact cov_decode 28 33057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_67 m (by omega) (by omega)
              · rcases (by omega : m < 34057 ∨ 34057 ≤ m) with h6 | h6
                · exact cov_decode 28 33557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_68 m (by omega) (by omega)
                · exact cov_decode 28 34057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_69 m (by omega) (by omega)
          · rcases (by omega : m < 35557 ∨ 35557 ≤ m) with h4 | h4
            · rcases (by omega : m < 35057 ∨ 35057 ≤ m) with h5 | h5
              · exact cov_decode 28 34557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_70 m (by omega) (by omega)
              · exact cov_decode 28 35057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_71 m (by omega) (by omega)
            · rcases (by omega : m < 36057 ∨ 36057 ≤ m) with h5 | h5
              · exact cov_decode 28 35557 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_72 m (by omega) (by omega)
              · rcases (by omega : m < 36557 ∨ 36557 ≤ m) with h6 | h6
                · exact cov_decode 28 36057 500 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_73 m (by omega) (by omega)
                · exact cov_decode 28 36557 331 [29, 31, 37, 41, 43, 47, 53] Erdos451Data.c_28_74 m (by omega) (by omega)
  exact final_helper 28 36888 [29, 31, 37, 41, 43, 47, 53] hpr hwin (by norm_num) (by norm_num) hw hcov


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

/-! ## §9 THE ARSENAL BRIDGE PROPOSITION (the complete board's final
conjunct, in the #282 `erdos282_complete` pattern: the §8 bridge facts —
ternary digits of the k=10 witness 220, carry bounds at the k=20 and
k=12 witnesses 550 and 338, the composite-modulus reduction at the
k=20 window prime 23, the ternary scaling at 183 (550 - 1 = 3 * 183) —
packaged as one named `Prop` and EXTENDED with kernel-decided arithmetic
facts on four more witness numbers: the ternary digits of 65 (n_9) and
368 (n_19), and the carry bounds at 220 (n_10) and 113 (n_17). The
existing §8 theorem `erdos451_arsenal_bridge` closes the final
sub-conjunct verbatim; the extension is `by decide` plus the arsenal's
`carryAtPos_bound`.) -/

def arsenalBridgeProp : Prop :=
  [65 % 3, (65 / 3) % 3, (65 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  [368 % 3, (368 / 3) % 3, (368 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
  carryAtPos 220 1 < 4 ∧ carryAtPos 113 1 < 4 ∧
  ([220 % 3, (220 / 3) % 3, (220 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 550 1 < 4 ∧ carryAtPos 338 2 < 4 ∧
    (550 % (23 * 2)) % 23 = 550 % 23 ∧
    v2r (3 ^ 1 * 183) = v2r 183)

theorem erdos451_arsenal_bridge_full : arsenalBridgeProp :=
  ⟨by decide, by decide, carryAtPos_bound 220 1, carryAtPos_bound 113 1,
    erdos451_arsenal_bridge⟩

/-! ## §10 THE COMPLETE BOARD (the one-statement assembly of everything
this kernel delivers unconditionally, in the #282 `erdos282_complete`
pattern: the primality bridge §1, the two product-direction laws §2 and
§3, THE general modular criterion §4, and the nineteen witness-table
rows §7 (k = 2..20) stated EXACTLY as §7 states them, with the arsenal
bridge §9 as the final conjunct. Honest scope, unchanged: the general
asymptotics of n_k remain open and are NOT claimed; the §5 decode
toolkit and the §6 assembly helper stay proven in this file exactly as
they were — they are the machinery that manufactures the nineteen rows,
not laws of the problem, so they are not board conjuncts). -/

theorem erdos451_complete :
    (∀ q : Nat, q.Prime → isP q = true) ∧
    (∀ p : Nat, p.Prime → ∀ k n, p ∣ prodK n k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ p ∣ (n - j)) ∧
    (∀ j n k : Nat, 1 ≤ j → j ≤ k → ∀ p, p ∣ (n - j) → p ∣ prodK n k) ∧
    (∀ p k n : Nat, p.Prime → k < p → k ≤ n → (p ∣ prodK n k ↔ 1 ≤ n % p ∧ n % p ≤ k)) ∧
    (2 * 2 < 6 ∧
      (∀ q, q.Prime → 2 < q → q < 2 * 2 → ¬ q ∣ prodK 6 2) ∧
      (∀ m, 2 * 2 < m → m < 6 → ∃ q, q.Prime ∧ 2 < q ∧ q < 2 * 2 ∧ q ∣ prodK m 2)) ∧
    (2 * 3 < 9 ∧
      (∀ q, q.Prime → 3 < q → q < 2 * 3 → ¬ q ∣ prodK 9 3) ∧
      (∀ m, 2 * 3 < m → m < 9 → ∃ q, q.Prime ∧ 3 < q ∧ q < 2 * 3 ∧ q ∣ prodK m 3)) ∧
    (2 * 4 < 20 ∧
      (∀ q, q.Prime → 4 < q → q < 2 * 4 → ¬ q ∣ prodK 20 4) ∧
      (∀ m, 2 * 4 < m → m < 20 → ∃ q, q.Prime ∧ 4 < q ∧ q < 2 * 4 ∧ q ∣ prodK m 4)) ∧
    (2 * 5 < 13 ∧
      (∀ q, q.Prime → 5 < q → q < 2 * 5 → ¬ q ∣ prodK 13 5) ∧
      (∀ m, 2 * 5 < m → m < 13 → ∃ q, q.Prime ∧ 5 < q ∧ q < 2 * 5 ∧ q ∣ prodK m 5)) ∧
    (2 * 6 < 21 ∧
      (∀ q, q.Prime → 6 < q → q < 2 * 6 → ¬ q ∣ prodK 21 6) ∧
      (∀ m, 2 * 6 < m → m < 21 → ∃ q, q.Prime ∧ 6 < q ∧ q < 2 * 6 ∧ q ∣ prodK m 6)) ∧
    (2 * 7 < 21 ∧
      (∀ q, q.Prime → 7 < q → q < 2 * 7 → ¬ q ∣ prodK 21 7) ∧
      (∀ m, 2 * 7 < m → m < 21 → ∃ q, q.Prime ∧ 7 < q ∧ q < 2 * 7 ∧ q ∣ prodK m 7)) ∧
    (2 * 8 < 22 ∧
      (∀ q, q.Prime → 8 < q → q < 2 * 8 → ¬ q ∣ prodK 22 8) ∧
      (∀ m, 2 * 8 < m → m < 22 → ∃ q, q.Prime ∧ 8 < q ∧ q < 2 * 8 ∧ q ∣ prodK m 8)) ∧
    (2 * 9 < 65 ∧
      (∀ q, q.Prime → 9 < q → q < 2 * 9 → ¬ q ∣ prodK 65 9) ∧
      (∀ m, 2 * 9 < m → m < 65 → ∃ q, q.Prime ∧ 9 < q ∧ q < 2 * 9 ∧ q ∣ prodK m 9)) ∧
    (2 * 10 < 220 ∧
      (∀ q, q.Prime → 10 < q → q < 2 * 10 → ¬ q ∣ prodK 220 10) ∧
      (∀ m, 2 * 10 < m → m < 220 → ∃ q, q.Prime ∧ 10 < q ∧ q < 2 * 10 ∧ q ∣ prodK m 10)) ∧
    (2 * 11 < 51 ∧
      (∀ q, q.Prime → 11 < q → q < 2 * 11 → ¬ q ∣ prodK 51 11) ∧
      (∀ m, 2 * 11 < m → m < 51 → ∃ q, q.Prime ∧ 11 < q ∧ q < 2 * 11 ∧ q ∣ prodK m 11)) ∧
    (2 * 12 < 338 ∧
      (∀ q, q.Prime → 12 < q → q < 2 * 12 → ¬ q ∣ prodK 338 12) ∧
      (∀ m, 2 * 12 < m → m < 338 → ∃ q, q.Prime ∧ 12 < q ∧ q < 2 * 12 ∧ q ∣ prodK m 12)) ∧
    (2 * 13 < 133 ∧
      (∀ q, q.Prime → 13 < q → q < 2 * 13 → ¬ q ∣ prodK 133 13) ∧
      (∀ m, 2 * 13 < m → m < 133 → ∃ q, q.Prime ∧ 13 < q ∧ q < 2 * 13 ∧ q ∣ prodK m 13)) ∧
    (2 * 14 < 321 ∧
      (∀ q, q.Prime → 14 < q → q < 2 * 14 → ¬ q ∣ prodK 321 14) ∧
      (∀ m, 2 * 14 < m → m < 321 → ∃ q, q.Prime ∧ 14 < q ∧ q < 2 * 14 ∧ q ∣ prodK m 14)) ∧
    (2 * 15 < 339 ∧
      (∀ q, q.Prime → 15 < q → q < 2 * 15 → ¬ q ∣ prodK 339 15) ∧
      (∀ m, 2 * 15 < m → m < 339 → ∃ q, q.Prime ∧ 15 < q ∧ q < 2 * 15 ∧ q ∣ prodK m 15)) ∧
    (2 * 16 < 340 ∧
      (∀ q, q.Prime → 16 < q → q < 2 * 16 → ¬ q ∣ prodK 340 16) ∧
      (∀ m, 2 * 16 < m → m < 340 → ∃ q, q.Prime ∧ 16 < q ∧ q < 2 * 16 ∧ q ∣ prodK m 16)) ∧
    (2 * 17 < 113 ∧
      (∀ q, q.Prime → 17 < q → q < 2 * 17 → ¬ q ∣ prodK 113 17) ∧
      (∀ m, 2 * 17 < m → m < 113 → ∃ q, q.Prime ∧ 17 < q ∧ q < 2 * 17 ∧ q ∣ prodK m 17)) ∧
    (2 * 18 < 114 ∧
      (∀ q, q.Prime → 18 < q → q < 2 * 18 → ¬ q ∣ prodK 114 18) ∧
      (∀ m, 2 * 18 < m → m < 114 → ∃ q, q.Prime ∧ 18 < q ∧ q < 2 * 18 ∧ q ∣ prodK m 18)) ∧
    (2 * 19 < 368 ∧
      (∀ q, q.Prime → 19 < q → q < 2 * 19 → ¬ q ∣ prodK 368 19) ∧
      (∀ m, 2 * 19 < m → m < 368 → ∃ q, q.Prime ∧ 19 < q ∧ q < 2 * 19 ∧ q ∣ prodK m 19)) ∧
    (2 * 20 < 550 ∧
      (∀ q, q.Prime → 20 < q → q < 2 * 20 → ¬ q ∣ prodK 550 20) ∧
      (∀ m, 2 * 20 < m → m < 550 → ∃ q, q.Prime ∧ 20 < q ∧ q < 2 * 20 ∧ q ∣ prodK m 20)) ∧
    arsenalBridgeProp :=
  ⟨fun q hq => isP_of_prime q hq,
   fun p hp k n hdvd => prime_dvd_prodK p hp k n hdvd,
   fun j n k hj1 hjk p hpdiv => dvd_prodK_factor j n k hj1 hjk p hpdiv,
   fun p k n hp hk hkn => erdos451_crit p k n hp hk hkn,
   erdos451_k2,
   erdos451_k3,
   erdos451_k4,
   erdos451_k5,
   erdos451_k6,
   erdos451_k7,
   erdos451_k8,
   erdos451_k9,
   erdos451_k10,
   erdos451_k11,
   erdos451_k12,
   erdos451_k13,
   erdos451_k14,
   erdos451_k15,
   erdos451_k16,
   erdos451_k17,
   erdos451_k18,
   erdos451_k19,
   erdos451_k20,
   erdos451_arsenal_bridge_full⟩

#eval "ERDOS451_COMPLETE_GREEN"
#print axioms erdos451_complete
#print axioms arsenalBridgeProp
#print axioms erdos451_arsenal_bridge_full

/-! ## §11 THE W63 EXTENSION COMPLETE BOARD (the one-statement assembly
of the W62+W63 extension volley, in the §10 `erdos451_complete` pattern: the
four general laws + the eight rows k = 21..28 stated EXACTLY as §7b states
them + the arsenal bridge §9 — together with §10 this boards the certified
frontier k = 2..28 unconditionally. Honest scope unchanged: the general
asymptotics of n_k remain open and are NOT claimed.) -/
theorem erdos451_complete_ext :
    (∀ q : Nat, q.Prime → isP q = true) ∧
    (∀ p : Nat, p.Prime → ∀ k n, p ∣ prodK n k → ∃ j, 1 ≤ j ∧ j ≤ k ∧ p ∣ (n - j)) ∧
    (∀ j n k : Nat, 1 ≤ j → j ≤ k → ∀ p, p ∣ (n - j) → p ∣ prodK n k) ∧
    (∀ p k n : Nat, p.Prime → k < p → k ≤ n → (p ∣ prodK n k ↔ 1 ≤ n % p ∧ n % p ≤ k)) ∧
    (2 * 21 < 805 ∧
      (∀ q, q.Prime → 21 < q → q < 2 * 21 → ¬ q ∣ prodK 805 21) ∧
      (∀ m, 2 * 21 < m → m < 805 → ∃ q, q.Prime ∧ 21 < q ∧ q < 2 * 21 ∧ q ∣ prodK m 21)) ∧
    (2 * 22 < 2691 ∧
      (∀ q, q.Prime → 22 < q → q < 2 * 22 → ¬ q ∣ prodK 2691 22) ∧
      (∀ m, 2 * 22 < m → m < 2691 → ∃ q, q.Prime ∧ 22 < q ∧ q < 2 * 22 ∧ q ∣ prodK m 22)) ∧
    (2 * 23 < 1884 ∧
      (∀ q, q.Prime → 23 < q → q < 2 * 23 → ¬ q ∣ prodK 1884 23) ∧
      (∀ m, 2 * 23 < m → m < 1884 → ∃ q, q.Prime ∧ 23 < q ∧ q < 2 * 23 ∧ q ∣ prodK m 23)) ∧
    (2 * 24 < 2664 ∧
      (∀ q, q.Prime → 24 < q → q < 2 * 24 → ¬ q ∣ prodK 2664 24) ∧
      (∀ m, 2 * 24 < m → m < 2664 → ∃ q, q.Prime ∧ 24 < q ∧ q < 2 * 24 ∧ q ∣ prodK m 24)) ∧
    (2 * 25 < 7653 ∧
      (∀ q, q.Prime → 25 < q → q < 2 * 25 → ¬ q ∣ prodK 7653 25) ∧
      (∀ m, 2 * 25 < m → m < 7653 → ∃ q, q.Prime ∧ 25 < q ∧ q < 2 * 25 ∧ q ∣ prodK m 25)) ∧
    (2 * 26 < 7654 ∧
      (∀ q, q.Prime → 26 < q → q < 2 * 26 → ¬ q ∣ prodK 7654 26) ∧
      (∀ m, 2 * 26 < m → m < 7654 → ∃ q, q.Prime ∧ 26 < q ∧ q < 2 * 26 ∧ q ∣ prodK m 26)) ∧
    (2 * 27 < 36887 ∧
      (∀ q, q.Prime → 27 < q → q < 2 * 27 → ¬ q ∣ prodK 36887 27) ∧
      (∀ m, 2 * 27 < m → m < 36887 → ∃ q, q.Prime ∧ 27 < q ∧ q < 2 * 27 ∧ q ∣ prodK m 27)) ∧
    (2 * 28 < 36888 ∧
      (∀ q, q.Prime → 28 < q → q < 2 * 28 → ¬ q ∣ prodK 36888 28) ∧
      (∀ m, 2 * 28 < m → m < 36888 → ∃ q, q.Prime ∧ 28 < q ∧ q < 2 * 28 ∧ q ∣ prodK m 28)) ∧
    arsenalBridgeProp :=
  ⟨fun q hq => isP_of_prime q hq,
   fun p hp k n hdvd => prime_dvd_prodK p hp k n hdvd,
   fun j n k hj1 hjk p hpdiv => dvd_prodK_factor j n k hj1 hjk p hpdiv,
   fun p k n hp hk hkn => erdos451_crit p k n hp hk hkn,
   erdos451_k21,
   erdos451_k22,
   erdos451_k23,
   erdos451_k24,
   erdos451_k25,
   erdos451_k26,
   erdos451_k27,
   erdos451_k28,
   erdos451_arsenal_bridge_full⟩

#eval "ERDOS451_FRONTIER_EXT_GREEN"
#print axioms erdos451_k21
#print axioms erdos451_k22
#print axioms erdos451_k23
#print axioms erdos451_k24
#print axioms erdos451_k25
#print axioms erdos451_k26
#print axioms erdos451_k27
#print axioms erdos451_k28
#print axioms erdos451_complete_ext

end Erdos451
