import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos389 — THE CONSECUTIVE-PRODUCT KERNEL (Kernel 67, W59-B-2)

Erdős #389 (open): for every n ≥ 1 does there exist k ≥ 1 with
n(n+1)···(n+k−1) ∣ (n+k)···(n+2k−1)?  The python engine bank of this
directory certified the minimal-k table k(1..11) = A375071 = 1, 5, 4, 207,
206, 2475, 984, 8171, 8170, 45144, 45143 (engine389.py + engine389b.py +
battery389.py, two-method cross-check, 93/93 GREEN); the deep scan
(scan389_deep.txt) adds k(12) = 3648830, k(13) = 3648829, k(14) = 7979077,
k(15) = 7979076 and NO k ≤ 10^7 for n = 16..18.  This kernel certifies:

* **HABITAT:** `prodRange` (the consecutive product), `countQ` (the
  window's multiple-count), `mCount` (the capped q-adic depth of one
  integer), `countChain` (Σ_e countQ (q^e) n k), `depthSum` (Σ_i capped
  element depths), `failRow` (the battery's Bool exclusion mirror).
* **WITNESS TABLE:** all eleven A375071 rows as closed-term `∣`-decides —
  720 ∣ 55440 (n=2,k=5); 360 ∣ 5040 (n=3,k=4); the ≈10^397-digit blocks
  (n=4,k=207 / n=5,k=206); n=6,k=2475; n=7,k=984; n=8,k=8171; n=9,k=8170;
  the ≈2·10^5-digit blocks n=10,k=45144 and n=11,k=45143, kernel-exact.
* **MINIMAL-K CENSUS (n ≤ 7):** works at k(n) and every 1 ≤ j < k(n) fails
  — failRow sweeps over [0, k(n)) chunked ≤ 500 rows per theorem (the
  NO-OOM law), consumed into full minimality theorems.
* **COUNT LAWS:** countQ monotonicity; the mod-shift congruence; THE SHIFT
  LAW (q ∣ k → the two k-blocks carry the SAME q-count); THE SWAP LAW
  (countChain = depthSum); THE CROWN LAW (q^e ∣ k for all 1 ≤ e ≤ E →
  q^countChain divides the RIGHT block (n+k)···(n+2k−1)).

Honest scope: the count-soundness direction and the n ≥ 6 minimality rows
(k(n) > 5000) stay the campaign's open lane; the n = 12..18 deep-scan rows
are battery-only.  Laws obeyed: zero sorry/admit/native_decide; decide only
on closed terms (bounded List.range sweeps ≤ 500 — never `∀ k < N` for
N > 501); `∣`-decidability only through the core Nat instances; mod
arithmetic via the CI-green Nat chain (add_mod/mul_mod/mod_self/
zero_mul/zero_mod/mod_mod — the draft's unverified `Nat.mul_mod_right`
route replaced); divisibility witnesses on the right; omega only on
consistent atoms (ite heads split by by_cases first).-/

namespace E389

/-! ## §1 The habitat (equation-compiler native folds). -/

/-- `prodRange n k` = n(n+1)···(n+k−1), the left block of #389 at window k. -/
def prodRange (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n + k) * prodRange n k

theorem prodRange_zero (n : Nat) : prodRange n 0 = 1 := rfl

theorem prodRange_succ (n k : Nat) : prodRange n (k + 1) = (n + k) * prodRange n k := rfl

/-- `countQ q n k` = #{i ∈ [n, n+k) : q ∣ i} — multiples of q in the window. -/
def countQ (q n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if (n + k) % q = 0 then 1 else 0) + countQ q n k

theorem countQ_zero (q n : Nat) : countQ q n 0 = 0 := rfl

theorem countQ_succ (q n k : Nat) : countQ q n (k + 1) = (if (n + k) % q = 0 then 1 else 0) + countQ q n k := rfl

/-- `mCount q m E` = #{e ∈ [1,E] : q^e ∣ m} — the capped q-adic depth of m
(the 0- and E+1-equations are rfl). -/
def mCount (q m : Nat) : Nat → Nat
  | 0 => 0
  | E + 1 => (if m % q ^ (E + 1) = 0 then 1 else 0) + mCount q m E

/-- `countChain q n k E` = Σ_{e=1}^{E} countQ (q^e) n k — the power-stacked
block chain (fold over E; equations rfl). -/
def countChain (q n k : Nat) : Nat → Nat
  | 0 => 0
  | E + 1 => countQ (q ^ (E + 1)) n k + countChain q n k E

/-- `depthSum q n E k` = Σ_{i<k} mCount q (n+i) E — the same chain summed
element-first (the swap partner; fold over k; equations rfl). -/
def depthSum (q n E : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mCount q (n + k) E + depthSum q n E k

/-- `failRow n j` = true iff j = 0 (outside the k ≥ 1 domain) or the j-window fails. -/
def failRow (n j : Nat) : Bool :=
  decide (j = 0 ∨ prodRange (n + j) j % prodRange n j ≠ 0)

/-! ## §2 The count laws (structural — THE MODULAR CORE). -/

/-- **MONOTONICITY:** widening the window never drops the count. -/
theorem e389_count_mono : ∀ q n k : Nat, countQ q n k ≤ countQ q n (k + 1) := by
  intro q n k
  have e1 : countQ q n (k + 1) = (if (n + k) % q = 0 then 1 else 0) + countQ q n k := rfl
  rw [e1]
  by_cases hmod : (n + k) % q = 0
  · rw [if_pos hmod]
    omega
  · rw [if_neg hmod]
    omega

/-- Every product is a multiple of its own modulus (the Erdos700 chain). -/
theorem e389_mul_mod_self (q t : Nat) : q * t % q = 0 := by
  rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

/-- **THE MOD-SHIFT CONGRUENCE:** s = q·t → (a + q·t) % q = a % q. -/
theorem e389_mod_shift (a t q : Nat) : (a + q * t) % q = a % q := by
  have h1 := Nat.add_mod a (q * t) q
  have h2 : q * t % q = 0 := e389_mul_mod_self q t
  rw [h1, h2, Nat.add_zero, Nat.mod_mod]

/-- **THE GENERAL SHIFT:** q ∣ s → the window [n, n+m) and its s-translate
carry the SAME q-count. -/
theorem e389_count_shift (q s : Nat) (hs : q ∣ s) :
    ∀ n m : Nat, countQ q n m = countQ q (n + s) m := by
  obtain ⟨t, ht⟩ := hs
  intro n m
  induction m with
  | zero => rfl
  | succ j ih =>
      have e1 : countQ q n (j + 1) = (if (n + j) % q = 0 then 1 else 0) + countQ q n j := rfl
      have e2 : countQ q (n + s) (j + 1) = (if (n + s + j) % q = 0 then 1 else 0) + countQ q (n + s) j := rfl
      have hmod' : (n + s + j) % q = (n + j) % q := by
        have hcomm : n + s + j = n + j + s := by omega
        rw [hcomm, ht]
        exact e389_mod_shift (n + j) t q
      rw [e1, e2, hmod', ih]

/-- **THE SHIFT LAW (the symmetry core of #389):** q ∣ k → the two k-blocks
[n, n+k) and [n+k, n+2k) carry the SAME q-count. -/
theorem e389_shift_law :
    ∀ q n k : Nat, q ∣ k → countQ q n k = countQ q (n + k) k := by
  intro q n k hd
  exact e389_count_shift q k hd n k

/-- **THE FAILROW BRIDGE:** a true failRow at nonzero j is a genuine exclusion. -/
theorem failRow_true_ne (n j : Nat) (h1 : ¬(j = 0)) (h : failRow n j = true) :
    ¬(prodRange n j ∣ prodRange (n + j) j) := by
  have hp : j = 0 ∨ prodRange (n + j) j % prodRange n j ≠ 0 := of_decide_eq_true h
  rcases hp with h0 | hne
  · exact absurd h0 h1
  · intro hdvd
    exact hne (Nat.mod_eq_zero_of_dvd hdvd)

/-! ## §3 The chain layer (structural — THE CROWN CORE). -/

/-- Powers divide powers upward: e ≤ f → q^e ∣ q^f. -/
theorem e389_pow_le_dvd (q e f : Nat) (h : e ≤ f) : q ^ e ∣ q ^ f := by
  obtain ⟨j, hj⟩ : ∃ j : Nat, f = e + j := ⟨f - e, by omega⟩
  rw [hj]
  exact ⟨q ^ j, Nat.pow_add q e j⟩

/-- A fully-divisible depth count is full: q^e ∣ m for all 1 ≤ e ≤ E →
mCount = E (all indicator rows fire). -/
theorem e389_mCount_full : ∀ (q m E : Nat),
    (∀ e : Nat, 1 ≤ e → e ≤ E → q ^ e ∣ m) → mCount q m E = E := by
  intro q m E
  induction E with
  | zero => intro _; rfl
  | succ E ih =>
      intro hq
      have hstep : mCount q m (E + 1) =
          (if m % q ^ (E + 1) = 0 then 1 else 0) + mCount q m E := rfl
      have hdvd : q ^ (E + 1) ∣ m := hq (E + 1) (by omega) (by omega)
      have hmod : m % q ^ (E + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hstep, if_pos hmod, ih (fun e h1 h2 => hq e h1 (by omega))]
      omega

/-- **THE DEPTH LAW:** q ^ mCount q m E ∣ m — the capped depth never
overshoots. -/
theorem e389_depth_dvd : ∀ (q m E : Nat), q ^ mCount q m E ∣ m := by
  intro q m E
  induction E with
  | zero =>
      have h0 : mCount q m 0 = 0 := rfl
      rw [h0, Nat.pow_zero]
      exact ⟨m, (Nat.one_mul m).symm⟩
  | succ E ih =>
      by_cases hmod : m % q ^ (E + 1) = 0
      · have hdvd : q ^ (E + 1) ∣ m := Nat.dvd_of_mod_eq_zero hmod
        have hfull : mCount q m (E + 1) = E + 1 :=
          e389_mCount_full q m (E + 1)
            (fun e h1 h2 => Nat.dvd_trans (e389_pow_le_dvd q e (E + 1) h2) hdvd)
        rw [hfull]
        exact hdvd
      · have hstep : mCount q m (E + 1) =
            (if m % q ^ (E + 1) = 0 then 1 else 0) + mCount q m E := rfl
        rw [hstep, if_neg hmod, Nat.zero_add]
        exact ih

/-- **THE CHAIN-POWER LAW:** q ^ depthSum q n E k ∣ prodRange n k — the
element-sum of capped depths is carried by the block product. -/
theorem e389_chain_dvd : ∀ (q n E k : Nat), q ^ depthSum q n E k ∣ prodRange n k := by
  intro q n E k
  induction k with
  | zero =>
      have h0 : depthSum q n E 0 = 0 := rfl
      have h1 : prodRange n 0 = 1 := rfl
      rw [h0, h1, Nat.pow_zero]
      exact Nat.dvd_refl 1
  | succ k ih =>
      have hd : depthSum q n E (k + 1) = mCount q (n + k) E + depthSum q n E k := rfl
      have hp : prodRange n (k + 1) = (n + k) * prodRange n k := rfl
      have hmc : q ^ mCount q (n + k) E ∣ n + k := e389_depth_dvd q (n + k) E
      rw [hd, hp, Nat.pow_add]
      exact Nat.mul_dvd_mul hmc ih

/-- The chain unfolds row-by-row in the window (E-induction inside). -/
theorem e389_chain_step : ∀ (q n k E : Nat),
    countChain q n (k + 1) E = countChain q n k E + mCount q (n + k) E := by
  intro q n k E
  induction E with
  | zero => rfl
  | succ E ih =>
      have c1 : countChain q n (k + 1) (E + 1) =
          countQ (q ^ (E + 1)) n (k + 1) + countChain q n (k + 1) E := rfl
      have c2 : countChain q n k (E + 1) =
          countQ (q ^ (E + 1)) n k + countChain q n k E := rfl
      have c3 : mCount q (n + k) (E + 1) =
          (if (n + k) % q ^ (E + 1) = 0 then 1 else 0) + mCount q (n + k) E := rfl
      have c4 : countQ (q ^ (E + 1)) n (k + 1) =
          (if (n + k) % q ^ (E + 1) = 0 then 1 else 0) + countQ (q ^ (E + 1)) n k := rfl
      rw [c1, c2, c3, c4, ih]
      by_cases hmod : (n + k) % q ^ (E + 1) = 0
      · rw [if_pos hmod]
        omega
      · rw [if_neg hmod]
        omega

/-- The empty window carries no chain. -/
theorem e389_chain_zero : ∀ (q n : Nat), ∀ E : Nat, countChain q n 0 E = 0 := by
  intro q n E
  induction E with
  | zero => rfl
  | succ E ih =>
      have h1 : countChain q n 0 (E + 1) = countQ (q ^ (E + 1)) n 0 + countChain q n 0 E := rfl
      have h2 : countQ (q ^ (E + 1)) n 0 = 0 := rfl
      rw [h1, h2, ih]

/-- **THE SWAP LAW:** countChain q n k E = depthSum q n E k — the chain and
the element sum count the same pairs {(i,e) : i < k, 1 ≤ e ≤ E, q^e ∣ n+i}
twice (the battery's chain identity). -/
theorem e389_swap : ∀ (q n k E : Nat), countChain q n k E = depthSum q n E k := by
  intro q n k E
  induction k with
  | zero => exact e389_chain_zero q n E
  | succ k ih =>
      have h1 : countChain q n (k + 1) E = countChain q n k E + mCount q (n + k) E :=
        e389_chain_step q n k E
      have h2 : depthSum q n E (k + 1) = mCount q (n + k) E + depthSum q n E k := rfl
      rw [h1, h2, ih]
      omega

/-- **THE CHAIN-SHIFT:** q^e ∣ k for all 1 ≤ e ≤ E → the two k-blocks carry
the SAME chain. -/
theorem e389_chain_shift (q n k : Nat) : ∀ E : Nat,
    (∀ e : Nat, 1 ≤ e → e ≤ E → q ^ e ∣ k) →
    countChain q n k E = countChain q (n + k) k E := by
  intro E
  induction E with
  | zero => intro _; rfl
  | succ E ih =>
      intro hq
      have h1 : countChain q n k (E + 1) = countQ (q ^ (E + 1)) n k + countChain q n k E := rfl
      have h2 : countChain q (n + k) k (E + 1) =
          countQ (q ^ (E + 1)) (n + k) k + countChain q (n + k) k E := rfl
      have hrow : countQ (q ^ (E + 1)) n k = countQ (q ^ (E + 1)) (n + k) k :=
        e389_shift_law (q ^ (E + 1)) n k (hq (E + 1) (by omega) (by omega))
      rw [h1, h2, hrow, ih (fun e he1 he2 => hq e he1 (by omega))]

/-- **THE CROWN LAW (the kernel's crown):** q^e ∣ k for all 1 ≤ e ≤ E →
q ^ countChain q n k E ∣ the RIGHT block (n+k)···(n+2k−1). -/
theorem e389_crown (q n k E : Nat)
    (hq : ∀ e : Nat, 1 ≤ e → e ≤ E → q ^ e ∣ k) :
    q ^ countChain q n k E ∣ prodRange (n + k) k := by
  have h1 : countChain q n k E = countChain q (n + k) k E := e389_chain_shift q n k E hq
  have h2 : countChain q (n + k) k E = depthSum q (n + k) E k := e389_swap q (n + k) k E
  rw [h1, h2]
  exact e389_chain_dvd q (n + k) E k

/-! ## §4 The witness tables (closed-term decides; B1–B3 of the battery). -/

/-- THE HABITAT VALUES: the two corpus witnesses' blocks in the small. -/
theorem e389_habitat_values :
    prodRange 2 5 = 720 ∧ prodRange 7 5 = 55440 ∧
    prodRange 3 4 = 360 ∧ prodRange 7 4 = 5040 := by decide

/-- **WITNESS (n=2, k=5):** 720 ∣ 55440 (55440 = 77 · 720). -/
theorem e389_witness_2_5 : prodRange 2 5 ∣ prodRange 7 5 := by decide

/-- **WITNESS (n=3, k=4):** 360 ∣ 5040 (5040 = 14 · 360). -/
theorem e389_witness_3_4 : prodRange 3 4 ∣ prodRange 7 4 := by decide

/-- **WITNESS (n=4, k=207):** the 207-wide block 4···210 (≈10^397 digits) divides 211···417. -/
theorem e389_witness_4_207 : prodRange 4 207 ∣ prodRange 211 207 := by decide

/-- **WITNESS (n=5, k=206):** the 206-wide block 5···210 divides 211···416. -/
theorem e389_witness_5_206 : prodRange 5 206 ∣ prodRange 211 206 := by decide

/-- **WITNESS (n=6, k=2475):** the 2475-wide block 6···2480 divides 2481···4955. -/
theorem e389_witness_6_2475 : prodRange 6 2475 ∣ prodRange 2481 2475 := by decide

/-- **WITNESS (n=7, k=984):** the 984-wide block 7···990 divides 991···1974. -/
theorem e389_witness_7_984 : prodRange 7 984 ∣ prodRange 991 984 := by decide

/-- **WITNESS (n=8, k=8171):** the 8171-wide block 8···8178 divides 8179···16349. -/
theorem e389_witness_8_8171 : prodRange 8 8171 ∣ prodRange 8179 8171 := by decide

/-- **WITNESS (n=9, k=8170):** the 8170-wide block 9···8178 divides 8179···16348. -/
theorem e389_witness_9_8170 : prodRange 9 8170 ∣ prodRange 8179 8170 := by decide

/-- **WITNESS (n=10, k=45144):** the 45144-wide block 10···45153 divides
45154···90297 (≈2.1·10^5 digits — the heaviest decide here). -/
theorem e389_witness_10_45144 : prodRange 10 45144 ∣ prodRange 45154 45144 := by decide

/-- **WITNESS (n=11, k=45143):** the 45143-wide block 11···45153 divides 45154···90296. -/
theorem e389_witness_11_45143 : prodRange 11 45143 ∣ prodRange 45154 45143 := by decide

/-- **WITNESS (n=1, k=1):** the 1-wide block at n=1 divides the 1-wide block at n=2. -/
theorem e389_witness_1_1 : prodRange 1 1 ∣ prodRange 2 1 := by decide

/-- THE QUOTIENT / RESIDUE / DEFICIT RECEIPTS: the quotients (77, 14), the
near-miss residues (24, 36), and the deficit primes of those misses. -/
theorem e389_quotient_residues :
    prodRange 7 5 / prodRange 2 5 = 77 ∧ prodRange 7 4 / prodRange 3 4 = 14 ∧
    prodRange 6 4 % prodRange 2 4 = 24 ∧ prodRange 6 3 % prodRange 3 3 = 36 ∧
    (5 ∣ prodRange 2 4 ∧ ¬(5 ∣ prodRange 6 4)) ∧
    (5 ∣ prodRange 3 3 ∧ ¬(5 ∣ prodRange 6 3)) := by decide

/-! ## §5 The minimal-k census (failRow sweeps, chunked ≤ 500 — B4/B8). -/

theorem e389_sweep_1 : (List.range 1).all (fun j => failRow 1 j) = true := by decide
theorem e389_sweep_2 : (List.range 5).all (fun j => failRow 2 j) = true := by decide
theorem e389_sweep_3 : (List.range 4).all (fun j => failRow 3 j) = true := by decide
theorem e389_sweep_4 : (List.range 207).all (fun j => failRow 4 j) = true := by decide
theorem e389_sweep_5 : (List.range 206).all (fun j => failRow 5 j) = true := by decide

/-- THE n=6 SWEEP (k = 2475, five ≤ 500 chunks over [0, 2475)). -/
theorem e389_sweep_6a : (List.range 500).all (fun i => failRow 6 i) = true := by decide
theorem e389_sweep_6b : (List.range 500).all (fun i => failRow 6 (500 + i)) = true := by decide
theorem e389_sweep_6c : (List.range 500).all (fun i => failRow 6 (1000 + i)) = true := by decide
theorem e389_sweep_6d : (List.range 500).all (fun i => failRow 6 (1500 + i)) = true := by decide
theorem e389_sweep_6e : (List.range 475).all (fun i => failRow 6 (2000 + i)) = true := by decide

/-- THE n=7 SWEEP (k = 984, two ≤ 500 chunks over [0, 984)). -/
theorem e389_sweep_7a : (List.range 500).all (fun i => failRow 7 i) = true := by decide
theorem e389_sweep_7b : (List.range 484).all (fun i => failRow 7 (500 + i)) = true := by decide

/-- THE n=6 CHUNK ASSEMBLY: every j < 2475 carries a true failRow. -/
theorem e389_min_value_6 : ∀ j : Nat, j < 2475 → failRow 6 j = true := by
  intro j hj
  rcases (show j < 500 ∨ (500 ≤ j ∧ j < 1000) ∨ (1000 ≤ j ∧ j < 1500) ∨ (1500 ≤ j ∧ j < 2000) ∨ 2000 ≤ j by omega) with h | ⟨h, hu⟩ | ⟨h, hu⟩ | ⟨h, hu⟩ | h
  · exact (List.all_eq_true.mp e389_sweep_6a) j (List.mem_range.mpr h)
  · have hrow := (List.all_eq_true.mp e389_sweep_6b) (j - 500) (List.mem_range.mpr (show j - 500 < 500 by omega))
    have hj' : 500 + (j - 500) = j := by omega
    rw [hj'] at hrow
    exact hrow
  · have hrow := (List.all_eq_true.mp e389_sweep_6c) (j - 1000) (List.mem_range.mpr (show j - 1000 < 500 by omega))
    have hj' : 1000 + (j - 1000) = j := by omega
    rw [hj'] at hrow
    exact hrow
  · have hrow := (List.all_eq_true.mp e389_sweep_6d) (j - 1500) (List.mem_range.mpr (show j - 1500 < 500 by omega))
    have hj' : 1500 + (j - 1500) = j := by omega
    rw [hj'] at hrow
    exact hrow
  · have hrow := (List.all_eq_true.mp e389_sweep_6e) (j - 2000) (List.mem_range.mpr (show j - 2000 < 475 by omega))
    have hj' : 2000 + (j - 2000) = j := by omega
    rw [hj'] at hrow
    exact hrow

/-- THE n=7 CHUNK ASSEMBLY: every j < 984 carries a true failRow. -/
theorem e389_min_value_7 : ∀ j : Nat, j < 984 → failRow 7 j = true := by
  intro j hj
  rcases (show j < 500 ∨ 500 ≤ j by omega) with h | h
  · exact (List.all_eq_true.mp e389_sweep_7a) j (List.mem_range.mpr h)
  · have hrow := (List.all_eq_true.mp e389_sweep_7b) (j - 500) (List.mem_range.mpr (show j - 500 < 484 by omega))
    have hj' : 500 + (j - 500) = j := by omega
    rw [hj'] at hrow
    exact hrow

/-- **k(1) = 1 (the full census at n=1):** works at 1; nothing below 1 can fail. -/
theorem e389_minimal_1 :
    prodRange 1 1 ∣ prodRange 2 1 ∧
    ∀ j : Nat, 1 ≤ j → j < 1 → ¬(prodRange 1 j ∣ prodRange (1 + j) j) :=
  ⟨e389_witness_1_1, fun j h1 hj => absurd h1 (by omega)⟩

/-- **k(2) = 5 (the full census at n=2):** k=5 works and every shorter window fails. -/
theorem e389_minimal_2 :
    prodRange 2 5 ∣ prodRange 7 5 ∧
    ∀ j : Nat, 1 ≤ j → j < 5 → ¬(prodRange 2 j ∣ prodRange (2 + j) j) :=
  ⟨e389_witness_2_5, fun j h1 hj =>
    failRow_true_ne 2 j (by omega)
      ((List.all_eq_true.mp e389_sweep_2) j (List.mem_range.mpr hj))⟩

/-- **k(3) = 4 (the full census at n=3):** 3 ∤ 4; 12 ∤ 30; 60 ∤ 336. -/
theorem e389_minimal_3 :
    prodRange 3 4 ∣ prodRange 7 4 ∧
    ∀ j : Nat, 1 ≤ j → j < 4 → ¬(prodRange 3 j ∣ prodRange (3 + j) j) :=
  ⟨e389_witness_3_4, fun j h1 hj =>
    failRow_true_ne 3 j (by omega)
      ((List.all_eq_true.mp e389_sweep_3) j (List.mem_range.mpr hj))⟩

/-- **k(4) = 207 (the full census at n=4):** every 1 ≤ j < 207 fails. -/
theorem e389_minimal_4 :
    prodRange 4 207 ∣ prodRange 211 207 ∧
    ∀ j : Nat, 1 ≤ j → j < 207 → ¬(prodRange 4 j ∣ prodRange (4 + j) j) :=
  ⟨e389_witness_4_207, fun j h1 hj =>
    failRow_true_ne 4 j (by omega)
      ((List.all_eq_true.mp e389_sweep_4) j (List.mem_range.mpr hj))⟩

/-- **k(5) = 206 (the full census at n=5):** every 1 ≤ j < 206 fails. -/
theorem e389_minimal_5 :
    prodRange 5 206 ∣ prodRange 211 206 ∧
    ∀ j : Nat, 1 ≤ j → j < 206 → ¬(prodRange 5 j ∣ prodRange (5 + j) j) :=
  ⟨e389_witness_5_206, fun j h1 hj =>
    failRow_true_ne 5 j (by omega)
      ((List.all_eq_true.mp e389_sweep_5) j (List.mem_range.mpr hj))⟩

/-- **k(6) = 2475 (the full census at n=6):** every 1 ≤ j < 2475 fails. -/
theorem e389_minimal_6 :
    prodRange 6 2475 ∣ prodRange 2481 2475 ∧
    ∀ j : Nat, 1 ≤ j → j < 2475 → ¬(prodRange 6 j ∣ prodRange (6 + j) j) :=
  ⟨e389_witness_6_2475, fun j h1 hj =>
    failRow_true_ne 6 j (by omega) (e389_min_value_6 j hj)⟩

/-- **k(7) = 984 (the full census at n=7):** every 1 ≤ j < 984 fails. -/
theorem e389_minimal_7 :
    prodRange 7 984 ∣ prodRange 991 984 ∧
    ∀ j : Nat, 1 ≤ j → j < 984 → ¬(prodRange 7 j ∣ prodRange (7 + j) j) :=
  ⟨e389_witness_7_984, fun j h1 hj =>
    failRow_true_ne 7 j (by omega) (e389_min_value_7 j hj)⟩

/-! ## §6 The count/chain/crown receipts (B5/B6 of the battery). -/

/-- THE COUNT RECEIPTS: the countQ values + the three shift instances (5 ∣ 5,
2 ∣ 4, 3 ∣ 207 — the battery's B5 rows). -/
theorem e389_count_receipts :
    countQ 5 2 5 = 1 ∧ countQ 5 7 5 = 1 ∧ countQ 2 3 4 = 2 ∧ countQ 2 7 4 = 2 ∧
    countQ 5 7 5 = countQ 5 2 5 ∧ countQ 2 7 4 = countQ 2 3 4 ∧
    countQ 3 211 207 = countQ 3 4 207 := by decide

/-- THE CHAIN RECEIPTS: the chain/mCount values + the two swap identities
(chain = sum of capped element depths). -/
theorem e389_chain_receipts :
    countChain 5 2 5 1 = 1 ∧ countChain 2 3 4 2 = 3 ∧ countChain 2 3 4 1 = 2 ∧
    mCount 2 4 2 = 2 ∧ mCount 5 5 1 = 1 ∧
    countChain 5 2 5 1 =
      mCount 5 2 1 + mCount 5 3 1 + mCount 5 4 1 + mCount 5 5 1 + mCount 5 6 1 ∧
    countChain 2 3 4 2 =
      mCount 2 3 2 + mCount 2 4 2 + mCount 2 5 2 + mCount 2 6 2 := by decide

/-- **CROWN INSTANCE (5,2,5,1):** 5 ^ countChain 5 2 5 1 = 5 ∣ 55440. -/
theorem e389_crown_inst_5_2_5 : 5 ^ countChain 5 2 5 1 ∣ prodRange 7 5 := by decide

/-- **CROWN INSTANCE (2,3,4,2):** 2 ^ countChain 2 3 4 2 = 8 ∣ 5040. -/
theorem e389_crown_inst_2_3_4_2 : 2 ^ countChain 2 3 4 2 ∣ prodRange 7 4 := by decide

/-- **CROWN INSTANCE (2,3,4,1):** 2 ^ countChain 2 3 4 1 = 4 ∣ 5040. -/
theorem e389_crown_inst_2_3_4_1 : 2 ^ countChain 2 3 4 1 ∣ prodRange 7 4 := by decide

/-! ## §7 The battery table (the banked A375071 ledger — B7/B9). -/

/-- THE MINIMAL-K TABLE of #389 (battery389.py, 93/93 GREEN; the kernel above
certifies the n = 1..11 rows by decide). The deep-scan rows k(12) = 3648830,
k(13) = 3648829, k(14) = 7979077, k(15) = 7979076 and the n = 16..18 no-hit
band (no k ≤ 10^7) stay battery-only. -/
def k389 : List Nat :=
  [1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143]

/-- The table's length row: n = 1..11. -/
theorem k389_length : k389.length = 11 := by decide

/-! ## §8 The arsenal bridge (the campaign's certified anchors). -/

/-- THE ARSENAL BRIDGE: the ternary digit 2 + three ternary-scaling instances
of the 2-adic depth reader at the standard anchors 44 and 14 and the
#389-native anchor 720 (the n=2 witness block). -/
theorem e389_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 2 = true ∧
    v2r (3 ^ 1 * 44) = v2r 44 ∧
    v2r (3 ^ 1 * 14) = v2r 14 ∧
    v2r (3 ^ 1 * 720) = v2r 720 :=
  ⟨ErdosTernary2.isTernaryDigit_two, CardinalWorldsV2.v2r_ternary_scaling 1 44,
    CardinalWorldsV2.v2r_ternary_scaling 1 14,
    CardinalWorldsV2.v2r_ternary_scaling 1 720⟩

/-! ## §9 The master board (flat anonymous constructor). -/

/-- THE E389 KERNEL MASTER BOARD: the eleven A375071 witnesses + the seven
census rows (works-at-k with every shorter window failing) + the
monotonicity law + THE SHIFT LAW + THE SWAP LAW + THE CROWN LAW + the three
crown instances + the arsenal bridge — every certified fact in one
unconditional conjunction. -/
theorem erdos389_board :
    (prodRange 1 1 ∣ prodRange 2 1) ∧ (prodRange 2 5 ∣ prodRange 7 5) ∧
    (prodRange 3 4 ∣ prodRange 7 4) ∧ (prodRange 4 207 ∣ prodRange 211 207) ∧
    (prodRange 5 206 ∣ prodRange 211 206) ∧ (prodRange 6 2475 ∣ prodRange 2481 2475) ∧
    (prodRange 7 984 ∣ prodRange 991 984) ∧ (prodRange 8 8171 ∣ prodRange 8179 8171) ∧
    (prodRange 9 8170 ∣ prodRange 8179 8170) ∧
    (prodRange 10 45144 ∣ prodRange 45154 45144) ∧
    (prodRange 11 45143 ∣ prodRange 45154 45143) ∧
    (prodRange 1 1 ∣ prodRange 2 1 ∧ ∀ j : Nat, 1 ≤ j → j < 1 → ¬(prodRange 1 j ∣ prodRange (1 + j) j)) ∧
    (prodRange 2 5 ∣ prodRange 7 5 ∧ ∀ j : Nat, 1 ≤ j → j < 5 → ¬(prodRange 2 j ∣ prodRange (2 + j) j)) ∧
    (prodRange 3 4 ∣ prodRange 7 4 ∧ ∀ j : Nat, 1 ≤ j → j < 4 → ¬(prodRange 3 j ∣ prodRange (3 + j) j)) ∧
    (prodRange 4 207 ∣ prodRange 211 207 ∧ ∀ j : Nat, 1 ≤ j → j < 207 → ¬(prodRange 4 j ∣ prodRange (4 + j) j)) ∧
    (prodRange 5 206 ∣ prodRange 211 206 ∧ ∀ j : Nat, 1 ≤ j → j < 206 → ¬(prodRange 5 j ∣ prodRange (5 + j) j)) ∧
    (prodRange 6 2475 ∣ prodRange 2481 2475 ∧ ∀ j : Nat, 1 ≤ j → j < 2475 → ¬(prodRange 6 j ∣ prodRange (6 + j) j)) ∧
    (prodRange 7 984 ∣ prodRange 991 984 ∧ ∀ j : Nat, 1 ≤ j → j < 984 → ¬(prodRange 7 j ∣ prodRange (7 + j) j)) ∧
    (∀ q n k : Nat, countQ q n k ≤ countQ q n (k + 1)) ∧
    (∀ q n k : Nat, q ∣ k → countQ q n k = countQ q (n + k) k) ∧
    (∀ q n k E : Nat, countChain q n k E = depthSum q n E k) ∧
    (∀ q n k E : Nat, (∀ e : Nat, 1 ≤ e → e ≤ E → q ^ e ∣ k) → q ^ countChain q n k E ∣ prodRange (n + k) k) ∧
    (5 ^ countChain 5 2 5 1 ∣ prodRange 7 5) ∧
    (2 ^ countChain 2 3 4 2 ∣ prodRange 7 4) ∧
    (2 ^ countChain 2 3 4 1 ∣ prodRange 7 4) ∧
    (ErdosTernary2.isTernaryDigit 2 = true ∧ v2r (3 ^ 1 * 44) = v2r 44 ∧
      v2r (3 ^ 1 * 14) = v2r 14 ∧ v2r (3 ^ 1 * 720) = v2r 720) :=
  ⟨e389_witness_1_1, e389_witness_2_5, e389_witness_3_4, e389_witness_4_207,
    e389_witness_5_206, e389_witness_6_2475, e389_witness_7_984,
    e389_witness_8_8171, e389_witness_9_8170, e389_witness_10_45144,
    e389_witness_11_45143, e389_minimal_1, e389_minimal_2, e389_minimal_3,
    e389_minimal_4, e389_minimal_5, e389_minimal_6, e389_minimal_7,
    e389_count_mono, e389_shift_law, e389_swap, e389_crown,
    e389_crown_inst_5_2_5, e389_crown_inst_2_3_4_2, e389_crown_inst_2_3_4_1,
    e389_arsenal_bridge⟩

/-! ## §10 Receipts. -/
#print axioms E389.e389_count_mono
#print axioms E389.e389_shift_law
#print axioms E389.e389_swap
#print axioms E389.e389_crown
#print axioms E389.e389_witness_2_5
#print axioms E389.e389_witness_4_207
#print axioms E389.e389_witness_6_2475
#print axioms E389.e389_witness_7_984
#print axioms E389.e389_witness_10_45144
#print axioms E389.e389_witness_11_45143
#print axioms E389.e389_minimal_2
#print axioms E389.e389_minimal_6
#print axioms E389.e389_crown_inst_2_3_4_2
#print axioms E389.e389_arsenal_bridge
#print axioms E389.erdos389_board

/-- THE GREEN RECEIPT STRING of the consecutive-product kernel. -/
def E389_CONSECUTIVE_PRODUCT_GREEN : String := "E389_CONSECUTIVE_PRODUCT_GREEN"

#eval E389_CONSECUTIVE_PRODUCT_GREEN

end E389
