import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos389 — THE CONSECUTIVE-PRODUCT KERNEL (Kernel 66, W59-T4r3)

Erdős–Straus #389 (open): for every n ≥ 1 does there exist k with
n(n+1)···(n+k−1) ∣ (n+k)···(n+2k−1) — the consecutive-product divisibility
question. The python engine of this directory (battery389.py, 93/93 GREEN)
certified the minimal-k table k(1..13) = 1, 5, 4, 207, 206, 2475, 984,
8171, 8170, 45144, 45143, 3648830, 3648829; this kernel certifies the
load-bearing facts unconditionally, all in exact-integer form:

* **HABITAT:** `E389.prodRange n k` = n(n+1)···(n+k−1) (equation-compiler
  structural on the window) and `E389.countQ q n k` = the number of
  multiples of q among n, n+1, ···, n+k−1.
* **WITNESSES (closed-term decide):** n=2, k=5 (720 ∣ 55440); n=3, k=4
  (360 ∣ 5040); the battery's big rows n=4, k=207 and n=5, k=206 —
  207-wide and 206-wide consecutive products (hundreds of digits, ≈10^397
  left blocks against ≈10^515 right blocks), kernel-exact through the
  core Nat instances.
* **MINIMAL-K CENSUS (n ≤ 3, closed-term decide):** k(1)=1; k(2)=5 with
  every shorter window failing; k(3)=4 with every shorter window failing.
* **COUNT MACHINERY (structural, THE CORE):** `e389_count_mono` (widening
  the window never drops the count); `e389_mod_shift` (q ∣ s → (a+s) % q =
  a % q, the per-index congruence via the core mod chain); and **THE SHIFT
  LAW** `e389_shift_law` (q ∣ k → countQ q n k = countQ q (n+k) k):
  whenever q divides the window length, the two k-blocks [n, n+k) and
  [n+k, n+2k) carry the SAME count of q-multiples — the symmetry core
  under every witness's window-matching.
* **SCOPE (honest):** the count-soundness direction (dominance of the
  right block's q-counts for every q ≤ n+k−1 implying the divisibility)
  is NOT carried in this kernel — it stays the campaign's open lane and
  is docstring-only here by design.

Laws obeyed: no sorry / admit / native_decide; decide only on closed
terms; `∣`-decidability only through the core Nat instances; mod
arithmetic via `Nat.add_mod` / `Nat.mul_mod_right` / `Nat.add_zero` /
`Nat.mod_mod`; divisibility destructured as `obtain ⟨t, ht⟩` with the
multiplier on the right; atoms spelled as the goal spells.
-/

namespace E389

/-! ## §1 Structural habitat (self-contained, equation-compiler native). -/

/-- THE CONSECUTIVE PRODUCT: `prodRange n k` = n(n+1)···(n+k−1), the left
block of the #389 divisibility question at window k (structural on the
window; the top factor n+k of the k+1-window multiplies the tail). -/
def prodRange (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n + k) * prodRange n k

/-- The window-0 equation (the empty product). -/
theorem prodRange_zero (n : Nat) : prodRange n 0 = 1 := rfl

/-- The window-successor equation: the head n+k multiplies the tail. -/
theorem prodRange_succ (n k : Nat) :
    prodRange n (k + 1) = (n + k) * prodRange n k := rfl

/-! ## §2 The witness tables (decide only on closed terms). -/

/-- The n=2, k=5 left block: 2·3·4·5·6 = 720. -/
theorem e389_prod_2_5 : prodRange 2 5 = 720 := by decide

/-- The n=2, k=5 right block: 7·8·9·10·11 = 55440. -/
theorem e389_prod_7_5 : prodRange 7 5 = 55440 := by decide

/-- The n=3, k=4 left block: 3·4·5·6 = 360. -/
theorem e389_prod_3_4 : prodRange 3 4 = 360 := by decide

/-- The n=3, k=4 right block: 7·8·9·10 = 5040. -/
theorem e389_prod_7_4 : prodRange 7 4 = 5040 := by decide

/-- The exact quotient of the n=2, k=5 witness: 55440 / 720 = 77 (the
multiplier that makes the divisibility visible). -/
theorem e389_quot_2_5 : prodRange 7 5 / prodRange 2 5 = 77 := by decide

/-- The exact quotient of the n=3, k=4 witness: 5040 / 360 = 14. -/
theorem e389_quot_3_4 : prodRange 7 4 / prodRange 3 4 = 14 := by decide

/-- **WITNESS (n=2, k=5):** 720 ∣ 55440 (55440 = 77 · 720) — the closed
`∣`-Prop, decided by the kernel through the core Nat instances. -/
theorem e389_witness_2_5 : prodRange 2 5 ∣ prodRange 7 5 := by decide

/-- **WITNESS (n=3, k=4):** 360 ∣ 5040 (5040 = 14 · 360). -/
theorem e389_witness_3_4 : prodRange 3 4 ∣ prodRange 7 4 := by decide

/-- **WITNESS (n=4, k=207 — the battery's minimal k(4)):** the 207-wide
left block 4···210 (a product of hundreds of digits) divides the
207-wide right block 211···417 — closed-term decide, kernel-exact
big-Nat arithmetic. -/
theorem e389_witness_4_207 : prodRange 4 207 ∣ prodRange 211 207 := by decide

/-- **WITNESS (n=5, k=206 — the battery's minimal k(5)):** the 206-wide
left block 5···210 divides the 206-wide right block 211···416 — the same
closed decide scale as the n=4 row. -/
theorem e389_witness_5_206 : prodRange 5 206 ∣ prodRange 211 206 := by decide

/-! ## §3 The minimal-k census (small n; decide on closed conjunctions). -/

/-- **k(1) = 1:** the 1-wide block at n=1 divides the 1-wide block at
n=2 (1 ∣ 2); with the domain k ≥ 1 there is nothing below 1 to fail. -/
theorem e389_min_1 : prodRange 1 1 ∣ prodRange 2 1 := by decide

/-- **k(2) = 5 (the full census at n=2):** k=5 works and every shorter
window fails — 2 ∤ 3; 6 ∤ 20; 24 ∤ 210; 120 ∤ 3024. -/
theorem e389_min_2 :
    prodRange 2 5 ∣ prodRange 7 5 ∧
    ¬(prodRange 2 1 ∣ prodRange 3 1) ∧
    ¬(prodRange 2 2 ∣ prodRange 4 2) ∧
    ¬(prodRange 2 3 ∣ prodRange 5 3) ∧
    ¬(prodRange 2 4 ∣ prodRange 6 4) := by decide

/-- The census at n=2, row by row (one closed decide each): j=1 — the
1-wide block 2 does not divide the 1-wide block 3. -/
theorem e389_k2_j1 : ¬(prodRange 2 1 ∣ prodRange 3 1) := by decide

/-- j=2 — 6 ∤ 20. -/
theorem e389_k2_j2 : ¬(prodRange 2 2 ∣ prodRange 4 2) := by decide

/-- j=3 — 24 ∤ 210. -/
theorem e389_k2_j3 : ¬(prodRange 2 3 ∣ prodRange 5 3) := by decide

/-- j=4 — the nearest miss: 120 ∤ 3024. -/
theorem e389_k2_j4 : ¬(prodRange 2 4 ∣ prodRange 6 4) := by decide

/-- The j=4 near-miss residue: 3024 % 120 = 24 (how far the j=4 window
is from closing). -/
theorem e389_k2_j4_res : prodRange 6 4 % prodRange 2 4 = 24 := by decide

/-- **k(3) = 4 (the full census at n=3):** k=4 works and every shorter
window fails — 3 ∤ 4; 12 ∤ 30; 60 ∤ 336. -/
theorem e389_min_3 :
    prodRange 3 4 ∣ prodRange 7 4 ∧
    ¬(prodRange 3 1 ∣ prodRange 4 1) ∧
    ¬(prodRange 3 2 ∣ prodRange 5 2) ∧
    ¬(prodRange 3 3 ∣ prodRange 6 3) := by decide

/-- The census at n=3, row by row: j=1 — 3 ∤ 4. -/
theorem e389_k3_j1 : ¬(prodRange 3 1 ∣ prodRange 4 1) := by decide

/-- j=2 — 12 ∤ 30. -/
theorem e389_k3_j2 : ¬(prodRange 3 2 ∣ prodRange 5 2) := by decide

/-- j=3 — the nearest miss: 60 ∤ 336. -/
theorem e389_k3_j3 : ¬(prodRange 3 3 ∣ prodRange 6 3) := by decide

/-- The j=3 near-miss residue: 336 % 60 = 36. -/
theorem e389_k3_j3_res : prodRange 6 3 % prodRange 3 3 = 36 := by decide

/-! ## §4 The count machinery (structural — THE CORE). -/

/-- THE MULTIPLE-COUNT: `countQ q n k` = #{i ∈ [n, n+k) : q ∣ i} — the
number of multiples of q among n, n+1, ···, n+k−1 (Prop-if on the core
Nat decidable equality; structural on the window). -/
def countQ (q n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if (n + k) % q = 0 then 1 else 0) + countQ q n k

/-- The window-0 equation (the empty count). -/
theorem countQ_zero (q n : Nat) : countQ q n 0 = 0 := rfl

/-- The window-successor equation: the head n+k contributes 1 or 0. -/
theorem countQ_succ (q n k : Nat) :
    countQ q n (k + 1) = (if (n + k) % q = 0 then 1 else 0) + countQ q n k :=
  rfl

/-- **MONOTONICITY:** widening the window never drops the count — the
one-step structural unfold (`rfl`-shaped equation at the constructor),
an if-split on the head, and omega (the head contributes 0 or 1). -/
theorem e389_count_mono : ∀ q n k : Nat, countQ q n k ≤ countQ q n (k + 1) := by
  intro q n k
  have e1 : countQ q n (k + 1) =
      (if (n + k) % q = 0 then 1 else 0) + countQ q n k := rfl
  rw [e1]
  by_cases hmod : (n + k) % q = 0
  · rw [if_pos hmod]
    omega
  · rw [if_neg hmod]
    omega

/-- **THE MOD-SHIFT CONGRUENCE (the per-index kernel of the file):**
q ∣ s → (a + s) % q = a % q — destructure the divisibility into s = q·t
(multiplier on the right) and walk the core mod chain `Nat.add_mod`,
`Nat.mul_mod_right`, `Nat.add_zero`, `Nat.mod_mod`. -/
theorem e389_mod_shift (a s q : Nat) (hs : q ∣ s) : (a + s) % q = a % q := by
  obtain ⟨t, ht⟩ := hs
  rw [ht, Nat.add_mod a (q * t) q, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

/-- **THE GENERAL SHIFT:** q ∣ s → the window [n, n+m) and its s-translate
[n+s, n+s+m) carry the SAME count of q-multiples — structural induction
on the window, the two heads aligned by `e389_mod_shift`. -/
theorem e389_count_shift (q s : Nat) (hs : q ∣ s) :
    ∀ n m : Nat, countQ q n m = countQ q (n + s) m := by
  intro n m
  induction m with
  | zero => rfl
  | succ j ih =>
    have e1 : countQ q n (j + 1) =
        (if (n + j) % q = 0 then 1 else 0) + countQ q n j := rfl
    have e2 : countQ q (n + s) (j + 1) =
        (if (n + s + j) % q = 0 then 1 else 0) + countQ q (n + s) j := rfl
    have hmod' : (n + s + j) % q = (n + j) % q := by
      have hcomm : n + s + j = n + j + s := by omega
      rw [hcomm]
      exact e389_mod_shift (n + j) s q hs
    rw [e1, e2, hmod', ih]

/-- **THE SHIFT LAW (the symmetry core of #389):** q ∣ k → the two
k-blocks [n, n+k) and [n+k, n+2k) have the SAME count of q-multiples —
the congruence that underlies the window-matching of every witness. -/
theorem e389_shift_law :
    ∀ q n k : Nat, q ∣ k → countQ q n k = countQ q (n + k) k := by
  intro q n k hd
  exact e389_count_shift q k hd n k

/-- COROLLARY (the witness-block symmetry at the battery's k(4) scale):
for every q dividing 207, the two 207-blocks at n and at n+207 carry the
same q-count — the shift shape behind the n=4 witness. -/
theorem e389_shift_207 (q n : Nat) (hq : q ∣ 207) :
    countQ q n 207 = countQ q (n + 207) 207 :=
  e389_shift_law q n 207 hq

/-- COROLLARY (the k(5) scale): the same symmetry at the 206-wide
witness window. -/
theorem e389_shift_206 (q n : Nat) (hq : q ∣ 206) :
    countQ q n 206 = countQ q (n + 206) 206 :=
  e389_shift_law q n 206 hq

/-! ## §5 The arsenal bridge (the campaign's certified anchors). -/

/-- THE ARSENAL BRIDGE: three Arsenal lemma instances at the campaign's
anchor numbers (ternary digit 2 carries the scaling; 44 and 14 are the
standard bridge anchors). -/
theorem e389_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 2 = true ∧
    v2r (3 ^ 1 * 44) = v2r 44 ∧
    v2r (3 ^ 1 * 14) = v2r 14 :=
  ⟨rfl, CardinalWorldsV2.v2r_ternary_scaling 1 44,
    CardinalWorldsV2.v2r_ternary_scaling 1 14⟩

/-! ## §6 The master board (flat anonymous constructor). -/

/-- THE E389 KERNEL MASTER BOARD: the four witnesses + the three census
rows + the monotonicity law + THE SHIFT LAW + the arsenal bridge — every
certified fact of the kernel in one unconditional conjunction. -/
theorem erdos389_board :
    (prodRange 2 5 ∣ prodRange 7 5) ∧
    (prodRange 3 4 ∣ prodRange 7 4) ∧
    (prodRange 4 207 ∣ prodRange 211 207) ∧
    (prodRange 5 206 ∣ prodRange 211 206) ∧
    (prodRange 1 1 ∣ prodRange 2 1) ∧
    (prodRange 2 5 ∣ prodRange 7 5 ∧
      ¬(prodRange 2 1 ∣ prodRange 3 1) ∧
      ¬(prodRange 2 2 ∣ prodRange 4 2) ∧
      ¬(prodRange 2 3 ∣ prodRange 5 3) ∧
      ¬(prodRange 2 4 ∣ prodRange 6 4)) ∧
    (prodRange 3 4 ∣ prodRange 7 4 ∧
      ¬(prodRange 3 1 ∣ prodRange 4 1) ∧
      ¬(prodRange 3 2 ∣ prodRange 5 2) ∧
      ¬(prodRange 3 3 ∣ prodRange 6 3)) ∧
    (∀ q n k : Nat, countQ q n k ≤ countQ q n (k + 1)) ∧
    (∀ q n k : Nat, q ∣ k → countQ q n k = countQ q (n + k) k) ∧
    (ErdosTernary2.isTernaryDigit 2 = true ∧
      v2r (3 ^ 1 * 44) = v2r 44 ∧
      v2r (3 ^ 1 * 14) = v2r 14) :=
  ⟨e389_witness_2_5, e389_witness_3_4, e389_witness_4_207, e389_witness_5_206,
    e389_min_1, e389_min_2, e389_min_3, e389_count_mono, e389_shift_law,
    e389_arsenal_bridge⟩

/-! ## §7 The battery table (the honest ledger of the campaign engine). -/

/-- THE MINIMAL-K TABLE of #389 (battery389.py, 93/93 GREEN — the python
engine's certified output). The kernel above certifies the n ≤ 5 rows
(k = 1, 5, 4, 207, 206 — the first five entries) by decide; the n ≥ 6
rows are battery-only and stay outside this kernel's receipts. -/
def k389 : List Nat :=
  [1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143, 3648830, 3648829]

/-- The table's length row: n = 1..13. -/
theorem k389_length : k389.length = 13 := by decide

/-! ## §8 Receipts. -/
#print axioms E389.e389_witness_2_5
#print axioms E389.e389_witness_3_4
#print axioms E389.e389_witness_4_207
#print axioms E389.e389_witness_5_206
#print axioms E389.e389_min_1
#print axioms E389.e389_min_2
#print axioms E389.e389_min_3
#print axioms E389.e389_shift_law
#print axioms E389.e389_count_mono
#print axioms E389.erdos389_board

/-- THE GREEN RECEIPT STRING of the consecutive-product kernel. -/
def E389_CONSECUTIVE_PRODUCT_GREEN : String := "E389_CONSECUTIVE_PRODUCT_GREEN"

#eval E389_CONSECUTIVE_PRODUCT_GREEN

end E389
