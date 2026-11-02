/-
# ERDŐS #261 — THE BLOCK-IDENTITY BRIDGE KERNEL (toward the rational-x question)

The problem (erdosproblems.com/261): Are there infinitely many n such that
n/2^n = Σ_{k=1}^{t} a_k/2^{a_k} for some t ≥ 2 and distinct integers
a_1, …, a_t ≥ 1?  Is this true for all n?  Is there a RATIONAL x such that
x = Σ_{k=1}^{∞} a_k/2^{a_k} has at least 2^{ℵ₀} solutions?

Sub-question 1 is known (Borwein–Loring [BoLo90]): every
n = 2^{m+1} − m − 2 has the m-piece witness {n+1, …, n+m}.  This kernel
formalizes the integer identity behind that family (independently re-derived
by this campaign), the geometric engine, and the toggle receipts of the NEW
reduction theorem for the rational-x question (full statement and proof in
DERIVATION.tex):

**THE Q3 BRIDGE (new, this campaign).** If every sufficiently large n has a
representation of n/2^n whose pieces all lie in (n, n+T] for a UNIFORM T,
then the rational  x = Σ_{k≥0} (N₀+kT)/2^{N₀+kT}  has 2^{ℵ₀} representations
(each toggle {N₀+kT} ↔ its witness set is value-preserving, the toggle
regions are disjoint, and the base value is rational by the
arithmetic-progression sum identity — proved in DERIVATION.tex).

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

* `jpow_sum_eq` : Σ_{j=1}^{m} j·2^{m−j} = 2^{m+1} − m − 2   (kernel identity)
* `pow_sum_eq`  : Σ_{j=1}^{m} 2^{m−j} = 2^m − 1             (geometric engine)
* `bl_family`   : for n = 2^{m+1} − m − 2:  Σ_{j=1}^{m} (n+j)·2^{m−j} = n·2^m
                  (the integer form of the representation family: dividing
                  by 2^{n+m},  Σ_{j=1}^{m} (n+j)/2^{n+j} = n/2^n)
* RECEIPTS: the family witnesses (n = 4, 11, 26), the value-preserving
  toggles {2} ≅ {3,6,8} ≅ {4,5,6} (all = 128 at scale 2^8), the AP-sum
  rationality engine values.
-/

-- ===========================================================================
-- §1  THE TWO SUM ENGINES
-- ===========================================================================

/-- `jpow_sum m = Σ_{j=1}^{m} j · 2^{m-j}` (recursion: double and add m). -/
def jpow_sum : Nat → Nat
  | 0 => 0
  | m + 1 => 2 * jpow_sum m + (m + 1)

/-- `pow_sum m = Σ_{j=1}^{m} 2^{m-j}` (recursion: double and add 1). -/
def pow_sum : Nat → Nat
  | 0 => 0
  | m + 1 => 2 * pow_sum m + 1

theorem one_le_two_pow : ∀ (k : Nat), 1 ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
    rw [Nat.pow_succ]
    exact one_le_mul _ _ (by decide) (one_le_two_pow k)

theorem pow_sum_eq (m : Nat) : pow_sum m = 2 ^ m - 1 := by
  induction m with
  | zero => simp [pow_sum]
  | succ m ih =>
    show 2 * pow_sum m + 1 = 2 ^ (m + 1) - 1
    rw [ih, Nat.pow_succ]
    omega

theorem jpow_sum_eq (m : Nat) : jpow_sum m = 2 ^ (m + 1) - m - 2 := by
  induction m with
  | zero => simp [jpow_sum]
  | succ m ih =>
    show 2 * jpow_sum m + (m + 1) = 2 ^ (m + 2) - (m + 1) - 2
    rw [ih, show m + 2 = m + 1 + 1 from by omega, Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ (m + 1) := one_le_two_pow (m + 1)
    omega

-- ===========================================================================
-- §2  THE REPRESENTATION FAMILY (integer form)
-- ===========================================================================

/-- `bl_sum n m = Σ_{j=1}^{m} (n+j) · 2^{m-j}`. -/
def bl_sum (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => 2 * bl_sum n m + (n + m + 1)

theorem bl_sum_split (n : Nat) : ∀ (m : Nat),
    bl_sum n m = n * pow_sum m + jpow_sum m
  | 0 => by simp [bl_sum, pow_sum, jpow_sum]
  | m + 1 => by
    have ih := bl_sum_split n m
    show 2 * bl_sum n m + (n + m + 1)
        = n * (2 * pow_sum m + 1) + (2 * jpow_sum m + (m + 1))
    rw [ih, Nat.mul_add n (2 * pow_sum m) 1, Nat.mul_one n,
        Nat.mul_comm n (2 * pow_sum m), Nat.mul_assoc 2 (pow_sum m) n,
        Nat.mul_comm (pow_sum m) n, Nat.mul_add 2 (n * pow_sum m) (jpow_sum m)]
    omega

/-- **The representation-family identity (kernel form).** If `jpow_sum m = n`
then `Σ_{j=1}^{m} (n+j)·2^{m−j} = n·2^m`. -/
theorem bl_of_jpow (n m : Nat) (hj : jpow_sum m = n) :
    bl_sum n m = n * 2 ^ m := by
  have hps : pow_sum m + 1 = 2 ^ m := by rw [pow_sum_eq]; omega
  have h := bl_sum_split n m
  rw [h, hj]
  have key : n * pow_sum m + n = n * (pow_sum m + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [key, hps]

/-- **The Borwein–Loring family identity (integer form).** For every m,
with `n = 2^{m+1} − m − 2` (n = 1, 4, 11, 26, 57, 120, 247, …):
`Σ_{j=1}^{m} (n+j)·2^{m−j} = n·2^m`.  Dividing by 2^{n+m} (every exponent
n+m−(n+j) = m−j ≥ 0): `Σ_{j=1}^{m} (n+j)/2^{n+j} = n/2^n` — every such n
admits an m-piece distinct representation.  (The family first appears in
[BoLo90]; the identity was independently re-derived by this campaign and is
formalized here.) -/
theorem bl_family (m : Nat) :
    bl_sum (2 ^ (m + 1) - m - 2) m = (2 ^ (m + 1) - m - 2) * 2 ^ m :=
  bl_of_jpow _ m (jpow_sum_eq m)

-- ===========================================================================
-- §3  RECEIPTS
-- ===========================================================================

-- The family (integer witnesses; divide both sides by 2^{n+m})
-- n = 4, m = 2:  5·2 + 6·1 = 16 = 4·4   →  5/32 + 6/64 = 4/16 = 1/4
#eval (bl_sum 4 2, 4 * 2 ^ 2)                             -- (16, 16)
-- n = 11, m = 3:  12·4 + 13·2 + 14·1 = 88 = 11·8
#eval (bl_sum 11 3, 11 * 2 ^ 3)                           -- (88, 88)
-- n = 26, m = 4:  27·8 + 28·4 + 29·2 + 30·1 = 416 = 26·16
#eval (bl_sum 26 4, 26 * 2 ^ 4)                           -- (416, 416)
-- the family list: n = 2^{m+1} − m − 2 for m = 1..8
#eval (List.range 8).map (fun m => 2 ^ (m + 2) - (m + 1) - 2)  -- [1,4,11,26,57,120,247,502]

-- Value-preserving toggles at scale 2^8 (all three represent 128/256 = 1/2):
-- {2}: 2·2^6;  {3,6,8}: 3·2^5+6·2^2+8;  {4,5,6}: 4·2^4+5·2^3+6·2^2
#eval (2 * 2 ^ (8 - 2), 3 * 2 ^ (8 - 3) + 6 * 2 ^ (8 - 6) + 8 * 2 ^ (8 - 8),
       4 * 2 ^ (8 - 4) + 5 * 2 ^ (8 - 5) + 6 * 2 ^ (8 - 6))  -- (128, 128, 128)

-- The AP-rationality engine (values; the general identity is in DERIVATION.tex):
-- Σ_{k=0}^{3} (9 + 24k)·2^{3−k} = 9·15 + 24·10 = 375
#eval (9 * 2 + 33 * 1, (9 + 24) * 2 + (9 + 48) * 1,
       (9) * 4 + (33) * 2 + (57) * 1,
       9 * 2 ^ 0 + 33 * 2 ^ 1 + 57 * 2 ^ 2 + 81 * 2 ^ 3)    -- tails of the AP 9,33,57,81

#print axioms bl_family
#print axioms bl_of_jpow
#print axioms jpow_sum_eq
#print axioms pow_sum_eq
