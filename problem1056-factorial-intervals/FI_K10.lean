import Arsenal.CardinalWorlds

/-! # Erdős #1056 — THE FACTORIAL-INTERVAL CASE-FRONTIER (Kill #22, S030)
The TREE-PRODUCT architecture: the compile war (R1/R5) proved linear fuel
recursions past ~3k depth kill the CI runner (the kernel evaluator's deep
native recursion); the R5 green boundary was FI_K9 (3009-deep, GREEN) vs
FI_K10 (8324-deep, killed). Fix: balanced binary product trees — depth
O(log span) (~17 for the largest block), identical values, same witness
statements. Structure law: k consecutive intervals with products ≡ 1
(mod p) ⟺ the prefix-factorial sequence j! mod p visits one value k+1
times. Known: k=2 (Erdős 1979, p=11), k=3 (Makowski 1983, p=17). -/

set_option maxRecDepth 65536

/-- Balanced-tree product of [a, b] mod p: split at the midpoint, leaves
are single terms. Fuel bounds the tree depth (64 ≫ log₂ 52163 + 2). -/
def prodmodT (p : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, a, b =>
    if a > b then 1
    else if a = b then a % p
    else (prodmodT p f a ((a + b) / 2) * prodmodT p f ((a + b) / 2 + 1) b) % p

/-- Product of the interval [a, b] modulo p (witness intervals have b > a). -/
def prodmod (p a b : Nat) : Nat := prodmodT p 64 a b

/-- Factorial j! mod p: the tree product of [1, j] (j = 0 gives the empty
range and 0! = 1 for free). -/
def factmod (p j : Nat) : Nat := prodmodT p 64 1 j

/-! ## The case k = 10 — NEW (p = 27901) -/
theorem erdos1056_k10 : Nat.Prime 27901 ∧
    prodmod 27901 2452 2867 = 1 ∧ prodmod 27901 2868 4768 = 1 ∧
    prodmod 27901 4769 10383 = 1 ∧ prodmod 27901 10384 18707 = 1 ∧
    prodmod 27901 18708 19589 = 1 ∧ prodmod 27901 19590 19965 = 1 ∧
    prodmod 27901 19966 22981 = 1 ∧ prodmod 27901 22982 24673 = 1 ∧
    prodmod 27901 24674 26322 = 1 ∧ prodmod 27901 26323 27263 = 1 := by
  decide

#eval "FI_K10_GREEN"
#print axioms erdos1056_k10
