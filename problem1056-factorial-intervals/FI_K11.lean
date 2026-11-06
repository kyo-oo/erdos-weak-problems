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

/-! ## The case k = 11 — THE FRONTIER (p = 52163): eleven consecutive
intervals covering [2, 52161], every block product ≡ 1 (mod 52163). The
value-1 chain cut points: 1, 3924, 7291, 7427, 18519, 24931, 26081,
27231, 33643, 44735, 44871, 52161. -/
theorem erdos1056_k11 : Nat.Prime 52163 ∧
    prodmod 52163 2 3924 = 1 ∧ prodmod 52163 3925 7291 = 1 ∧
    prodmod 52163 7292 7427 = 1 ∧ prodmod 52163 7428 18519 = 1 ∧
    prodmod 52163 18520 24931 = 1 ∧ prodmod 52163 24932 26081 = 1 ∧
    prodmod 52163 26082 27231 = 1 ∧ prodmod 52163 27232 33643 = 1 ∧
    prodmod 52163 33644 44735 = 1 ∧ prodmod 52163 44736 44871 = 1 ∧
    prodmod 52163 44872 52161 = 1 := by decide

#eval "FI_K11_GREEN"
#print axioms erdos1056_k11
