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

/-! ## The cases k = 2 .. 8 -/
theorem erdos1056_k2 : Nat.Prime 11 ∧
    prodmod 11 3 4 = 1 ∧ prodmod 11 5 7 = 1 := by decide

theorem erdos1056_k3 : Nat.Prime 17 ∧
    prodmod 17 2 5 = 1 ∧ prodmod 17 6 11 = 1 ∧ prodmod 17 12 15 = 1 := by
  decide

theorem erdos1056_k4 : Nat.Prime 23 ∧
    prodmod 23 2 4 = 1 ∧ prodmod 23 5 8 = 1 ∧ prodmod 23 9 11 = 1 ∧
    prodmod 23 12 21 = 1 := by decide

theorem erdos1056_k5 : Nat.Prime 109 ∧
    prodmod 109 10 11 = 1 ∧ prodmod 109 12 39 = 1 ∧ prodmod 109 40 58 = 1 ∧
    prodmod 109 59 73 = 1 ∧ prodmod 109 74 85 = 1 := by decide

theorem erdos1056_k6 : Nat.Prime 71 ∧
    prodmod 71 8 9 = 1 ∧ prodmod 71 10 19 = 1 ∧ prodmod 71 20 51 = 1 ∧
    prodmod 71 52 61 = 1 ∧ prodmod 71 62 63 = 1 ∧ prodmod 71 64 70 = 1 := by
  decide

theorem erdos1056_k7 : Nat.Prime 673 ∧
    prodmod 673 160 316 = 1 ∧ prodmod 673 317 354 = 1 ∧
    prodmod 673 355 393 = 1 ∧ prodmod 673 394 397 = 1 ∧
    prodmod 673 398 506 = 1 ∧ prodmod 673 507 545 = 1 ∧
    prodmod 673 546 647 = 1 := by decide

theorem erdos1056_k8 : Nat.Prime 599 ∧
    prodmod 599 29 50 = 1 ∧ prodmod 599 51 122 = 1 ∧ prodmod 599 123 183 = 1 ∧
    prodmod 599 184 250 = 1 ∧ prodmod 599 251 289 = 1 ∧ prodmod 599 290 500 = 1 ∧
    prodmod 599 501 539 = 1 ∧ prodmod 599 540 555 = 1 := by decide

#eval "FI_K2_K8_GREEN"
#print axioms erdos1056_k2
#print axioms erdos1056_k4
#print axioms erdos1056_k8
