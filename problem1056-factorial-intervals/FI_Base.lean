/-! # FI_Base — the tree-product oracle for Erdős #1056 (Kill #22, S030)
THE §7-FREEZE OLEAN LADDER (the K14 architecture): this core-only module
defines the products ONCE; the data modules prove one block-product each
(small kernel decides, term-budgeted); the FINAL modules assemble the
k-theorems with ZERO kernel work (pure ⟨⟩ composition).

The TREE-PRODUCT: balanced binary product of [a, b] mod p — depth
O(log span) (the linear-fuel version's deep native recursion is the
R1/R5 killer; the total kernel grind ~1.5ms/term is the step wall —
every process is term-budgeted ≤ ~15k terms ≈ 25s). -/

set_option maxRecDepth 65536

/-- Balanced-tree product of [a, b] mod p: split at the midpoint. -/
def prodmodT (p : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, a, b =>
    if a > b then 1
    else if a = b then a % p
    else (prodmodT p f a ((a + b) / 2) * prodmodT p f ((a + b) / 2 + 1) b) % p

/-- Product of the interval [a, b] modulo p. -/
def prodmod (p a b : Nat) : Nat := prodmodT p 64 a b

/-- Factorial j! mod p (the tree product of [1, j]; 0! = 1 free). -/
def factmod (p j : Nat) : Nat := prodmodT p 64 1 j
