/-! # Erdos396_Base — the descending-factorial divisibility oracle (S038)

Erdős #396: is it true that for every $k$ there exists $n$ such that
$\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}$?

This module defines the computation ONCE (the K20/Erdos1063_Base
architecture, lifted verbatim): `binomP n k = ∏_{i<k}(n-i)` (the problem's
own descending product — for k+1 factors read `binomP n (k+1)`), `kfact`,
and `binom n k = binomP n k / kfact k` — THE binomial coefficient,
certified exact by `erdos396_binomP_absorb` in the FINAL module. The data
modules decide the exclusion chunks; the FINAL module assembles. -/

set_option maxRecDepth 65536

/-- The descending product ∏_{i<k} (n − i) = n·(n−1)·…·(n−k+1). -/
def binomP : Nat → Nat → Nat
  | _, 0 => 1
  | n, k + 1 => (n - k) * binomP n k

/-- The factorial k!. -/
def kfact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * kfact k

/-- The binomial coefficient C(n,k) = ∏_{i<k}(n−i) / k!. -/
def binom (n k : Nat) : Nat := binomP n k / kfact k
