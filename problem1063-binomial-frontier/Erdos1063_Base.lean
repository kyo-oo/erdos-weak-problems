/-! # Erdos1063_Base — the binomial-frontier oracle (Kill candidate, S033)

Erdős–Selfridge #1063: n_k = least n ≥ 2k such that (n−i) ∣ C(n,k) for
all but one 0 ≤ i < k. This module defines the computation ONCE (the K18
§7-freeze architecture): data modules decide one chunk each; the FINAL
module assembles with zero kernel work on the assembly theorems.

- `binomP n k = ∏_{i<k} (n−i)` (descending product, structural recursion);
- `kfact k = k!`;
- `binom n k = binomP n k / kfact k` — THE binomial coefficient (the
  division is mathematically exact; certified by `erdos1063_binomP_absorb`
  in the FINAL module: binomP n k · (n−k)! = n!);
- `wcount n k` = #{i < k : (n−i) ∣ C(n,k)}. -/

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

/-- The divisibility census: #{i < k : (n−i) ∣ C(n,k)}. -/
def wcount (n k : Nat) : Nat :=
  (List.range k).countp (fun i => binom n k % (n - i) == 0)
