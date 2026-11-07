/-! # Erdos1072_Data — the factorial-chain oracle (Kill candidate, S033)

Erdős–Hardy–Subbarao #1072: f(p) = least n with n! ≡ −1 (mod p).

Definitions (structural recursions, depth ≤ 71 in all uses):
- `fm p j` = j! mod p;
- `tm p m` = the product of the m consecutive integers just below p,
  (p−m)·(p−m+1)·…·(p−1), reduced mod p;
- `sgn p m` = (−1)^m mod p as an explicit residue: 1 (m even) or p−1 (m odd).

Receipts (all decide-verified): the Wilson values (p−1)! ≡ −1 (mod p) for
the thirteen named census primes, and the eleven first extra-solution
instances n! ≡ −1 (mod p) at n < p−1. -/

set_option maxRecDepth 65536

/-- j! mod p. -/
def fm (p : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => ((j + 1) * fm p j) % p

/-- The tail product (p−1)·(p−2)·…·(p−m) mod p. -/
def tm (p : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => ((p - 1 - m) * tm p m) % p

/-- (−1)^m mod p as the explicit residue 1 (m even) / p−1 (m odd). -/
def sgn (p m : Nat) : Nat := if m % 2 = 0 then 1 else p - 1

namespace Erdos1072Data

/-! ## Wilson receipts: (p−1)! ≡ −1 (mod p) for the named primes. -/
theorem wilson_5  : fm 5 4   = 4   := by decide
theorem wilson_7  : fm 7 6   = 6   := by decide
theorem wilson_11 : fm 11 10 = 10  := by decide
theorem wilson_13 : fm 13 12 = 12  := by decide
theorem wilson_19 : fm 19 18 = 18  := by decide
theorem wilson_23 : fm 23 22 = 22  := by decide
theorem wilson_29 : fm 29 28 = 28  := by decide
theorem wilson_43 : fm 43 42 = 42  := by decide
theorem wilson_47 : fm 47 46 = 46  := by decide
theorem wilson_59 : fm 59 58 = 58  := by decide
theorem wilson_61 : fm 61 60 = 60  := by decide
theorem wilson_67 : fm 67 66 = 66  := by decide
theorem wilson_71 : fm 71 70 = 70  := by decide

/-! ## The named extra-solution instances (n! ≡ −1 at n < p−1;
battery census: these are the first primes with a second solution). -/
theorem inst_7_3   : fm 7 3   = 6   := by decide
theorem inst_11_5  : fm 11 5  = 10  := by decide
theorem inst_19_9  : fm 19 9  = 18  := by decide
theorem inst_23_14 : fm 23 14 = 22  := by decide
theorem inst_29_18 : fm 29 18 = 28  := by decide
theorem inst_43_21 : fm 43 21 = 42  := by decide
theorem inst_47_23 : fm 47 23 = 46  := by decide
theorem inst_59_15 : fm 59 15 = 58  := by decide
theorem inst_61_8  : fm 61 8  = 60  := by decide
theorem inst_67_18 : fm 67 18 = 66  := by decide
theorem inst_71_7  : fm 71 7  = 70  := by decide

/-! ## The paired tails (p−1−n)! for the named instances. -/
theorem tail_7_3   : fm 7 3   = 6   := by decide
theorem tail_11_5  : fm 11 5  = 10  := by decide
theorem tail_19_9  : fm 19 9  = 18  := by decide
theorem tail_23_8  : fm 23 8  = 1   := by decide
theorem tail_29_10 : fm 29 10 = 1   := by decide
theorem tail_43_21 : fm 43 21 = 42  := by decide
theorem tail_47_23 : fm 47 23 = 46  := by decide
theorem tail_59_43 : fm 59 43 = 58  := by decide
theorem tail_61_52 : fm 61 52 = 60  := by decide
theorem tail_67_48 : fm 67 48 = 66  := by decide
theorem tail_71_63 : fm 71 63 = 70  := by decide

#eval "ERDOS1072_DATA_GREEN"

end Erdos1072Data
