# STATUS — #451 frontier extended: n_21 = 805, n_22 = 2691, n_23 = 1884, n_24 = 2664

**S063 W62 volley, task 1-c (the guaranteed-kill executor).** Battery:
`battery451_ext.py` (output `battery451_ext_output.txt`, ALL GREEN).
Calibration law honored: k = 2..20 re-derived by both methods and equal to the
certified table (6, 9, 20, 13, 21, 21, 22, 65, 220, 51, 338, 133, 321, 339,
340, 113, 114, 368, 550) before extending.

## THE NEW CERTIFIED THEOREM (complete, unconditional)

$$n_{21}=805,\qquad n_{22}=2691,\qquad n_{23}=1884,\qquad n_{24}=2664 .$$

The certified frontier of #451 now reads (k = 2..24):
6, 9, 20, 13, 21, 21, 22, 65, 220, 51, 338, 133, 321, 339, 340, 113, 114,
368, 550, **805, 2691, 1884, 2664**.

Definition (Erdos451.lean §0 header, verbatim corpus statement): n_k is the
smallest integer > 2k such that P(n_k) = ∏_{1≤i≤k}(n_k − i) has no prime
factor in the open interval (k, 2k).

## The certificate (per new row: witness + exclusion, dual code paths)

| k | primes in (k, 2k) | n_k | witness residues n_k mod p (all outside [1,k]) |
|---|---|---|---|
| 21 | 23, 29, 31, 37, 41 | 805 | 0, 22, 30, 28, 26 |
| 22 | 23, 29, 31, 37, 41, 43 | 2691 | 0, 23, 25, 27, 26, 25 |
| 23 | 29, 31, 37, 41, 43 | 1884 | 28, 24, 34, 39, 35 |
| 24 | 29, 31, 37, 41, 43, 47 | 2664 | 25, 29, 0, 40, 41, 32 |

**Witness law (direct product formulation):** at each n_k the literal
product P(n_k) = ∏_{1≤i≤k}(n_k − i) is computed and checked against every
prime p ∈ (k, 2k): none divides it (asserted per prime).

**Exclusion law (direct):** every 2k < m < n_k has SOME prime p ∈ (k, 2k)
dividing P(m) — the same direct-product route scans from 2k+1 upward, each
m before the witness is machine-checked to carry a window-prime factor.

**Dual independent code paths, agreement on every row:**
- Path A — the modular criterion (Erdos451.lean `erdos451_crit`, general):
  for prime p ∈ (k, 2k) (so k < p), p | ∏_{i=1}^{k}(n−i) ⟺ n mod p ∈ {1,…,k}
  (Euclid + the residue shift; backward: the residue itself is a factor
  index). Hence n_k = least n > 2k with n mod p ∉ [1,k] for all window
  primes. Scan n = 2k+1, 2k+2, ….
- Path B — the direct product route (the definition, factor-free): literal
  product divisibility as above.
Both methods return the same value on every k = 2..24 (asserted equal; the
battery aborts on any mismatch). 22/22 rows dual-GREEN.

## Termination of the search (elementary)

n = M := ∏_{p ∈ (k,2k)} p satisfies n mod p = 0 ∉ [1,k] for every window
prime, so a witness always exists ≤ max(2k+1, M); the scans terminated at
805 / 2691 / 1884 / 2664, far below their caps.

## Honest scope

Each new value is a certified exact value of n_k at the stated k — "the
certified frontier extended to k = 24". The general asymptotics of n_k (the
corpus's open estimation ask) remain open and are not claimed. The Lean-side
decide rows for k = 21..24 (the Erdos451_Data table extension) are the
optional next step — the Python dual-method machine certificate above is
complete as it stands.
