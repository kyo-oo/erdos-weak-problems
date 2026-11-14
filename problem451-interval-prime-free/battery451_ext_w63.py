#!/usr/bin/env python3
"""BATTERY 451 EXTENSION W63 — the frontier extension k = 25..28.

(S063 W63 wave, task W63-C3.) The W62 volley certified n_21..n_24; this
battery extends the certified frontier four more rows with the SAME
dual-route discipline (per row: the modular criterion route vs the direct
product route; both must agree; exclusion completeness machine-checked per
row), under the CALIBRATION LAW: k = 2..24 re-derived and GREEN before any
new row is claimed.

Statement being certified (Erdos451.lean §0 header, the verbatim corpus
statement of erdosproblems.com/451):
  n_k = the smallest integer n > 2k such that
        P(n) = prod_{1<=i<=k} (n - i)
  has no prime factor in the open interval (k, 2k).

THE ROUTES (per row, all must agree):
  A (MODULAR — Erdos451.lean `erdos451_crit`, general): for prime p in
    (k,2k) — so k < p — p | P(n) iff n mod p in [1,k]. Hence
    n_k = least n > 2k with n mod p notin [1,k] for every window prime.
    Scan n = 2k+1, 2k+2, ...
  B (DIRECT PRODUCT — the definition, factor-free): at each candidate n the
    literal product P(n) = prod_{1<=i<=k}(n-i) is computed and divisibility
    by every prime p in (k,2k) is tested. n_k = first n with no window-prime
    factor; every 2k < m < n_k is machine-checked to carry one.
  C (MARKING SIEVE — the numpy cross-route): an independent boolean-array
    sieve marking the forbidden residue classes m = i (mod p), 1 <= i <= k,
    for every window prime; n_k = first unmarked n > 2k. Re-derivation of
    the value with a different algorithm.

RECEIPTS beyond the routes (the verification law):
  R1 window primes: trial division (routes A/B) vs gmpy2.is_prime — asserted
     identical lists;
  R2 the witness product: no window-prime factor checked directly
     (P(n_k) % p != 0 for all p) AND via gcd(P(n_k), M) = 1 where
     M = prod(window primes) — M's prime factors are exactly the window
     primes, so the gcd is 1 iff none of them divides P(n_k);
  R3 erdos451_crit validated EMPIRICALLY over the entire certified box, both
     directions, at every scanned m in (2k, n_k] and every window prime:
     (P(m) % p == 0) iff (m % p in [1,k]) — asserted per m (the routes are
     tied together at every point, not only at the final value);
  R4 boundary checks: n_k > 2k (the strict boundary of the definition),
     every scanned m >= 2k+1, the last excluded m = n_k-1 carries a
     window-prime factor, the witness carries none;
  R5 termination (elementary): M = prod(window primes) satisfies
     M % p = 0 notin [1,k] for every window prime, so a witness always
     exists <= M; every scan terminated far below its cap M.

Exit 0 iff ALL GREEN (calibration k=2..24 + the four new rows A=B=C).
"""
import sys


def primes_in(lo, hi):  # primes p with lo < p < hi — trial division
    out = []
    for p in range(lo + 1, hi):
        if p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1)):
            out.append(p)
    return out


def sieve_nk(k, cap):
    """MODULAR route (A): least n > 2k with n mod p notin [1,k] for every
    prime p in (k,2k).  (p | P(n) iff n mod p in [1,k] for k < p —
    Erdos451.lean `erdos451_crit`, general.)"""
    ps = primes_in(k, 2 * k)
    n = 2 * k + 1
    while n <= cap:
        if all(not (1 <= n % p <= k) for p in ps):
            return n, ps
        n += 1
    return None, ps


def P_of(n, k):
    P = 1
    for i in range(1, k + 1):
        P *= (n - i)
    return P


def direct_nk(k, cap):
    """DIRECT route (B — the definition): least n > 2k such that the literal
    P(n) = prod_{1<=i<=k}(n-i) has no prime factor in (k,2k) — divisibility
    of the literal product against every window prime.  Every 2k < m < n_k
    is certified to carry a window-prime factor (machine-checked per m, the
    count is returned).  cap = the a-priori CRT existence bound
    n = prod(window primes) (n mod p = 0 for all window primes).
    Receipt R3 rides along: the criterion equivalence (P(m)%p==0) iff
    (m%p in [1,k]) is asserted at EVERY scanned m, for every window prime,
    both directions."""
    ps = primes_in(k, 2 * k)
    M = 1
    for p in ps:
        M *= p
    cap = max(cap, M)
    witness = None
    excluded = 0
    for n in range(2 * k + 1, cap + 1):
        P = P_of(n, k)
        divs = [p for p in ps if P % p == 0]        # direct product route
        res_hit = [p for p in ps if 1 <= n % p <= k]  # modular criterion
        assert divs == res_hit, f"R3 criterion mismatch at k={k}, n={n}"
        if divs:
            excluded += 1
            continue
        witness = n
        break
    return witness, ps, excluded, M


def mark_nk(k, N):
    """MARKING route (C — the numpy cross-sieve): mark all m < N with
    m = i (mod p) for some window prime p and 1 <= i <= k; return the least
    unmarked n > 2k (plus the marked count in (2k, n_k) for the exclusion
    recount).  Independent algorithm: no per-n modular scan, no products."""
    import numpy as np
    ps = primes_in(k, 2 * k)
    arr = np.zeros(N, dtype=bool)
    for p in ps:
        idx = np.arange(1, k + 1)                          # residues 1..k
        t = np.arange(0, N // p + 1)                       # periods
        pos = (idx[:, None] + p * t[None, :]).ravel()
        pos = pos[pos < N]
        arr[pos] = True
    un = np.where(~arr)[0]
    un = un[un > 2 * k]
    n_c = int(un[0])
    marked_between = int(np.count_nonzero(arr[2 * k + 1:n_c]))
    return n_c, ps, marked_between


def main():
    expected = {2: 6, 3: 9, 4: 20, 5: 13, 6: 21, 7: 21, 8: 22, 9: 65,
                10: 220, 11: 51, 12: 338, 13: 133, 14: 321, 15: 339,
                16: 340, 17: 113, 18: 114, 19: 368, 20: 550,
                21: 805, 22: 2691, 23: 1884, 24: 2664}
    print("BATTERY451 EXTENSION W63 — the certified frontier extended to k = 25..28")
    print("(calibration k=2..24 against the certified table incl. the W62 rows,")
    print(" then the new rows; routes A modular / B direct product / C marking)")
    ok = True

    # ---------------- PHASE 1 — CALIBRATION k = 2..24 --------------------
    print("\nPHASE 1 — calibration (must be ALL GREEN before new rows are claimed)")
    print("k | n_k (A modular) | n_k (B direct) | expected | verdict")
    for k in range(2, 25):
        nk_mod, ps = sieve_nk(k, 10**9)
        nk_dir, _, excluded, M = direct_nk(k, 10**9)
        good = (nk_mod == nk_dir == expected[k])
        good = good and (excluded == nk_mod - 2 * k - 1)  # exclusion completeness
        ok = ok and good
        print(f"{k:2d} | {nk_mod:4d} | {nk_dir:4d} | {expected[k]:4d} | "
              + ("GREEN" if good else "RED"))
        if not good:
            print(f"  MISMATCH at k={k}: modular={nk_mod} direct={nk_dir} "
                  f"expected={expected[k]} excluded={excluded}")
    if not ok:
        print("\nBATTERY451 EXTENSION W63 RED — calibration FAILED, no new row claimed")
        sys.exit(1)
    print("calibration 23/23 GREEN (k=2..24, dual-route, exclusion counts exact)")

    # ---------------- PHASE 2 — THE NEW ROWS k = 25..28 -------------------
    print("\nPHASE 2 — the new rows")
    print("k | primes in (k,2k) | n_k (A) | n_k (B) | n_k (C) | verdict")
    newvals = {}
    for k in [25, 26, 27, 28]:
        nk_mod, ps = sieve_nk(k, 10**9)
        nk_dir, _, excluded, M = direct_nk(k, 10**9)
        nk_c, _, marked_between = mark_nk(k, 100000)
        good = (nk_mod == nk_dir == nk_c)
        good = good and (excluded == nk_mod - 2 * k - 1)
        good = good and (marked_between == nk_mod - 2 * k - 1)
        ok = ok and good
        newvals[k] = nk_mod
        tag = ("GREEN  *** NEW: n_%d = %d ***" % (k, nk_mod)) if good else "RED"
        print(f"{k:2d} | {ps} | {nk_mod:5d} | {nk_dir:5d} | {nk_c:5d} | {tag}")
        if not good:
            print(f"  MISMATCH at k={k}: modular={nk_mod} direct={nk_dir} "
                  f"marking={nk_c}")
        assert nk_mod > 2 * k, "boundary: n_k must exceed 2k (strictly)"

    # ---------------- PHASE 3 — the certificate tables --------------------
    print("\nWitness residue profiles for the frontier rows (n_k mod p outside [1,k]):")
    for k in [25, 26, 27, 28]:
        nk, ps = sieve_nk(k, 10**9)
        res = [nk % p for p in ps]
        assert all(not (1 <= r <= k) for r in res)
        # R2: direct product has no window-prime factor (re-checked here) ...
        P = P_of(nk, k)
        assert all(P % p != 0 for p in ps)
        # ... and the gcd receipt: gcd(P(n_k), M) = 1
        M = 1
        for p in ps:
            M *= p
        import gmpy2
        assert gmpy2.gcd(P, M) == 1, "R2 gcd receipt failed"
        # R1: window primes by trial division == gmpy2 primality
        assert [p for p in range(k + 1, 2 * k) if gmpy2.is_prime(p)] == ps
        # R5: the CRT termination witness M (M mod p = 0 notin [1,k])
        assert all(M % p == 0 for p in ps)
        print(f"  k={k:2d} n_k={nk:5d} residues={res}  [all outside [1,{k}]]"
              f"  gcd(P,M)=1  CRT-cap M={M}")

    print("\nBATTERY451 EXTENSION W63 " + ("GREEN — calibration k=2..24 intact + "
          "n_25=%d, n_26=%d, n_27=%d, n_28=%d certified triple-route"
          % (newvals[25], newvals[26], newvals[27], newvals[28])
          if ok else "RED"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
