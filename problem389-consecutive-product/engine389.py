#!/usr/bin/env python3
# engine389.py — W59-T4, Kernel 66 front (Erdos #389 consecutive-product divisibility).
#
# TARGET (corpus / FULL_PROOF_CAMPAIGN/P389/PROOF.md):
#   For every n >= 1 is there a k with  n(n+1)...(n+k-1) | (n+k)...(n+2k-1) ?
#   Corpus witnesses: n=2, k=5: 720 | 55440 ; n=3, k=4: 360 | 5040.
#   Minimal k for 1 <= n <= 18 = OEIS A375071 (Bhavik Mehta).
#
# THIS ENGINE: exact big-integer brute force — for each n in 1..18 find the
# minimal k (search 1..KMAX=200, exact division P2 % P1 == 0, no gcd tricks),
# plus the full witness data needed by Erdos389.lean:
#   * the A375071 table k(n) for n = 1..18,
#   * per-row failure of every 1 <= j < k(n),
#   * the two corpus witnesses (n,k) = (2,5), (3,4),
#   * count-machinery instances for the shift-law / sufficiency-law layer
#     (countQ q n k = #{multiples of q in [n, n+k)}, the multiplicity depth
#     of a single integer, and the block chains).
#
# Output: engine389_output.txt (banked alongside).

import sys

sys.set_int_max_str_digits(2_000_000)

KMAX = 4000
NMAX = 18


def prod_range(n: int, k: int) -> int:
    """prodRange n k = n * (n+1) * ... * (n+k-1)  (k factors; k=0 -> 1)."""
    r = 1
    for i in range(k):
        r *= n + i
    return r


def works(n: int, k: int) -> bool:
    """Exact divisibility test P1 | P2 (P1 = n..n+k-1, P2 = n+k..n+2k-1)."""
    if k < 1:
        return False  # the problem asks for a positive-length block
    P1 = prod_range(n, k)
    P2 = prod_range(n + k, k)
    return P2 % P1 == 0


def minimal_k(n: int, kmax: int = KMAX):
    for k in range(1, kmax + 1):
        if works(n, k):
            return k
    return None


def count_q(q: int, n: int, k: int) -> int:
    """countQ q n k = #{i in [0,k) : q | n+i} (multiples of q in [n, n+k))."""
    return sum(1 for i in range(k) if (n + i) % q == 0)


def m_count(q: int, m: int, E: int) -> int:
    """mCount q m E = #{e in [1,E] : q^e | m} (capped q-adic depth of m)."""
    return sum(1 for e in range(1, E + 1) if m % (q ** e) == 0)


def count_chain(q: int, n: int, k: int, E: int) -> int:
    """countChain q n k E = sum_{e=1}^{E} countQ (q^e) n k  (swap-free chain)."""
    return sum(count_q(q ** e, n, k) for e in range(1, E + 1))


def short(x: int) -> str:
    """Compact scientific view of a big integer."""
    if x < 10 ** 12:
        return str(x)
    s = str(x)
    return "%d.%se%d" % (int(s[0]), s[1:5], len(s) - 1)


def main():
    lines = []
    A = []
    # 1. THE A375071 TABLE (n = 1..18)
    lines.append("=== ENGINE389: minimal k(n), n = 1..%d, search k <= %d ===" % (NMAX, KMAX))
    for n in range(1, NMAX + 1):
        k = minimal_k(n)
        assert k is not None, "no k <= %d for n=%d (WIDEN THE SEARCH)" % (KMAX, n)
        A.append(k)
        lines.append("n=%2d  k=%d   P1~%s  P2~%s  ratio=%s"
                     % (n, k, short(prod_range(n, k)), short(prod_range(n + k, k)),
                        short(prod_range(n + k, k) // prod_range(n, k))))
    lines.append("A375071 (n=1..18): " + ",".join(str(x) for x in A))
    # 2. minimality: every 1 <= j < k(n) FAILS (row exclusion)
    lines.append("=== minimality rows: every 1 <= j < k(n) fails ===")
    ok = True
    for n in range(1, NMAX + 1):
        k = A[n - 1]
        fails = [j for j in range(1, k) if not works(n, j)]
        if len(fails) != k - 1:
            ok = False
            lines.append("ROW BREAK n=%d" % n)
        lines.append("n=%2d k=%2d : %d/%d smaller j fail"
                     % (n, k, len(fails), k - 1))
    lines.append("all minimality rows verified: %s" % ok)
    # 3. corpus witnesses
    lines.append("=== corpus witnesses ===")
    lines.append("n=2,k=5: P1=%d P2=%d divis=%s (720 | 55440 expected)"
                 % (prod_range(2, 5), prod_range(7, 5), works(2, 5)))
    lines.append("n=3,k=4: P1=%d P2=%d divis=%s (360 | 5040 expected)"
                 % (prod_range(3, 4), prod_range(7, 4), works(3, 4)))
    # 4. shift-law instances (q | k -> countQ q n k = countQ q (n+k) k)
    lines.append("=== shift-law instances ===")
    for (q, n, k) in [(5, 2, 5), (2, 3, 4), (4, 3, 4), (2, 6, 3), (3, 6, 3)]:
        if k % q == 0:
            lines.append("q=%d n=%d k=%d: countQ=%d countQshift=%d equal=%s"
                         % (q, n, k, count_q(q, n, k), count_q(q, n + k, k),
                            count_q(q, n, k) == count_q(q, n + k, k)))
    # 5. crown/chain instances: q-chain | k -> q^chain(n,k,E) | P2
    lines.append("=== crown-law instances (q^e | k for 1<=e<=E -> q^chain | P2) ===")
    for (q, n, k, E) in [(5, 2, 5, 1), (2, 3, 4, 2), (2, 3, 4, 1)]:
        chain_ok = all((k % (q ** e)) == 0 for e in range(1, E + 1))
        c = count_chain(q, n, k, E)
        P2 = prod_range(n + k, k)
        lines.append("q=%d n=%d k=%d E=%d: qchain|k=%s chain=%d q^chain=%d P2=%d divides=%s"
                     % (q, n, k, E, chain_ok, c, q ** c, P2, P2 % (q ** c) == 0))
    # 6. chain == sum of per-element capped depths (the mCount identity)
    lines.append("=== chain = sum of capped element depths (swap check) ===")
    for (q, n, k, E) in [(5, 2, 5, 1), (2, 3, 4, 2), (2, 3, 4, 1), (3, 1, 6, 2)]:
        lhs = count_chain(q, n, k, E)
        rhs = sum(m_count(q, n + i, E) for i in range(k))
        lines.append("q=%d n=%d k=%d E=%d: chain=%d elem-sum=%d equal=%s"
                     % (q, n, k, E, lhs, rhs, lhs == rhs))
    out = "\n".join(lines)
    print(out)
    with open("engine389_output.txt", "w") as f:
        f.write(out + "\n")


if __name__ == "__main__":
    main()
