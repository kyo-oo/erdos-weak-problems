#!/usr/bin/env python3
"""
ERDŐS #404 — THE FACTORIAL-SUM p-ADIC CLASSIFIER
================================================
Problem: For which (a, p) is sup_k { p^k | (a_1! + ... + a_n!) : a = a_1 < ... < a_n } finite?
Reduction (this session): sum = a! * (1 + sum_{i in B} P_i), P_i = (a+1)...i = i!/a!.
  f(a,p) = v_p(a!) + g(a,p),   g(a,p) = max { k : -1 in SubsetSums({P_i mod p^k}) }
  (empty B allowed -> g >= 0). If -1 reachable at level k then at all levels < k (reduction mod p^j).
  g = infinity  <=>  exists B (finite or infinite) with 1 + sum P_i = 0 in Z_p (compactness),
        and then the infinite chain a_1 < a_2 < ... with m_k -> infinity EXISTS.
Engine: exact bitset DP over the window [a+1, i_max(k)] where v_p(P_i) < k.
Zero floats. Pure ints. Deterministic.
"""
import sys
from math import isqrt

def vp_fact(n, p):
    """v_p(n!) exactly."""
    s = 0
    q = p
    while q <= n:
        s += n // q
        q *= p
    return s

def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(2, n + 1) if sieve[i]]

def window(a, p, k):
    """indices i in [a+1, i_max] with v_p(P_i) < k, where v_p(P_i) = vp_fact(i,p) - vp_fact(a,p)."""
    va = vp_fact(a, p)
    out = []
    i = a + 1
    while True:
        if vp_fact(i, p) - va < k:
            out.append(i)
            i += 1
        else:
            break
    return out

def P_mod(a, i, p, k):
    """P_i = i!/a! mod p^k, computed exactly (cancel the factorial division)."""
    m = p ** k
    r = 1
    for j in range(a + 1, i + 1):
        r = (r * (j % m)) % m
    return r

def reachable_minus1(a, p, k):
    """Is -1 (mod p^k) a subset sum of {P_i : i in window(a,p,k)}?  Bitset DP via Python ints."""
    m = p ** k
    idx = window(a, p, k)
    if not idx:
        return False, 0
    terms = [P_mod(a, i, p, k) for i in idx]
    R = 1  # bit r set <=> residue r reachable (0 reachable via empty subset)
    mask = (1 << m) - 1
    for t in terms:
        if t == 0:
            continue
        if t <= m - t:
            Rs = ((R << t) | (R >> (m - t))) & mask
        else:
            t2 = m - t
            Rs = ((R >> t2) | (R << (m - t2))) & mask
        R |= Rs
        if (R >> (m - 1)) & 1:
            return True, len(idx)
    return ((R >> (m - 1)) & 1) == 1, len(idx)

def g_value(a, p, max_bits=4*10**6, max_level=None):
    """g(a,p): first failing level minus 1. Returns (g, status)."""
    level = 1
    while True:
        if max_level and level > max_level:
            return level - 1, "DEPTH-LIMIT"
        if p ** level > max_bits:
            return level - 1, "BITS-LIMIT"
        ok, nterms = reachable_minus1(a, p, level)
        if not ok:
            return level - 1, "BOUNDED"
        level += 1

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "scan"
    if mode == "scan":
        print("=== BROAD SCAN: g(a,p), depth ~ p^k <= 4M ===")
        ps = primes_upto(61)
        print("a\\p " + " ".join(f"{p:>7}" for p in ps))
        for a in range(1, 41):
            row = []
            for p in ps:
                if (a + 1) % p == 0:
                    row.append("      0*")
                    continue
                g, status = g_value(a, p)
                row.append(f"{g:>7}" if status == "BOUNDED" else f"{g:>6}+")
            print(f"{a:>3} " + " ".join(row))
        print("(* = p | a+1 => g=0 PROVEN; N+ = unbounded candidate at scan depth)")
    elif mode == "deep":
        a, p = int(sys.argv[2]), int(sys.argv[3])
        maxb = int(sys.argv[4]) if len(sys.argv) > 4 else 2*10**8
        g, status = g_value(a, p, max_bits=maxb)
        print(f"g({a},{p}) = {g}  [{status}]   f = v_{p}({a}!) + g = {vp_fact(a,p)} + {g} = {vp_fact(a,p)+g}")
    elif mode == "witness":
        a, p, k = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        m = p ** k
        idx = window(a, p, k)
        target = m - 1
        cur = {0: []}
        for i in idx:
            t = P_mod(a, i, p, k)
            if t == 0: continue
            nxt = dict(cur)
            for r, sub in cur.items():
                r2 = (r + t) % m
                if r2 not in nxt:
                    nxt[r2] = sub + [i]
                    if r2 == target:
                        B = nxt[r2]
                        print("WITNESS B =", B)
                        chk = (1 + sum(P_mod(a, i, p, k) for i in B)) % m
                        print("check 1+sum(P_B) == 0 mod p^k:", chk == 0)
                        # exact integer check
                        big = 1
                        for i in B:
                            pr = 1
                            for j in range(a+1, i+1): pr *= j
                            big += pr
                        print("exact v_p(1 + sum P_B) =", vp_fact(0, p) if False else None)
                        from math import gcd
                        v = 0; x = big
                        while x % p == 0: x //= p; v += 1
                        print("exact v_p(1+sum P_B) =", v, " (claimed >= ", k, ")")
                        return
            cur = nxt
            if len(cur) > 3_000_000:
                print("memory cap at i =", i); return
        print("no witness at this level")
    elif mode == "verify-bounded":
        # exact certificate: g(a,p) = G with an explicit obstruction witness at level G+1
        a, p, G = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        k = G + 1
        m = p ** k
        idx = window(a, p, k)
        # full reachable set as residues (dict-based subset enumeration is too big; use bitset + decomposition)
        # For a CERTIFICATE: enumerate the reachable set of sums mod p^k restricted to the MOD p^{G+1} classes...
        # Simpler: bitset again but we also print the reachable residues mod p^{G+1} to show -1 missing.
        R = 1
        mask = (1 << m) - 1
        for i in idx:
            t = P_mod(a, i, p, k)
            if t == 0: continue
            if t <= m - t:
                R |= ((R << t) | (R >> (m - t))) & mask
            else:
                t2 = m - t
                R |= ((R >> t2) | (R << (m - t2))) & mask
        has = (R >> (m - 1)) & 1
        print(f"a={a} p={p} level {k}: -1 reachable = {has} (expect False)")
        print("number of reachable residues:", bin(R).count('1'), "of", m)

if __name__ == "__main__":
    main()
