#!/usr/bin/env python3
# scan939_w66_box.py — W66-P939-D Task 1: THE INDEPENDENT BOX SCANNER (r=4).
#
# Data structure: DISTINCT from every prior hunt engine in this repo:
#   - hunt939b/c: buggy fourth-power enumerators (FLT-void), sorted pair scan.
#   - hunt939d/e: numpy uint64 arrays + mod-16 bucketed EO/OO lanes.
#   - THIS scanner: python SET of 4-powerfuls (kernel-faithful, INCLUDING 1),
#     pair scan sorted-list-with-break (method 1) AND dict-of-lists mod-16
#     residue buckets (method 2) — pure python + sympy only, no numpy/gmpy2.
#
# TWO INDEPENDENT ENUMERATORS:
#   A: recursive prime-exponent enumeration (fresh implementation).
#   B: the r-powerful parametrization n = a^4 · b^5 · c^6 · d^7 (a different
#      mathematical decomposition — every exponent e >= 4 is a non-negative
#      combination of 4,5,6,7; every such product is 4-powerful, every
#      4-powerful has such a representation). Set equality A == B is a
#      generator-independence cross-check.
#
# Validations: Lean census row at 1e4; SPF-sieve brute force at 1e6;
# sympy.factorint of EVERY value at 1e13 (soundness, independent of both
# generators); c-driven pair enumeration at 1e6 (box method cross-check).
import sys, time
from math import gcd
from collections import Counter
from sympy import primerange, factorint

T0 = time.time()
LOG = open("scan939_w66_output.txt", "w")
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True); LOG.write(s + "\n"); LOG.flush()

LEAN_CENSUS_R4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048,
                  2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]

def iroot4(n):
    r = int(round(n ** 0.25))
    while r ** 4 > n: r -= 1
    while (r + 1) ** 4 <= n: r += 1
    return r

# ---------------- Enumerator A (fresh prime-exponent recursion) ----------------
def genA(limit):
    """All n in [1, limit] with every prime exponent >= 4 (kernel-faithful:
    includes n=1, matching rpow 4 1 = true)."""
    primes = list(primerange(2, iroot4(limit) + 1))
    out = [1]
    def rec(i, val):
        for j in range(i, len(primes)):
            p = primes[j]
            v = val * p ** 4
            if v > limit:
                break
            while v <= limit:
                out.append(v)
                rec(j + 1, v)
                v *= p
    rec(0, 1)
    out.sort()
    return out

# ---------------- Enumerator B (a^4 b^5 c^6 d^7 parametrization) ----------------
def genB(limit):
    """All products a^4 b^5 c^6 d^7 <= limit (set). Mathematically the same
    set as genA: sound (every prime exponent >= 4) and complete (every
    e >= 4 is 4alpha+5beta+6gamma+7delta). Includes 1."""
    out = set()
    a = 1
    while a ** 4 <= limit:
        r4 = a ** 4
        b = 1
        while r4 * b ** 5 <= limit:
            r5 = r4 * b ** 5
            c = 1
            while r5 * c ** 6 <= limit:
                r6 = r5 * c ** 6
                d = 1
                while r6 * d ** 7 <= limit:
                    out.add(r6 * d ** 7)
                    d += 1
                c += 1
            b += 1
        a += 1
    return out

# ---------------- PHASE 0: reproduce the prior-hunt FLT-void bug ----------------
P("=== PHASE 0: prior-hunt enumeration bug (AUDIT939_prior_hunt_bug.md) reproduced ===")
def gen_bug(limit):
    """The hunt939b/c generator: multiply by p^4 only -> exponents = multiples
    of 4 -> PERFECT FOURTH POWERS (the FLT-void set)."""
    primes = list(primerange(2, iroot4(limit) + 1))
    out = []
    def rec(i, val):
        for j in range(i, len(primes)):
            v = val * primes[j] ** 4
            if v > limit:
                break
            while v <= limit:
                out.append(v)
                rec(j + 1, v)
                v *= primes[j] ** 4      # <-- THE BUG (multiples of 4 only)
    rec(0, 1)
    out.sort()
    return out
bug = gen_bug(10 ** 13)
P(f"  buggy generator count <= 1e13: {len(bug)} (AUDIT939 says 1777 = #4th powers m^4, m=2..{iroot4(10**13)})")
P(f"  32 (=2^5, certified rpow 4 32 = true) in buggy list: {32 in bug} (must be False)")
P(f"  buggy list == [m^4 for m in 2..{iroot4(10**13)}]: "
  f"{bug == [m ** 4 for m in range(2, iroot4(10 ** 13) + 1)]}")
P(f"  2592 = 2^5*3^4 in buggy list: {2592 in bug} (must be False — census member missing)")

# ---------------- PHASE 1: enumerator validation ----------------
P("=== PHASE 1: enumerator validation ===")
A4 = genA(10 ** 4)
P(f"  genA(1e4) == Lean census row (incl. 1): {A4 == LEAN_CENSUS_R4}")
B4 = genB(10 ** 4)
P(f"  genB(1e4) == genA(1e4): {sorted(B4) == A4}")

# SPF sieve brute force (independent of both generators)
def spf_brute(limit):
    spf = list(range(limit + 1))
    for i in range(2, int(limit ** 0.5) + 1):
        if spf[i] == i:
            for k in range(i * i, limit + 1, i):
                if spf[k] == k:
                    spf[k] = i
    out = []
    for n in range(1, limit + 1):
        m = n
        ok = True
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p; e += 1
            if e < 4:
                ok = False; break
        if ok:
            out.append(n)
    return out
t = time.time()
brute6 = spf_brute(10 ** 6)
P(f"  SPF-sieve brute force <= 1e6: {len(brute6)} values == genA: {brute6 == genA(10 ** 6)} "
  f"({time.time() - t:.1f}s)")

A13 = genA(10 ** 13)
B13 = genB(10 ** 13)
P(f"  genA(1e13) count: {len(A13)}")
P(f"  genB(1e13) count (distinct): {len(B13)}")
P(f"  SET EQUALITY A == B at 1e13: {set(A13) == B13}")
t = time.time()
bad = [n for n in A13 if n > 1 and min(factorint(n).values()) < 4]
P(f"  sympy.factorint soundness of every genA value at 1e13: {len(bad)} failures "
  f"({time.time() - t:.1f}s) — every one of the {len(A13)} values (n >= 2; n = 1 is the")
P("  kernel-faithful vacuous member) re-derived by an independent factorization engine.")

# ---------------- PHASE 2: the count ladder 1e13..1e19 ----------------
P("=== PHASE 2: TRUE 4-powerful count ladder (enumerator A; B cross-check) ===")
REPO = {13: 11653, 15: 40048, 16: 73698, 17: 135058, 18: 246652, 19: 449087}
cntA = {}
for e in (13, 14, 15, 16, 17, 18, 19):
    t = time.time()
    cntA[e] = len(genA(10 ** e))
    verdict = "MATCH" if (REPO.get(e) is None or cntA[e] == REPO[e]) else f"MISMATCH (repo claims {REPO[e]})"
    P(f"  1e{e}: genA count = {cntA[e]}   {verdict}   ({time.time() - t:.1f}s)")
for e in (13, 15, 16):
    t = time.time()
    nB = len(genB(10 ** e))
    P(f"  1e{e}: genB count = {nB}   [cross-check vs A: "
      f"{'MATCH' if nB == cntA[e] else 'MISMATCH'}]   ({time.time() - t:.1f}s)")
P("  -> the W66 brief's '449,087 4-powerfuls <= 1e13' is FALSE as stated:")
P("     449,087 is the count <= 1e19 (the W64-I box bound). The count <= 1e13 is 11,653.")

# ---------------- PHASE 3: THE BOX AT 1e13 (the zero-coprime-witness claim) ----------------
P("=== PHASE 3: THE BOX c <= 1e13 — every pair (a,b), a <= b, a+b 4-powerful ===")
L = 10 ** 13
Lst = A13                      # sorted, includes 1 (kernel-faithful)
S = set(Lst)
n = len(Lst)
P(f"  |L| = {n} (with {sum(1 for x in Lst if x & 1)} odd, "
  f"{sum(1 for x in Lst if not x & 1)} even)")

# --- Method 1: full sorted pair scan with break (set membership) ---
t = time.time()
hits = []
npairs = 0
for i in range(n):
    a = Lst[i]
    if 2 * a > L:
        break
    for j in range(i, n):
        b = Lst[j]
        c = a + b
        if c > L:
            break
        npairs += 1
        if c in S:
            hits.append((a, b, c))
P(f"  [M1] full pair scan: {npairs} pairs with a+b <= 1e13 examined; "
  f"{len(hits)} sum-hits ({time.time() - t:.1f}s)")

# --- Method 2: dict-of-lists residue buckets (EO + OO lanes) ---
t = time.time()
odd = [x for x in Lst if x & 1]
even = [x for x in Lst if not (x & 1)]
Eset = set(even)
buck = {}
for o in odd:
    buck.setdefault(o & 15, []).append(o)
hits2 = []
# EO lane: e even (16 | e), o odd, c = e + o odd with c == o mod 16 ->
# (o, c) in the SAME residue bucket, c > o, e = c - o in the even set.
for r in (1, 3, 5, 7, 9, 11, 13, 15):
    lst = buck[r]
    m = len(lst)
    for ii in range(m):
        o = lst[ii]
        for jj in range(ii + 1, m):
            c = lst[jj]
            if (c - o) in Eset:
                hits2.append((min(o, c - o), max(o, c - o), c))
# OO lane: a, b odd, c = a+b even 4-powerful -> 16 | c (kernel mod16_obstruction)
# -> b = -a mod 16 -> COMPLEMENTARY residue buckets.
for r in (1, 3, 5, 7):
    s = (-r) & 15
    l1, l2 = buck[r], buck[s]
    for o1 in l1:
        for o2 in l2:
            c = o1 + o2
            if c <= L and c in Eset:
                hits2.append((min(o1, o2), max(o1, o2), c))
mixed_odd_1 = sorted([h for h in hits if h[0] & 1 or h[1] & 1])
mixed_odd_2 = sorted(hits2)
P(f"  [M2] dict-bucket lanes: {len(hits2)} mixed/odd sum-hits; M1 mixed/odd = "
  f"{len(mixed_odd_1)}; AGREEMENT (sorted lists equal): {mixed_odd_1 == mixed_odd_2} "
  f"({time.time() - t:.1f}s)")

# --- brute cross-check at 1e6: c-driven enumeration (a THIRD loop structure) ---
A6 = genA(10 ** 6); S6 = set(A6)
bh = []
for c in A6:
    for a in A6:
        if 2 * a > c:
            break
        b = c - a
        if b >= a and b in S6:
            bh.append((a, b, c))
m6 = [(a, b, a + b) for i, a in enumerate(A6) for b in A6[i:] if a + b <= 10 ** 6 and (a + b) in S6]
P(f"  [1e6 cross] c-driven enumeration: {len(bh)} hits; pair-driven: {len(m6)}; "
  f"AGREEMENT: {sorted(bh) == sorted(m6)}")

# --- THE VERDICT: gcd census over ALL sum-hits ---
P("=== PHASE 3b: gcd census of every sum-hit at 1e13 ===")
cop = []
for (a, b, c) in hits:
    g = gcd(a, b)
    if g == 1:
        cop.append((a, b, c))
P(f"  TOTAL sum-hits (a+b=c, all three 4-powerful, c <= 1e13): {len(hits)}")
P(f"  coprime witnesses among them (gcd(a,b) = 1): {len(cop)}")
P(f"  -> CLAIM 'every 4-powerful pair with 4-powerful sum has gcd > 1' at 1e13: "
  f"{'VERIFIED' if not cop else 'FALSIFIED — COUNTEREXAMPLES: ' + str(cop)}")
pw = [h for h in hits if gcd(h[0], h[1]) == 1 and gcd(h[0], h[2]) == 1 and gcd(h[1], h[2]) == 1]
P(f"  pairwise-coprime TRIPLES (all three gcds = 1): {len(pw)}  (== the gcd(a,b)=1 lane, "
  f"since gcd(a,c) = gcd(a,b) and gcd(b,c) = gcd(a,b) for c = a+b)")

# consecutive-4-powerful lane (pairs differing by 1 -> the a=1 witnesses)
consec = [(x, x + 1) for x in Lst if x + 1 in S]
P(f"  consecutive 4-powerful pairs <= 1e13 (the a=1 lane): {len(consec)} {consec[:5]}")

# --- gcd structure of the hits ---
P("=== PHASE 3c: shared-prime structure of the sum-hits ===")
gcd_hist = Counter()
for (a, b, c) in hits:
    f = factorint(gcd(a, b))
    gcd_hist[tuple(sorted(f.items()))] += 1
P(f"  distinct gcd factorizations: {len(gcd_hist)}")
for k, v in sorted(gcd_hist.items(), key=lambda kv: -kv[1])[:20]:
    P(f"    gcd = {dict(k)}: {v} hits")

def strip16(t):
    a, b, c = t
    k = 0
    while a % 16 == 0 and b % 16 == 0 and c % 16 == 0:
        a //= 16; b //= 16; c //= 16; k += 1
    return k, (a, b, c)
prim = Counter()
for t in hits:
    k, core = strip16(t)
    prim[core] += 1
P(f"  16-stripped hit cores (the x16-cascade roots): {len(prim)} distinct")
for core, cnt in sorted(prim.items()):
    fa, fb, fc = factorint(core[0]), factorint(core[1]), factorint(core[2])
    g = gcd(core[0], core[1])
    P(f"    core {core[0]} + {core[1]} = {core[2]}  gcd={g} ({dict(factorint(g))})  "
      f"{cnt} hit(s) above; a={dict(fa)} b={dict(fb)} c={dict(fc)}")
P(f"  scan939_w66_box total: {time.time() - T0:.1f}s")
LOG.close()
print("SCAN939_W66_DONE")
