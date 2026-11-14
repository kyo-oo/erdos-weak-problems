#!/usr/bin/env python3
# hunt939_w66_yes2.py — W66-P939-D YES-DIRECTION HUNT, part 2:
#   (D) LANE C — DISJOINT-PRIME-SUPPORT lattices: a from primes P, b from
#       primes Q, P ∩ Q = ∅  =>  gcd(a,b) = 1 BY CONSTRUCTION — any sum-hit
#       is an INSTANT pairwise-coprime counterexample. Swept to c <= 1e16.
#   (E) LANE CD — the c-driven x^4 lane: every 4-powerful c in (1e13, 1e15],
#       every x with x^4 < c, testing b = c - x^4 for 4-powerfulness
#       (covers ALL triples with a = x^4 and c an arbitrary 4-powerful <= 1e15;
#       subsumes the Nitaj-style b = k·y^4 lane in that window).
import sys, time
from math import gcd
from sympy import primerange, factorint

T0 = time.time()
LOG = open("hunt939_w66_yes2_output.txt", "w")
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True); LOG.write(s + "\n"); LOG.flush()

def iroot(n, k):
    r = int(round(n ** (1.0 / k)))
    while r ** k > n: r -= 1
    while (r + 1) ** k <= n: r += 1
    return r

def genA(limit, r=4):
    primes = list(primerange(2, iroot(limit, r) + 1))
    out = [1]
    def rec(i, val):
        for j in range(i, len(primes)):
            v = val * primes[j] ** r
            if v > limit:
                break
            while v <= limit:
                out.append(v)
                rec(j + 1, v)
                v *= primes[j]
    rec(0, 1)
    out.sort()
    return out

SMALLP = list(primerange(2, 101))

def is4powerful_quick2(n):
    """Strip by primes <= 100; residual 1, or >= 1e8 with all sympy-verified
    exponents >= 4. Sound and complete (residual < 1e8 with all factors > 100
    cannot have every exponent >= 4)."""
    if n == 1:
        return True
    if n < 16:
        return False
    for p in SMALLP:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p; e += 1
            if e < 4:
                return False
    if n == 1:
        return True
    if n < 100 ** 4:
        return False
    f = factorint(n)
    return all(e >= 4 for e in f.values())

# ================= (D) LANE C: disjoint-support lattices =================
P("=== (D) LANE C: disjoint-prime-support lattices, c <= 1e16, gcd = 1 BY CONSTRUCTION ===")
CMAX = 10 ** 16
S1 = [2, 3, 5, 7, 11, 13]
S2 = [17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

def lattice(primes, cap):
    """All prod p^e (e >= 4, p from `primes`) <= cap, sorted (excludes 1)."""
    out = []
    def rec(i, val):
        for j in range(i, len(primes)):
            v = val * primes[j] ** 4
            if v > cap:
                break
            while v <= cap:
                out.append(v)
                rec(j + 1, v)
                v *= primes[j]
    rec(0, 1)
    out.sort()
    return out

def lat1(p, cap):
    out = []
    v = p ** 4
    while v <= cap:
        out.append(v)
        v *= p
    return out

subsets = lambda S, k: [tuple(S[i:i + 1]) for i in range(len(S))] if k == 1 else \
    [ (S[i], S[j]) for i in range(len(S)) for j in range(i + 1, len(S)) ]

t = time.time()
hits = []
nch = 0
fams = 0
Popts = subsets(S1, 1) + subsets(S1, 2)
Qopts_S2 = subsets(S2, 1) + subsets(S2, 2)
for Pset in Popts:
    latP = lattice(list(Pset), CMAX)
    # Q from S2 (always disjoint from S1-based P)
    for Qset in Qopts_S2:
        latQ = lattice(list(Qset), CMAX)
        fams += 1
        for a in latP:
            for b in latQ:
                if a + b > CMAX:
                    break
                nch += 1
                if is4powerful_quick2(a + b):
                    hits.append((a, b, a + b, Pset, Qset))
    # Q from S1, disjoint from P
    for Qset in Popts:
        if set(Pset) & set(Qset):
            continue
        if tuple(sorted(Pset)) > tuple(sorted(Qset)):
            continue  # canonical: count each unordered family pair once
        latQ = lattice(list(Qset), CMAX)
        fams += 1
        for a in latP:
            for b in latQ:
                if a + b > CMAX:
                    break
                nch += 1
                if is4powerful_quick2(a + b):
                    hits.append((a, b, a + b, Pset, Qset))
P(f"  [C1] P <= 2 primes of {S1} x Q <= 2 primes of {S2} or S1-disjoint: "
  f"{fams} families, {nch} pair-sums tested, WITNESSES {len(hits)} "
  f"({time.time() - t:.1f}s)")
for h in hits[:10]:
    P(f"    *** {h} ***")

# C2: ALL unordered single-prime disjoint supports, p, q <= 200
t = time.time()
allp = list(primerange(2, 201))
hits2 = []
nch2 = 0
for i in range(len(allp)):
    for j in range(i + 1, len(allp)):
        p, q = allp[i], allp[j]
        la, lb = lat1(p, CMAX), lat1(q, CMAX)
        for a in la:
            for b in lb:
                if a + b > CMAX:
                    break
                nch2 += 1
                if is4powerful_quick2(a + b):
                    hits2.append((a, b, a + b, p, q))
P(f"  [C2] single-prime x single-prime, primes <= 200: "
  f"{len(allp)} primes, {nch2} pair-sums tested, WITNESSES {len(hits2)} "
  f"({time.time() - t:.1f}s)")
for h in hits2[:10]:
    P(f"    *** {h} ***")
P("  (any hit here is gcd(a,b) = 1 BY CONSTRUCTION — an instant counterexample)")

# ================= (E) LANE CD: c-driven x^4 lane, 1e13 < c <= 1e15 =================
P("=== (E) LANE CD: a = x^4, c any 4-powerful in (1e13, 1e15] — the x^4-lane ===")
t = time.time()
CL = [c for c in genA(10 ** 15) if c > 10 ** 13]
P(f"  c-values: {len(CL)} (4-powerfuls in (1e13, 1e15])")
F4 = [k ** 4 for k in range(1, iroot(10 ** 15, 4) + 1)]
hitsCD = []
nchCD = 0
copCD = []
for c in CL:
    for x4 in F4:
        if x4 >= c:
            break
        b = c - x4
        nchCD += 1
        if is4powerful_quick2(b):
            hitsCD.append((x4, b, c))
            if gcd(x4, b) == 1 and gcd(x4, c) == 1 and gcd(b, c) == 1:
                copCD.append((x4, b, c))
P(f"  (x, c) pairs tested: {nchCD}; b = c - x^4 4-powerful (sum-hits): {len(hitsCD)}; "
  f"COprime among them: {len(copCD)} ({time.time() - t:.1f}s)")
for h in hitsCD[:15]:
    P(f"    sum-hit: {h[0]} + {h[1]} = {h[2]}  gcd = {gcd(h[0], h[1])}")
for h in copCD[:10]:
    P(f"    *** COPRIME WITNESS {h} ***")
P(f"  hunt939_w66_yes2 total: {time.time() - T0:.1f}s")
LOG.close()
print("HUNT939_W66_YES2_DONE")
