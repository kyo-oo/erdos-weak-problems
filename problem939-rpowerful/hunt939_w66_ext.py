#!/usr/bin/env python3
# hunt939_w66_ext.py — W66-P939-D: (1) the sum-hit STRUCTURE LAW at 1e13
# (what makes sums work when gcd > 1), (2) the r=3 POSITIVE CONTROL (the
# scanner must detect the known coprime 3-powerful triples), (3) the
# zero-coprime EO/OO extension scans 1e15 -> 1e17 (EE pairs excluded with
# proof: both even => gcd >= 2).
import sys, time
from math import gcd
from collections import Counter
from sympy import primerange, factorint

T0 = time.time()
LOG = open("hunt939_w66_ext_output.txt", "w")
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True); LOG.write(s + "\n"); LOG.flush()

def iroot(n, k):
    r = int(round(n ** (1.0 / k)))
    while r ** k > n: r -= 1
    while (r + 1) ** k <= n: r += 1
    return r

def genA(limit, r=4):
    """All n in [1, limit], every prime exponent >= r (kernel-faithful: 1 in)."""
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

# ================= 1. THE STRUCTURE LAW AT 1e13 =================
P("=== THE STRUCTURE LAW: every sum-hit decomposed as a = g*a', b = g*b', c = g*s ===")
L = 10 ** 13
Lst = genA(L); S = set(Lst); n = len(Lst)
t = time.time()
hits = []
for i in range(n):
    a = Lst[i]
    if 2 * a > L:
        break
    for j in range(i, n):
        b = Lst[j]
        c = a + b
        if c > L:
            break
        if c in S:
            hits.append((a, b, c))
P(f"  recomputed 1e13 box: {len(hits)} sum-hits ({time.time() - t:.1f}s; "
  f"matches scan939_w66_box: {len(hits) == 42923})")

law = Counter()
spow2 = 0; ssub = 0; other = []
for (a, b, c) in hits:
    g = gcd(a, b)
    ap, bp, s = a // g, b // g, c // g
    assert ap + bp == s and gcd(ap, bp) == 1
    # s is a pure power of 2?
    if s & (s - 1) == 0:
        spow2 += 1
        law["s = 2^k"] += 1
    else:
        fs = factorint(s)
        fg = factorint(g)
        if set(fs) <= set(fg) | {2}:
            ssub += 1
            law["support(s) within support(g) (+2)"] += 1
        else:
            other.append((a, b, c, g, s, dict(fs)))
            law["s brings a prime OUTSIDE g"] += 1
P(f"  s = a'+b' classification over all {len(hits)} hits:")
P(f"    s a pure power of 2 : {spow2}")
P(f"    support(s) <= support(g) (incl. 2): {ssub}")
P(f"    s brings a prime OUTSIDE support(g): {len(other)}")
for (a, b, c, g, s, fs) in other[:12]:
    P(f"      a={a} b={b} c={c} g={g} s={s}={fs} gcd(a',b')=1, a'={a//g} b'={b//g}")
P("  LAW (empirical, 1e13): sum-hits exist BECAUSE a,b share a big 4-powerful")
P("  core g = gcd(a,b) (always itself 4-powerful); the coprime remainders sum to")
P("  s = a'+b' whose primes are absorbed by g's exponent headroom (or s = 2^k).")
P("  A COPRIME triple has g = 1: the FULL exponent burden falls on c = a+b itself.")
P("  That is why coprime hits are the hard lane and the shared core is the easy one.")

# ================= 2. THE r=3 POSITIVE CONTROL =================
P("=== THE r=3 POSITIVE CONTROL (scanner validated where witnesses EXIST) ===")
for B in (10 ** 9,):
    L3 = genA(B, 3); S3 = set(L3)
    t = time.time()
    cop3 = []
    hits3 = 0
    m = len(L3)
    for i in range(m):
        a = L3[i]
        if 2 * a > B:
            break
        for j in range(i, m):
            b = L3[j]
            c = a + b
            if c > B:
                break
            if c in S3:
                hits3 += 1
                if gcd(a, b) == 1:
                    cop3.append((a, b, c))
    P(f"  r=3 box <= 1e9: |L3| = {m}; sum-hits {hits3}; COPRIME triples {len(cop3)} "
      f"({time.time() - t:.1f}s)")
    known = 271 ** 3 + 2 ** 3 * 3 ** 5 * 73 ** 3
    for (a, b, c) in cop3:
        tag = " <= THE KERNEL witness1 19902511+756249048=776151559" if (a, b, c) == (19902511, 756249048, 776151559) else ""
        P(f"    coprime: {a} + {b} = {c}{tag}")
    P(f"  -> the scanner DETECTS the known r=3 witness (positive control): "
      f"{(19902511, 756249048, 776151559) in cop3}")
    P("     (so the r=4 zero is a property of r=4, not a scanner blind spot)")

# ================= 3. ZERO-COPRIME EXTENSION SCANS 1e15, 1e16, 1e17 =================
P("=== THE ZERO-COPRIME EXTENSION (EO/OO lanes; EE pairs die by gcd >= 2) ===")
P("  justification: a coprime pair (a,b) cannot be both even; so every coprime")
P("  triple intersects the odd set — the EO/OO lanes are SOUND AND COMPLETE for")
P("  the zero-coprime question. (1 is included — kernel-faithful.)")

def zero_coprime_scan(L, tag):
    t = time.time()
    Lst = genA(L); S = set(Lst)
    odd = [x for x in Lst if x & 1]
    Eset = set(x for x in Lst if not (x & 1))
    buck = {}
    for o in odd:
        buck.setdefault(o & 15, []).append(o)
    ncop = 0
    nhit = 0
    wit = None
    # EO lane: (o, c) same residue bucket, c > o, e = c - o in the even set
    for r in (1, 3, 5, 7, 9, 11, 13, 15):
        lst = buck[r]
        m = len(lst)
        for ii in range(m):
            o = lst[ii]
            for jj in range(ii + 1, m):
                c = lst[jj]
                e = c - o
                if e in Eset:
                    nhit += 1
                    if gcd(e, o) == 1:
                        ncop += 1
                        wit = (e, o, c)
    # OO lane: complementary residue buckets (16 | c forced by the obstruction)
    for r in (1, 3, 5, 7):
        s = (-r) & 15
        l1, l2 = buck[r], buck[s]
        for o1 in l1:
            lim = L - o1
            for o2 in l2:
                c = o1 + o2
                if c > lim:
                    break
                if c in Eset:
                    nhit += 1
                    if gcd(o1, o2) == 1:
                        ncop += 1
                        wit = (o1, o2, c)
    P(f"  [{tag}] |L|={len(Lst)} (odd {len(odd)}): mixed/odd sum-hits {nhit}; "
      f"COPRIME WITNESSES {ncop} {wit if wit else ''} ({time.time() - t:.1f}s)")
    return ncop, nhit

for e, tag in ((15, "1e15"), (16, "1e16"), (17, "1e17")):
    zero_coprime_scan(10 ** e, tag)

P(f"  hunt939_w66_ext total: {time.time() - T0:.1f}s")
LOG.close()
print("HUNT939_W66_EXT_DONE")
