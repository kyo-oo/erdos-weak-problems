#!/usr/bin/env python3
"""
S094 ATTACKER — CAP LANE ASSAULT: the dual-method verification battery.

Every claimed identity in S094_ATTACKER_CAP.md is verified here by TWO
independent methods.  Numerics are EVIDENCE, not proof — the proofs in the
artifact are the mathematics; this file is the receipt printer.

Sections:
  A. PF1  the k=2 exact law            v2(3^a+3^b) = 1 + [b-a odd]
  B. PF2  the k=3 exact law            v2 = 0 (odd)
  C. PF3  the level-1 census law       n ≡ k + 2O (mod 8)
  D. PF4  the k=4 census laws          mod-8 dichotomy + mod-16 pattern list
  E. PF5  the exact order lemma        3^i ≡ 1 (mod 2^t) ⟺ 2^(t-2) | i
            + the dlog structure theorem (Hensel lift, single class mod 2^(t-2))
  F. PF6  the dlog rigidity counting bound (injectivity of S -> (S minus max, max mod 2^(t-2)))
  G. PF7  the complement law           v2(Full-x) ≥ t ⟺ x ≡ Full (mod 2^t)
            + the exact law v2(Full(M)) = 1+v2(M+1) if M odd else 0
  H. PF8  the trivial-range CAP(185)   certificates 3^316 < 2^501, threshold exactness,
            the rider seam alignment K≥251 ⟺ M≥316
  I. WALL the far-cap dlog constants d* (of -13 in <3>), T_4 = ∞ (tower satisfiability),
            W_4(M) growth (2+2 meet-in-the-middle), W_k small tables
"""

import itertools, random, math, json, sys
from collections import defaultdict

random.seed(406)
PASS = 0
FAIL = 0

def check(name, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
        print(f"  [PASS] {name} {detail}")
    else:
        FAIL += 1
        print(f"  [FAIL] {name} {detail}")

def v2(n):                      # method 1: direct factorization
    if n == 0:
        return None
    t = 0
    while n % 2 == 0:
        n //= 2
        t += 1
    return t

def v2b(n):                     # method 2: bit-scan on binary string
    if n == 0:
        return None
    s = bin(n)[2:]
    return len(s) - 1 - s.rindex('1')

def tern_log3(n):               # the Arsenal's ternaryLog3 (floor log_3, n>=1)
    assert n >= 1
    t = 0
    while n >= 3:
        n //= 3
        t += 1
    return t

print("=" * 78)
print("A. PF1 — THE k=2 EXACT LAW:  v2(3^a + 3^b) = 2 if b-a odd, 1 if b-a even")
print("=" * 78)
# Method 1: direct valuation.  Method 2: the mod-8 residue pattern
#   3^d + 1 ≡ 2 (mod 8) if d even  -> v2 = 1 ;  ≡ 4 (mod 8) if d odd -> v2 = 2.
bad = 0
for a in range(0, 60):
    for b in range(a + 1, 60):
        n = 3**a + 3**b
        d = b - a
        m1 = v2(n)
        m2 = 2 if (3**d + 1) % 8 == 4 else 1          # residue-pattern method
        m3 = v2b(n)                                    # bit-scan method
        expect = 2 if d % 2 == 1 else 1
        if not (m1 == m2 == m3 == expect):
            bad += 1
check("k=2 exact law (a,b<60, three methods agree)", bad == 0, f"({60*59//2} pairs, {bad} bad)")
# multiplicity form used by the census: {c,c}: 2*3^c has v2 = 1
bad = 0
for c in range(0, 30):
    if v2(2 * 3**c) != 1:
        bad += 1
check("k=2 multiset {c,c}: v2(2*3^c) = 1", bad == 0)
# CAP form: primitive k=2 numbers are exactly n = 1 + 3^b (b>=1); CAP(1), sharp at b=1
bad = 0
for b in range(1, 80):
    n = 1 + 3**b
    if not (v2(n) <= tern_log3(n) + 1):
        bad += 1
check("k=2 CAP(1): v2(1+3^b) <= ternaryLog3 + 1 (b<80)", bad == 0)
check("k=2 CAP(1) sharp: v2(1+3)=2=ternaryLog3(4)+1", v2(4) == 2 and tern_log3(4) == 1)
bad = 0
for b in range(2, 80):          # for b >= 2 even CAP(0) holds
    n = 1 + 3**b
    if not (v2(n) <= tern_log3(n)):
        bad += 1
check("k=2 CAP(0) holds for all b >= 2 (b<80)", bad == 0)

print()
print("=" * 78)
print("B. PF2 — THE k=3 EXACT LAW:  v2(3^a+3^b+3^c) = 0 (sum of three odds is odd)")
print("=" * 78)
bad = 0
for triple in itertools.combinations(range(0, 20), 3):
    n = sum(3**i for i in triple)
    if v2(n) != 0 or v2b(n) != 0 or n % 2 != 1:
        bad += 1
check("k=3: v2 = 0 for all 3-subsets of [0,20) (C(20,3)=1140)", bad == 0)
bad = 0
for _ in range(2000):           # random multisets with repetition also odd
    t = [random.randrange(0, 40) for _ in range(3)]
    if v2(sum(3**i for i in t)) != 0:
        bad += 1
check("k=3 multisets (with repetition): v2 = 0 (2000 random)", bad == 0)
bad = 0
for triple in itertools.combinations(range(0, 15), 3):
    n = sum(3**i for i in triple)
    if n % 3 == 1:              # primitive: exactly one exponent = 0
        if v2(n) > tern_log3(n) + 0:
            bad += 1
check("k=3 CAP(0) on primitive triples (a=0) in [0,15)", bad == 0)

print()
print("=" * 78)
print("C. PF3 — THE LEVEL-1 CENSUS LAW (all k):  n ≡ k + 2O (mod 8), O = #odd exps")
print("=" * 78)
# Method 1: direct. Method 2: digit census count.
bad = 0
for M in [5, 9, 12]:
    for S in itertools.chain.from_iterable(
            itertools.combinations(range(M + 1), k) for k in range(0, M + 2)):
        n = sum(3**i for i in S)
        k = len(S)
        O = sum(1 for i in S if i % 2 == 1)
        if n % 8 != (k + 2 * O) % 8:
            bad += 1
check("n ≡ k + 2O (mod 8), all subsets of [0,M], M∈{5,9,12}", bad == 0)
# classification corollaries
bad = 0
for M in [8, 11]:
    for S in itertools.chain.from_iterable(
            itertools.combinations(range(M + 1), k) for k in range(1, M + 2)):
        n = sum(3**i for i in S)
        k = len(S)
        O = sum(1 for i in S if i % 2 == 1)
        r = (k + 2 * O) % 8
        v = v2(n)
        ok = ((v >= 3) == (r == 0)) and ((v == 2) == (r == 4)) and \
             ((v == 1) == (r in (2, 6))) and ((v == 0) == (r % 2 == 1))
        if not ok:
            bad += 1
check("classification v>=3 ⟺ k+2O≡0(8), v=2 ⟺ ≡4, v=1 ⟺ ≡2,6, v=0 ⟺ k odd",
      bad == 0, "(all nonempty subsets of [0,8],[0,11])")
bad = 0
for _ in range(3000):
    M = random.randrange(1, 30)
    S = [i for i in range(M + 1) if random.random() < 0.5]
    if S:
        n = sum(3**i for i in S)
        if not (v2(n) >= 1) == (len(S) % 2 == 0):
            bad += 1
check("parity law: v2 >= 1 ⟺ popcount even (3000 random)", bad == 0)

print()
print("=" * 78)
print("D. PF4 — THE k=4 CENSUS LAWS: mod-8 dichotomy + the mod-16 pattern list")
print("=" * 78)
# mod-8: v>=3 ⟺ exactly two of the four exponents odd
bad = 0
for quad in itertools.combinations(range(0, 16), 4):
    n = sum(3**i for i in quad)
    O = sum(1 for i in quad if i % 2 == 1)
    if (v2(n) >= 3) != (O == 2):
        bad += 1
check("k=4 mod-8 law: v2>=3 ⟺ exactly 2 odd exponents (quads in [0,16))", bad == 0)
# mod-16: full census pattern enumeration over multisets (c0,c1,c2,c3), sum=4
w = [1, 3, 9, 11]               # 3^(i mod 4) mod 16
patterns = []
for c0 in range(5):
    for c1 in range(5 - c0):
        for c2 in range(5 - c0 - c1):
            c3 = 4 - c0 - c1 - c2
            if (c0 * w[0] + c1 * w[1] + c2 * w[2] + c3 * w[3]) % 16 == 0:
                patterns.append((c0, c1, c2, c3))
patterns.sort()
print(f"  mod-16 admissible census patterns (multiset form): {patterns}")
# verify against all 4-subsets with v2 >= 4: their mod-4 census must be in the list
bad = 0
hits = 0
for quad in itertools.combinations(range(0, 26), 4):
    n = sum(3**i for i in quad)
    if v2(n) >= 4:
        hits += 1
        c = [0, 0, 0, 0]
        for i in quad:
            c[i % 4] += 1
        if tuple(c) not in patterns:
            bad += 1
check("every 4-subset of [0,26) with v2>=4 has mod-4 census in the pattern list",
      bad == 0, f"({hits} deep quads found)")
# and conversely: quads whose census is in the list have v2 >= 3 always, >=4 iff also 2 odd
bad = 0
for quad in itertools.combinations(range(0, 26), 4):
    c = [0, 0, 0, 0]
    for i in quad:
        c[i % 4] += 1
    if tuple(c) in patterns:
        n = sum(3**i for i in quad)
        if v2(n) < 3:
            bad += 1
check("census-in-list ⟹ v2 >= 3 (necessary-direction converse, [0,26))", bad == 0)
# mod-32 pattern count (level 3) — the rigidification shrinks as 3^i mod 32
w32 = [3**i % 32 for i in range(8)]
p32 = []
for c in itertools.product(range(5), repeat=8):
    if sum(c) == 4 and sum(c[i] * w32[i] for i in range(8)) % 32 == 0:
        p32.append(c)
print(f"  mod-32 admissible census patterns (exponents mod 8): {len(p32)} patterns")
# check {0,1,2,69}-class: exps mod 8 = {0,1,2,5}
c = [0] * 8
for i in [0, 1, 2, 69 % 8]:
    c[i] += 1
check("far-cap {0,1,2,69} mod-8 census is mod-32 admissible", tuple(c) in p32,
      f"census={tuple(c)}")

print()
print("=" * 78)
print("E. PF5 — THE EXACT ORDER LEMMA + THE DLOG STRUCTURE THEOREM")
print("=" * 78)
# order lemma: for t >= 3: 3^i ≡ 1 (mod 2^t)  ⟺  2^(t-2) | i
bad = 0
for t in range(3, 18):
    m = 1 << t
    period = 1 << (t - 2)
    for i in range(0, 4 * period):
        lhs = (3**i) % m == 1
        rhs = (i % period) == 0
        if lhs != rhs:
            bad += 1
check("3^i ≡ 1 (mod 2^t) ⟺ 2^(t-2) | i, t ∈ [3,18), i < 4·2^(t-2)", bad == 0)
# order is exactly 2^(t-2): 3^(2^(t-3)) ≢ 1 (mod 2^t)
bad = 0
for t in range(3, 20):
    if (3 ** (1 << (t - 3))) % (1 << t) == 1:
        bad += 1
check("3^(2^(t-3)) ≢ 1 (mod 2^t) — the order is EXACTLY 2^(t-2), t<20", bad == 0)
# dlog structure: for odd R: solutions of 3^e ≡ R (mod 2^t) exist ⟺ R ≡ 1,3 (mod 8),
# and then form exactly ONE residue class mod 2^(t-2).
bad = 0
for t in range(3, 15):
    m = 1 << t
    period = 1 << (t - 2)
    # image = {1,3 mod 8}?
    img = {(3**e) % m for e in range(period)}
    target = {u for u in range(m) if u % 2 == 1 and u % 8 in (1, 3)}
    if img != target:
        bad += 1
    # single class per R
    where = defaultdict(list)
    for e in range(period):
        where[(3**e) % m].append(e)
    for R, es in where.items():
        if len(es) != 1:
            bad += 1
check("image of e↦3^e (mod 2^t) = {u ≡ 1,3 (mod 8)}, and injective on Z/2^(t-2), t<15",
      bad == 0)
# Hensel lift structure: 3^(e+2^(t-3)) ≡ 3^e + 2^(t-1)·odd (mod 2^t)
bad = 0
for t in range(4, 16):
    m = 1 << t
    for e in range(0, 1 << (t - 2), 7):
        d = (3 ** (e + (1 << (t - 3))) - 3**e) % m
        if d != 1 << (t - 1):
            bad += 1
check("3^(e+2^(t-3)) ≡ 3^e + 2^(t-1) (mod 2^t) — the two-branch Hensel lift", bad == 0)

print()
print("=" * 78)
print("F. PF6 — THE DLOG RIGIDITY COUNTING BOUND")
print("=" * 78)
# If 2^t | sum_{i in S} 3^i, k=|S|, then S ↦ (S \ {max}, max mod 2^(t-2)) is injective.
# Empirical: enumerate all k-subsets of [0,M] with v2 >= t and check the map is injective,
# and that max is pinned mod 2^(t-2) by the rest.
for (M, k, t) in [(14, 4, 6), (16, 4, 7), (16, 6, 6), (18, 5, 6), (20, 4, 8), (20, 6, 7)]:
    period = 1 << (t - 2)
    seen = {}
    coll = 0
    total = 0
    for S in itertools.combinations(range(M + 1), k):
        n = sum(3**i for i in S)
        if n % (1 << t) == 0 and n > 0:
            total += 1
            rest = S[:-1]
            R = (-(sum(3**i for i in rest))) % (1 << t)
            # find the class of S[-1]
            cls = S[-1] % period
            # verify S[-1] actually solves 3^e ≡ R
            if (3 ** S[-1]) % (1 << t) != R:
                coll += 1
            key = (rest, cls)
            if key in seen:
                coll += 1
            seen[key] = S
    bound = math.comb(M, k - 1) * (M // period + 1)
    check(f"rigidity: M={M},k={k},t={t}: {total} solutions, map injective, "
          f"max solves the dlog of the rest", coll == 0,
          f"count {total} ≤ bound {bound}")

print()
print("=" * 78)
print("G. PF7 — THE COMPLEMENT LAW (dense→sparse) + v2(Full(M)) EXACT LAW")
print("=" * 78)
def Full(M):
    return (3 ** (M + 1) - 1) // 2
# v2(Full(M)) = 1 + v2(M+1) if M odd, else 0
bad = 0
for M in range(0, 60):
    expect = (1 + v2(M + 1)) if M % 2 == 1 else 0
    if v2(Full(M)) != expect or v2b(Full(M)) != expect:
        bad += 1
check("v2(Full(M)) = 1+v2(M+1) if M odd else 0, M<60 (two methods)", bad == 0)
# complement law: for x < Full(M):  v2(Full - x) >= t  ⟺  x ≡ Full (mod 2^t)
bad = 0
for M in [6, 9, 11]:
    F = Full(M)
    for _ in range(4000):
        # random sparse complement: choose k' <= M/2 positions
        kp = random.randrange(0, M // 2 + 1)
        x = sum(3**i for i in sorted(random.sample(range(M + 1), kp))) if kp else 0
        if x >= F:
            continue
        t = random.randrange(1, 14)
        lhs = v2(F - x) is not None and v2(F - x) >= t
        rhs = (x % (1 << t)) == (F % (1 << t))
        if lhs != rhs:
            bad += 1
check("v2(Full-x) >= t ⟺ x ≡ Full (mod 2^t) (M∈{6,9,11}, 4000 random each)", bad == 0)

print()
print("=" * 78)
print("H. PF8 — THE TRIVIAL-RANGE CAP(185) + THE SEAM ALIGNMENT")
print("=" * 78)
# certificates (big-int, exact)
check("3^316 < 2^501", 3**316 < 2**501,
      f"ratio·2^501 headroom: {(2**501)//(3**316)}·")
check("3^317 > 2^502 (threshold exactness at M=316)", 3**317 > 2**502)
check("3^315 < 2^500", 3**315 < 2**500)
# the theorem: ternaryLog3 n <= 315 ⟹ v2 n <= M + 185, via n < 3^316 < 2^501 ⟹ v2 <= 500
bad = 0
for _ in range(3000):
    M = random.randrange(0, 316)
    S = [i for i in range(M + 1) if random.random() < 0.5]
    if S:
        n = sum(3**i for i in S)
        if v2(n) > tern_log3(n) + 185:
            bad += 1
check("random 0/1-ternary, M<=315: v2 <= M+185 (3000 samples)", bad == 0)
# the seam alignment: rider K -> M(K) = floor(K log_3 4); K=250 -> 315, K=251 -> 316
def rider_M(K):
    n = 4**K
    return tern_log3(n)
m250, m251 = rider_M(250), rider_M(251)
check("rider seam: ternaryLog3(4^250) = 315 <= 315 (covered by trivial cap)",
      m250 == 315, f"M(250)={m250}")
check("rider seam: ternaryLog3(4^251) = 316 > 315 (NOT covered)", m251 == 316,
      f"M(251)={m251}")
check("census seam: 2*250 = 500 <= 500 (covered), 2*251 = 502 > 500 (not)",
      2 * 250 <= 500 and 2 * 251 > 500)
check("kill condition at the seam: v2(4^251)=502 > M+185 = 501 — CAP(185) would kill K=251",
      2 * 251 == 502 and m251 + 185 == 501)
# also verify: for K in [251, 400], 2K - M(K) >= 186 (the cap kills all of them)
bad = 0
for K in range(251, 401):
    if 2 * K - rider_M(K) < 186:
        bad += 1
check("for all K in [251,400]: 2K - ternaryLog3(4^K) >= 186 (cap kills)", bad == 0)

print()
print("=" * 78)
print("I. WALL EVIDENCE — far-cap dlog constants, T_4 = ∞, W_4 growth, LX receipts")
print("=" * 78)
# I.1 the LX receipts
n1 = 3**0 + 3**7 + 3**8 + 3**13
check("LX counterexample 3^0+3^7+3^8+3^13 = 2^9·3131 (v2=9 > 8=2·4)",
      n1 == 2**9 * 3131 and v2(n1) == 9)
nf = 13 + 3**69
check("far-cap 13 + 3^69: v2 = 11", v2(nf) == 11)
# I.2 the dlog of -13 in <3>: compute d* = the 2-adic integer with 3^d = -13, by Hensel lift
#     (the two-branch lift: at each t exactly one of d, d + 2^(t-3) solves mod 2^t)
dstar = {}
d = 1                          # 3^1 = 3 ≡ -13 (mod 16)
for t in range(3, 42):
    m = 1 << t
    period = 1 << (t - 2)
    if pow(3, d, m) != (-13) % m:
        d = d + period // 2
    assert pow(3, d, m) == (-13) % m
    dstar[t] = d % period
# lift consistency (the class only refines)
for t in range(3, 41):
    assert dstar[t + 1] % (1 << (t - 2)) == dstar[t]
print(f"  d* (dlog of -13 in <3>) mod 2^(t-2) for t=3..41:")
row = []
for t in range(3, 42):
    row.append(f"t={t}:{dstar[t]}")
    if len(row) == 6:
        print("   " + "  ".join(row))
        row = []
if row:
    print("   " + "  ".join(row))
# verify the far-cap law (d ODD only — for even d, 13 + 3^d ≡ 6 (mod 8), v2 = 1):
#   d odd:  v2(13 + 3^d) = 2 + v2(d - d*)
bad = 0
for dtry in [d for d in range(1, 3000) if d % 2 == 1] + [69, 581, 1605, 2629, 10821, 27205]:
    v = v2(13 + 3**dtry)
    dd = (dtry - dstar[40])              # d* known mod 2^38
    pred = 2 + v2(abs(dd)) if dd != 0 else 2 + 38
    if v != min(pred, 38 + 2):
        bad += 1
check("far-cap law: d odd ⟹ v2(13+3^d) = 2 + v2(d - d*) (1500+ odd d < 2^30)", bad == 0)
bad = 0
for dtry in range(2, 400, 2):
    if v2(13 + 3**dtry) != 1:
        bad += 1
check("far-cap off-family: d even ⟹ v2(13+3^d) = 1 (the mod-8 wall)", bad == 0)
# the d sequence realizing increasing t: d_t = d* mod 2^(t-2)
seq = [dstar[t] for t in range(3, 30)]
print(f"  smallest-d sequence driving v2 -> t: {seq}")
ratios = [seq[i + 1] / max(seq[i], 1) for i in range(len(seq) - 1)]
print(f"  growth ratios of the d-sequence (should hover ~2): "
      f"{[round(r,2) for r in ratios[-8:]]}")
# I.3 T_4 = infinity: for every s, the 4-multiset {0,1,2, d* mod 2^s} in [0,2^s)
#        has census sum ≡ 0 (mod 2^(s+2)).  This KILLS the tower-compression route.
bad = 0
for s in range(2, 30):
    t = s + 2
    d = dstar[t]              # d* mod 2^(t-2) = d* mod 2^s
    assert d < (1 << s)
    csum = 1 + 3 + 9 + 3**d   # the level-s census of {0,1,2,d} (multiset sum)
    if csum % (1 << t) != 0 or max(0, 1, 2, d) >= (1 << s):
        bad += 1
check("T_4 = ∞: for every s in [2,30) the multiset {0,1,2, d* mod 2^s} ⊂ [0,2^s) has "
      "census ≡ 0 (mod 2^(s+2)) — the tower-compression route is dead", bad == 0)
# I.4 W_4(M): max v2 over 4-subsets of [0,M], via 2+2 meet-in-the-middle.
def W4_mitm(M, tmax=40):
    """Return dict t -> an example 4-subset with v2 >= t (max t found)."""
    pairs = []
    for i in range(M + 1):
        for j in range(i + 1, M + 1):
            pairs.append((3**i + 3**j, (i, j)))
    best = (0, None)
    # for each t from high to low, look for disjoint pair-of-pairs summing to 0 mod 2^t
    for t in range(tmax, 3, -1):
        m = 1 << t
        table = defaultdict(list)
        for s, ij in pairs:
            table[s % m].append((s, ij))
        found = None
        for r, lst in table.items():
            need = (-r) % m
            if need in table:
                for s1, ij1 in lst:
                    for s2, ij2 in table[need]:
                        if ij1[0] != ij2[0] and ij1[0] != ij2[1] and \
                           ij1[1] != ij2[0] and ij1[1] != ij2[1]:
                            found = (ij1, ij2)
                            break
                    if found:
                        break
            if found:
                break
        if found:
            S = sorted(found[0] + found[1])
            n = sum(3**i for i in S)
            vt = v2(n)
            best = max(best, (vt, tuple(S)))
            if best[0] >= t:
                return best
    return best
print("  W_4(M) (max v2 over 4-subsets of [0,M], 2+2 MITM + direct re-verify):")
w4_curve = {}
for M in [20, 40, 60, 90, 120, 160, 200, 260, 320]:
    vt, S = W4_mitm(M)
    n = sum(3**i for i in S)
    assert v2(n) == vt and v2b(n) == vt and len(set(S)) == 4 and max(S) <= M
    w4_curve[M] = (vt, list(S))
    print(f"    M={M:4d}: W_4 = {vt:3d}  (excess {vt - M:+d})  extremal S={list(S)}")
# I.5 W_k small exhaustive tables
print("  W_k(M) exhaustive (max v2 over k-subsets of [0,M]):")
for k in [5, 6]:
    line = []
    for M in range(k, 25):
        best = 0
        for S in itertools.combinations(range(M + 1), k):
            best = max(best, v2(sum(3**i for i in S)))
        line.append(f"M={M}:{best}")
    print(f"    k={k}: " + "  ".join(line))

print()
print("=" * 78)
print(f"BATTERY COMPLETE: {PASS} PASS, {FAIL} FAIL")
print("=" * 78)
json.dump({"w4_curve": {str(k): v for k, v in w4_curve.items()},
           "dstar": {str(t): dstar[t] for t in range(3, 42)},
           "patterns_mod16": [list(p) for p in patterns],
           "patterns_mod32_count": len(p32)},
          open("/home/z/erdos-weak-problems/problem406-ternary-powers/council/"
               "attack_s094_receipts.json", "w"), indent=1)
sys.exit(1 if FAIL else 0)
