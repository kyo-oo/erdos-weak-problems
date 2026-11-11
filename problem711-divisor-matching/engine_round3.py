#!/usr/bin/env python3
"""ENGINE ROUND 3 — S044-C. THEOREM U + THEOREM N under deeper water.

f(n,m) = minimal F such that the OPEN interval (m, m+F) contains distinct
a_1..a_n with k | a_k for all k <= n.  THEOREM U conjecture:
        f(n,m) <= 2n-1  for every n >= 2, m >= 1
(window (m, m+2n-1) = the 2n-2 integers m+1..m+2n-2).
THEOREM N conjecture: f(n,n) <= n+1-ish (any 2n-1-omega(1) bound).

Phases (run foreground, one per invocation, ~<=9 min each):
  A  full-period census n = 13..16 (L = 360360, 720720) + exact max f
  B  full-period census n = 17 (L = 12252240)
  C  full-period census n = 18 (L = 12252240)
  D  n = 19..22: small-m full sweep + random + adversarial m
  E  n = 23, 24: adversarial + random m
  F  THEOREM N: exact f(n,n) n=2..24 + bound classification
  G  Hall tightness probe: enumerate S subsets, find deficient/tight S
  H  greedy-vs-Kuhn: does descending-greatest greedy alone ever fail?

Usage: python3 engine_round3.py A   (letter phase)
Writes: engine_round3_<phase>.txt (append, flushed) + stdout.
"""
import sys, time, random
from math import gcd

BASE = "/home/z/my-project/repos/erdos-weak-problems/problem711-divisor-matching"
PHASE = sys.argv[1] if len(sys.argv) > 1 else "A"
LOG = open(f"{BASE}/engine_round3_{PHASE}.txt", "a", buffering=1)
random.seed(711711 + ord(PHASE[0]))

def log(s=""):
    print(s)
    LOG.write(s + "\n")

def lcm_upto(n):
    L = 1
    for k in range(1, n + 1):
        L = L * k // gcd(L, k)
    return L

def greedy(n, m, win):
    """Descending-greatest greedy on keys n..2; key 1 free (window>=n).
    Returns assignment dict or None."""
    lo, hi = m + 1, m + win
    used = set()
    for k in range(n, 1, -1):
        v = hi - hi % k
        while v >= lo and v in used:
            v -= k
        if v < lo:
            return None
        used.add(v)
    # key 1: any free integer (exists since win >= n)
    for v in range(lo, hi + 1):
        if v not in used:
            a = {1: v}
            a.update({k: None for k in range(2, 1)})
            return a
    return None

def greedy_ok(n, m, win):
    lo, hi = m + 1, m + win
    used = set()
    for k in range(n, 1, -1):
        v = hi - hi % k
        while v >= lo and v in used:
            v -= k
        if v < lo:
            return False
        used.add(v)
    return len(used) <= win  # key 1 has a free slot iff win >= n-... (win>=n)

def kuhn(n, m, win):
    """Exact bipartite matching, keys n..2 via Kuhn augmenting, key 1 free.
    Returns assignment or None."""
    lo, hi = m + 1, m + win
    matchR = {}   # value -> key
    def try_k(k, seen):
        v = lo + (-lo) % k if lo % k else lo
        v = lo + (k - lo % k) % k
        while v <= hi:
            if v not in seen:
                seen[v] = True
                if v not in matchR or try_k(matchR[v], seen):
                    matchR[v] = k
                    return True
            v += k
        return False
    for k in range(n, 1, -1):
        if not try_k(k, {}):
            return None
    assign = {vk[1]: vk[0] for vk in matchR.items()}
    for v in range(lo, hi + 1):
        if v not in matchR:
            assign[1] = v
            return assign
    return None

def matchable(n, m, win):
    if win < n:
        return None
    if greedy_ok(n, m, win):
        return "greedy"
    return kuhn(n, m, win)

def f711(n, m, cap):
    """Exact f(n,m) capped at cap (returns cap+1 if exceeds)."""
    F = n + 1
    while F <= cap:
        if matchable(n, m, F - 1) is not None:
            return F
        F += 1
    return None

def census(n, L, mlo, mhi, tag):
    """Full census over m in [mlo, mhi]: U-law + exact max + greedy stats."""
    t0 = time.time()
    badU = []       # m where f > 2n-1 (matchable fails at win 2n-2)
    greedyfail = 0  # greedy failed but kuhn saved
    kuhnbad = 0     # genuinely unmatchable at 2n-2 (THEOREM U violation)
    fmax = 0; farg = []
    cnt = mhi - mlo + 1
    for m in range(mlo, mhi + 1):
        # exact f up to 2n-1
        F = n + 1
        while F <= 2 * n - 1:
            if matchable(n, m, F - 1) is not None:
                break
            F += 1
        if F > 2 * n - 1:
            badU.append(m)
            if len(badU) > 4:
                break
            continue
        if F > fmax:
            fmax = F; farg = [m]
        elif F == fmax:
            if len(farg) < 6:
                farg.append(m)
        # greedy instrumentation at win 2n-2
        if not greedy_ok(n, m, 2 * n - 2):
            greedyfail += 1
    dt = time.time() - t0
    log(f"  [{tag}] n={n:2d} m in [{mlo:,},{mhi:,}] ({cnt:,} vals, {dt:.1f}s, "
        f"{cnt/max(dt,0.001):,.0f}/s): max f = {fmax} (2n-1={2*n-1}) "
        f"argmax~{farg[:6]} greedyFails={greedyfail} UVIOLATIONS={len(badU)} {badU[:5]}")
    return len(badU) == 0

# =============== PHASES ===============

if PHASE == "A":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE A: full-period census n = 13..16 + exact max")
    log("=" * 78)
    ok = True
    for n in range(13, 17):
        L = lcm_upto(n)
        ok &= census(n, L, 1, L, f"A/13-{n}")
    log("PHASE A VERDICT: " + ("THEOREM U CONFIRMED n=13..16 (full periods)" if ok else "U BROKEN — SEE ABOVE"))

elif PHASE == "B":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE B: full-period census n = 17 (L = 12,252,240)")
    log("=" * 78)
    n = 17; L = lcm_upto(n)
    # split into 4 chunks to stay under the time limit; run chunk by invocations B1..B4
    which = sys.argv[2] if len(sys.argv) > 2 else "1"
    parts = 4
    step = (L + parts - 1) // parts
    i = int(which) - 1
    lo = 1 + i * step
    hi = min(L, lo + step - 1)
    ok = census(n, L, lo, hi, f"B{which}")
    log(f"PHASE B{which} VERDICT: chunk done" + ("" if ok else " — U BROKEN HERE"))

elif PHASE == "C":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE C: full-period census n = 18 (L = 12,252,240)")
    log("=" * 78)
    n = 18; L = lcm_upto(n)
    which = sys.argv[2] if len(sys.argv) > 2 else "1"
    parts = 4
    step = (L + parts - 1) // parts
    i = int(which) - 1
    lo = 1 + i * step
    hi = min(L, lo + step - 1)
    ok = census(n, L, lo, hi, f"C{which}")
    log(f"PHASE C{which} VERDICT: chunk done" + ("" if ok else " — U BROKEN HERE"))

elif PHASE == "D":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE D: n = 19..22 adversarial + random + small-m sweep")
    log("=" * 78)
    okall = True
    for n in range(19, 23):
        W = 2 * n - 2
        tests = []
        # (i) full small-m sweep 1..2n^2+2n (the tight zone lives near squares)
        for m in range(1, 2 * n * n + 2 * n + 1):
            tests.append(m)
        # (ii) squares +/- j around and beyond the obstruction
        for k in range(max(2, n - 3), 4 * n + 2):
            for j in range(-2 * n, 2 * n + 1):
                mm = k * k + j
                if 1 <= mm:
                    tests.append(mm)
        # (iii) lcm-aligned adversarial
        Ls = [lcm_upto(min(n, 12)), 720720, 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19,
              2**21, 3**11, 2**6 * 3**4 * 5**3 * 7**2, 10**9, 10**12, 10**15]
        for M in Ls:
            for t in range(0, 40):
                for j in range(-2 * n, 2 * n + 1):
                    mm = M * t + j
                    if 1 <= mm:
                        tests.append(mm)
        # (iv) random m in [1, 10^9] and [1, 10^18]
        for _ in range(40000):
            tests.append(random.randint(1, 10**9))
        for _ in range(20000):
            tests.append(random.randint(1, 10**18))
        tests = sorted(set(tests))
        t0 = time.time()
        bad = []; gfail = 0
        for m in tests:
            if matchable(n, m, W) is None:
                bad.append(m)
                if len(bad) > 4: break
            elif not greedy_ok(n, m, W):
                gfail += 1
        log(f"  n={n:2d}: {len(tests):,} adversarial+random m "
            f"({time.time()-t0:.1f}s): UVIOLATIONS={len(bad)} {bad[:5]} greedyFails={gfail}")
        if bad: okall = False
    log("PHASE D VERDICT: " + ("THEOREM U CONFIRMED n=19..22 (adversarial)" if okall else "U BROKEN — SEE ABOVE"))

elif PHASE == "E":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE E: n = 23, 24 adversarial + random")
    log("=" * 78)
    okall = True
    for n in range(23, 25):
        W = 2 * n - 2
        tests = []
        for m in range(1, 2 * n * n + 2 * n + 1):
            tests.append(m)
        for k in range(max(2, n - 3), 4 * n + 2):
            for j in range(-2 * n, 2 * n + 1):
                mm = k * k + j
                if 1 <= mm:
                    tests.append(mm)
        Ls = [lcm_upto(12), 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23,
              2**22, 3**12, 2**7 * 3**5 * 5**4 * 7**3, 10**9, 10**12, 10**15, 10**18]
        for M in Ls:
            for t in range(0, 40):
                for j in range(-2 * n, 2 * n + 1):
                    mm = M * t + j
                    if 1 <= mm:
                        tests.append(mm)
        for _ in range(60000):
            tests.append(random.randint(1, 10**9))
        for _ in range(30000):
            tests.append(random.randint(1, 10**18))
        tests = sorted(set(tests))
        t0 = time.time()
        bad = []; gfail = 0
        for m in tests:
            if matchable(n, m, W) is None:
                bad.append(m)
                if len(bad) > 4: break
            elif not greedy_ok(n, m, W):
                gfail += 1
        log(f"  n={n:2d}: {len(tests):,} adversarial+random m "
            f"({time.time()-t0:.1f}s): UVIOLATIONS={len(bad)} {bad[:5]} greedyFails={gfail}")
        if bad: okall = False
    log("PHASE E VERDICT: " + ("THEOREM U CONFIRMED n=23,24 (adversarial)" if okall else "U BROKEN — SEE ABOVE"))

elif PHASE == "F":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE F: THEOREM N — exact f(n,n), n = 2..24")
    log("=" * 78)
    for n in range(2, 25):
        v = f711(n, n, 2 * n)   # exact, capped at 2n
        cls = []
        for bnd, name in [(n + 1, "n+1"), (n + 2, "n+2"), ((3 * n) // 2 + 1, "3n/2"),
                          (2 * n - 1, "2n-1")]:
            if v is not None and v <= bnd:
                cls.append(name)
        log(f"  f({n:2d},{n:2d}) = {v}   [2n-1 = {2*n-1}]   fits: {cls}")

elif PHASE == "G":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE G: Hall tightness probe (bitmask over S subsets)")
    log("=" * 78)
    def hall_probe(n, m, win, exhaustive_limit=2**14):
        """MAX over S != empty of (|S| - |N(S)|).  Positive = Hall failure."""
        pos = {}   # key k -> bitmask over window positions
        for k in range(2, n + 1):
            msk = 0
            for p in range(win):
                if (m + 1 + p) % k == 0:
                    msk |= 1 << p
            pos[k] = msk
        keys = sorted(pos)
        best = -10**9; bestS = None
        sub = (1 << (n - 1)) if n - 1 <= 15 else exhaustive_limit
        enum = range(1, 1 << (n - 1)) if n - 1 <= 15 else \
            [random.getrandbits(n - 1) | 1 for _ in range(exhaustive_limit)]
        for sb in enum:
            S = [keys[i] for i in range(n - 1) if sb >> i & 1]
            N = 0
            for i in range(n - 1):
                if sb >> i & 1:
                    N |= pos[keys[i]]
            d = len(S) - bin(N).count("1")
            if d > best:
                best, bestS = d, S
        return best, bestS
    # (a) obstruction window must FAIL Hall (sanity of the probe)
    for n in [5, 8, 10, 12]:
        b, S = hall_probe(n, (n - 1) * (n - 1), 2 * n - 3)
        log(f"  sanity n={n} m=(n-1)^2 win=2n-3: min deficiency = {b} at S={S}  (expect < 0)")
    # (b) the U window must PASS; find the TIGHTEST S (deficiency 0 with |S|>=2)
    for n in [5, 6, 7, 8, 9, 10, 11, 12]:
        worst = -10**9; wS = None; wm = None; cnt0 = 0
        for m in range(1, lcm_upto(n) + 1):
            b, S = hall_probe(n, m, 2 * n - 2)
            if b > worst:
                worst, wS, wm = b, S, m
            if b == 0 and len(S) >= 2:
                cnt0 += 1
        log(f"  n={n:2d} full period: max deficiency = {worst} (Hall {'OK' if worst <= 0 else 'FAILS'}) "
            f"tight S={wS} at m={wm}; #tight-S-cases={cnt0}")
    # (c) bigger n sampled
    for n in [13, 14, 15, 16]:
        worst = -10**9; wS = None; wm = None
        for m in [1, 7, 50, (n-1)*(n-1), (n-1)*(n-1)+1, (n-2)*(n-2), 10**6, 10**9, 12345678] + \
                 [random.randint(1, 10**9) for _ in range(30)]:
            b, S = hall_probe(n, m, 2 * n - 2, exhaustive_limit=6000)
            if b > worst:
                worst, wS, wm = b, S, m
        log(f"  n={n:2d} sampled: max deficiency = {worst} tight S={wS} at m={wm}")
    # (d) census of the TIGHT S structure: all m in a full period with n=8..
    for n in [8, 10, 12]:
        L = lcm_upto(n)
        seen = {}
        for m in range(1, L + 1):
            b, S = hall_probe(n, m, 2 * n - 2)
            if b == 0:
                key = tuple(S)
                seen[key] = seen.get(key, 0) + 1
        top = sorted(seen.items(), key=lambda kv: -kv[1])[:12]
        log(f"  n={n:2d}: tight S multiset over full period: {top}")

elif PHASE == "H":
    log("=" * 78)
    log("ENGINE ROUND 3 / PHASE H: greedy-alone census n=2..16 full periods")
    log("=" * 78)
    allok = True
    for n in range(2, 17):
        L = lcm_upto(n)
        gfail = []
        for m in range(1, L + 1):
            if not greedy_ok(n, m, 2 * n - 2):
                gfail.append(m)
                if len(gfail) > 5: break
        stat = "GREEDY ALWAYS SUCCEEDS" if not gfail else f"greedy fails at m={gfail[:6]}"
        if gfail: allok = False
        log(f"  n={n:2d} L={L:7d}: {stat}")
    log("PHASE H VERDICT: " + ("descending-greatest greedy is a constructive proof of U (n<=16 full periods)" if allok else "greedy insufficient — need matching/exchange"))

log("\n[engine_round3 phase " + PHASE + " complete]")
LOG.close()
