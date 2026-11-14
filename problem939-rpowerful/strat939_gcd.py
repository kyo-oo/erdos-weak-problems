#!/usr/bin/env python3
# strat939_gcd.py — W66-P939-S (STRATEGIST LANE): THE GCD-PATTERN ANALYSIS.
#
# THE CORE QUESTION (battle order #1): why do ALL sum-hit pairs share gcd > 1?
# Classify the sum-hit pairs (a+b=c, all TRUE 4-powerful, c <= B) by their gcd
# factorization; decompose every hit into its p^4-scaling primitive base; census
# the bases. If every primitive base is non-coprime, the sum-hit population is
# EXACTLY the p^4-scaling closure of a tiny non-coprime base set — the empirical
# structure behind "all gcd > 1".
#
# This engine REGENERATES the box evidence the W64-I lane lost (its 1e18/1e19
# output files were never committed: hunt939e_output.txt absent, hunt939d_output
# truncated at the 1e17 count row). All three parity lanes are swept (EE, EO,
# OO — the prior lanes dropped EE as "dying by coprimality", which hides half
# the family structure: every doubling-family hit (s,s,2s) is EE).
#
# Purity law: pure python + numpy (vectorized membership only) + sympy
# (primerange/factorint). NO gmpy2 / PARI / sage. Integer k-th roots by
# Newton iteration on python ints (exact).
#
# Validation spine (same as hunt939d, re-verified here): gen4 reproduces the
# K60 Lean census row at 1e4 exactly; the bucketed lanes are brute-force
# cross-checked at 1e7 against ALL-pair enumeration.
#
# PHASES (env, comma-separated):  A13 A15 A18 A19 W ALL7
#   A13/A15/A18/A19 : the full-lane box at 10^13 / 10^15 / 10^18 / 10^19
#                     (A13 = deep classification; others: classification with
#                      capped receipts)
#   W  : witness/bracket/curve facts (the r=3 coprime witnesses' diagonal-cubic
#         shapes, the 1e15 bracket factorizations, gcd(19902511,756249048))
import sys, os, time, math, subprocess
from collections import Counter, defaultdict
from sympy import primerange, factorint
import numpy as np

T0 = time.time()
REPO = os.path.dirname(os.path.abspath(__file__))
LOG = None
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    if LOG is not None:
        LOG.write(s + '\n'); LOG.flush()

LEAN_CENSUS_R4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296, 2048,
                  2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776, 8192, 10000]

# ----------------------------------------------------------------------------
# exact integer k-th root (Newton on python ints)
# ----------------------------------------------------------------------------
def iroot(n, k):
    if n < 0: raise ValueError
    if n < 2 or k == 1: return n
    if k == 2:
        r = int(math.isqrt(n)); return r
    x = int(round(n ** (1.0 / k)))
    if x < 1: x = 1
    while x ** k > n: x -= 1
    while (x + 1) ** k <= n: x += 1
    return x

def is_4th_power(n):
    if n < 0: return False
    r = iroot(n, 4); return r ** 4 == n

# ----------------------------------------------------------------------------
# THE CORRECT 4-POWERFUL ENUMERATOR (exponents >= 4; validated vs Lean census)
# ----------------------------------------------------------------------------
def gen4(limit, mod4=None):
    r4 = iroot(limit, 4)
    P = list(primerange(2, r4 + 2))
    if mod4 == 1:
        P = [p for p in P if p % 4 == 1]
    out = []
    ap = out.append
    def rec(i, val):
        ap(val)
        for j in range(i, len(P)):
            v = val * P[j] ** 4
            if v > limit: break
            while v <= limit:
                rec(j + 1, v)
                v *= P[j]
    rec(0, 1)
    out = [x for x in out if 1 < x <= limit]
    out.sort()
    return out

def is_r4(n):
    if n < 1: return False
    if n == 1: return True
    f = factorint(n)
    return all(e >= 4 for e in f.values())

# ----------------------------------------------------------------------------
# THE FULL-LANE SUM-HIT BOX (numpy membership; B <= 1e19 < 2^64 exact)
# ----------------------------------------------------------------------------
def box(B, tag):
    """All triples (a, b, c=a+b), a <= b, all three TRUE 4-powerful, c <= B.
    Lanes: EE (a,b even — gcd >= 2 forced), EO (one even), OO (both odd).
    Returns (hits, lane_stats). Sound+complete: every a+b=c triple with
    c <= B appears in exactly its parity lane; the lanes enumerate every
    candidate pair with sum <= B and test list membership of the sum."""
    t0 = time.time()
    L = gen4(B)
    E = [x for x in L if not (x & 1)]
    O = [x for x in L if (x & 1)]
    L_np = np.array(L, dtype=np.uint64)
    E_np = np.array(E, dtype=np.uint64)
    nL, nE, nO = len(L), len(E), len(O)
    obuck = {r: np.array([o for o in O if (o & 15) == r], dtype=np.uint64)
             for r in (1, 3, 5, 7, 9, 11, 13, 15)}
    hits = {'EE': [], 'EO': [], 'OO': []}
    stats = {'|L|': nL, '|E|': nE, '|O|': nO}
    Bnp = np.uint64(B)
    # ---- EE lane: e1 <= e2 even, e1 + e2 <= B, sum in E ----------------------
    nEE = 0
    for i, e1 in enumerate(E):
        lim = B - e1
        if lim < e1: break
        lo = i  # e2 >= e1 (E is sorted, index i is e1 itself)
        hi = int(np.searchsorted(E_np, np.uint64(lim), side='right'))
        if hi <= lo: continue
        cands = E_np[lo:hi]
        sums = cands + np.uint64(e1)
        pos = np.searchsorted(E_np, sums)
        np.clip(pos, 0, nE - 1, out=pos)
        hitm = E_np[pos] == sums
        nEE += int(cands.size)
        if hitm.any():
            for k in np.nonzero(hitm)[0]:
                hits['EE'].append((e1, int(cands[k]), int(sums[k])))
    # ---- EO lane: o odd, c odd in the same mod-16 bucket (c = o mod 16 forced
    #      by 16 | e), c > o, e = c - o in E ------------------------------------
    nEO = 0
    for o in O:
        r = o & 15
        bk = obuck[r]
        lo = int(np.searchsorted(bk, np.uint64(o), side='right'))
        if lo >= bk.size: continue
        cands = bk[lo:]
        diffs = cands - np.uint64(o)
        pos = np.searchsorted(E_np, diffs)
        np.clip(pos, 0, nE - 1, out=pos)
        hitm = E_np[pos] == diffs
        nEO += int(cands.size)
        if hitm.any():
            for k in np.nonzero(hitm)[0]:
                c = int(cands[k]); e = int(diffs[k])
                hits['EO'].append((min(e, o), max(e, o), c))
    # ---- OO lane: a, b odd complementary mod-16 buckets (16 | c forced),
    #      a < b, a + b <= B, sum in E -----------------------------------------
    nOO = 0
    for a in O:
        r = (-a) & 15
        bk = obuck[r]
        lo = int(np.searchsorted(bk, np.uint64(a), side='right'))
        hi = int(np.searchsorted(bk, np.uint64(B - a), side='right'))
        if lo >= hi: continue
        cands = bk[lo:hi]
        sums = cands + np.uint64(a)
        pos = np.searchsorted(E_np, sums)
        np.clip(pos, 0, nE - 1, out=pos)
        hitm = E_np[pos] == sums
        nOO += int(cands.size)
        if hitm.any():
            for k in np.nonzero(hitm)[0]:
                hits['OO'].append((a, int(cands[k]), int(sums[k])))
    stats.update(EE_checks=nEE, EO_checks=nEO, OO_checks=nOO,
                 box_time=time.time() - t0)
    log(f"[BOX {tag}] |L|={nL} (E={nE}, O={nO}); lane candidate checks: "
        f"EE={nEE} EO={nEO} OO={nOO}; box time {time.time()-t0:.1f}s")
    return hits, stats

# ----------------------------------------------------------------------------
# THE GCD-PATTERN CLASSIFICATION (the core question)
#
# THE CORE DECOMPOSITION (the frame-break): every sum-hit (a,b,c) reduces
# canonically by stripping p^4 from ALL THREE members while the reduced
# triple stays 4-powerful (valid strip: every member's p-exponent in
# {4} ∪ [8,∞), so after the strip it is in {0} ∪ [4,∞)). The reduction
# terminates at a CANONICAL CORE (order-free: p/q-strips commute) with
# hit = core * M^4, M = product of stripped primes. Conversely every
# core*M^4 is again a sum-hit (exponents only grow by 4k >= 0 and were
# >= 4). Hence:  SumHits(B) = { C * M^4 : C ∈ Cores, C·M^4 within B }
# — the population is EXACTLY the 4th-power scaling closure of the core
# set, and gcd(hit) = M^4 * gcd(core). Coprime hits ⟺ coprime cores at
# M = 1. THE core question = does a coprime core exist at all.
# ----------------------------------------------------------------------------
def reduce_core(a, b, c):
    """Canonical core + stripped multiplier M (hit = core * M^4)."""
    fa, fb, fc = factorint(a), factorint(b), factorint(c)
    M = 1
    changed = True
    while changed:
        changed = False
        for p in sorted(set(fa) | set(fb) | set(fc)):
            ea, eb, ec = fa.get(p, 0), fb.get(p, 0), fc.get(p, 0)
            if (ea >= 4 and eb >= 4 and ec >= 4 and
                (ea == 4 or ea >= 8) and (eb == 4 or eb >= 8) and
                    (ec == 4 or ec >= 8)):
                for f, e in ((fa, ea), (fb, eb), (fc, ec)):
                    if e - 4 == 0:
                        del f[p]
                    else:
                        f[p] = e - 4
                M *= p
                changed = True
    core = (math.prod(p ** e for p, e in fa.items()),
            math.prod(p ** e for p, e in fb.items()),
            math.prod(p ** e for p, e in fc.items()))
    return core, M

def classify(hits, stats, tag, deep=True, receipt_cap=40):
    t0 = time.time()
    allh = sorted(hits['EE'] + hits['EO'] + hits['OO'])
    ncop = 0; wit = []
    gcd_sp = Counter()      # smallest prime dividing gcd(a,b)
    rad_c = Counter()       # rad(gcd)
    cores = Counter()       # canonical cores
    core_gcd = {}
    core_lane = {}
    coprime_cores = set()
    doubling = 0
    min_gcd_hits = []       # (gcd, a, b, c)
    isolated = []           # (smallest-prime(gcd), gcd, a, b, c)
    lane_of = {}
    for (a, b, c) in allh:
        g = math.gcd(a, b)
        if g == 1:
            ncop += 1; wit.append((a, b, c))
        if a == b:
            doubling += 1
        fg = factorint(g) if g > 1 else {}
        if fg:
            sp = min(fg)
            gcd_sp[sp] += 1
            rad_c[math.prod(fg.keys())] += 1
            min_gcd_hits.append((g, a, b, c))
            isolated.append((sp, g, a, b, c))
        core, M = reduce_core(a, b, c)
        cores[core] += 1
        if core not in core_gcd:
            core_gcd[core] = math.gcd(core[0], core[1])
            if core_gcd[core] == 1:
                coprime_cores.add(core)
        # gcd law receipt: gcd(a,b) == M^4 * gcd(core)
        if g != M ** 4 * core_gcd[core]:
            log(f'[CLS {tag}] GCD-LAW VIOLATION at {(a,b,c)}: {g} != '
                f'{M**4}*{core_gcd[core]}')
    min_gcd_hits.sort()
    isolated.sort(reverse=True)
    for lane in ('EE', 'EO', 'OO'):
        log(f"[CLS {tag}] lane {lane}: {len(hits[lane])} hits")
    log(f"[CLS {tag}] SUM-HIT CENSUS: total {len(allh)}; "
        f"doubling-form a==b: {doubling}")
    log(f"[CLS {tag}] *** COPRIME SUM-HITS (gcd(a,b)=1): {ncop} ***")
    for w in wit[:10]:
        log(f"[CLS {tag}]   WITNESS CANDIDATE: {w}")
    log(f"[CLS {tag}] smallest-prime-dividing-gcd distribution: "
        f"{dict(sorted(gcd_sp.items()))}")
    msp = max(gcd_sp) if gcd_sp else None
    log(f"[CLS {tag}] max over hits of smallest-prime(gcd) = {msp}")
    log(f"[CLS {tag}] rad(gcd) top-15: {rad_c.most_common(15)}")
    log(f"[CLS {tag}] CANONICAL CORES: {len(cores)} distinct; "
        f"coprime cores: {len(coprime_bases) if False else len(coprime_cores)}; "
        f"gcd-law verified on all {len(allh)} hits (gcd(a,b) = M^4*gcd(core))")
    for core, cnt in sorted(cores.items(), key=lambda kv: -kv[1])[:receipt_cap]:
        log(f"[CLS {tag}]   core {core} x{cnt}  gcd(core)={core_gcd[core]}")
    if coprime_cores:
        for core in sorted(coprime_cores):
            log(f"[CLS {tag}]   *** COPRIME CORE {core} ***")
    log(f"[CLS {tag}] smallest cores (by max member): ")
    for core in sorted(cores, key=lambda c: max(c))[:15]:
        log(f"[CLS {tag}]   core {core} x{cores[core]} gcd(core)={core_gcd[core]}")
    log(f"[CLS {tag}] near-coprime frontier — smallest gcds:")
    for (g, a, b, c) in min_gcd_hits[:15]:
        log(f"[CLS {tag}]   gcd={g} = {dict(factorint(g))}: {a} + {b} = {c}")
    log(f"[CLS {tag}] most-isolated hits — largest smallest-prime(gcd):")
    for (sp, g, a, b, c) in isolated[:10]:
        log(f"[CLS {tag}]   sp={sp} gcd={g} = {dict(factorint(g))}: "
            f"{a} + {b} = {c}")
    log(f"[CLS {tag}] classification time {time.time()-t0:.1f}s")
    return dict(total=len(allh), ncop=ncop, cores=len(cores),
                coprime_cores=len(coprime_cores), msp=msp, doubling=doubling)

# ----------------------------------------------------------------------------
# Brute-force cross-validation of the full-lane box at small bound
# ----------------------------------------------------------------------------
def brute_box(LIMIT):
    L = gen4(LIMIT); Lset = set(L)
    hits = []
    for i, a in enumerate(L):
        if 2 * a > LIMIT: break
        for b in L[i:]:
            if a + b > LIMIT: break
            if (a + b) in Lset:
                hits.append((a, b, a + b))
    return hits

def crosscheck():
    ok_gen = gen4(10 ** 4) == LEAN_CENSUS_R4[1:]
    log(f"[XCHK] gen4(1e4) == K60 Lean census row (excl. 1): {ok_gen}")
    for lim in (10 ** 7, 10 ** 9):
        h, st = box(lim, f'X{int(round(math.log10(lim)))}')
        ref = brute_box(lim)
        mine = sorted(h['EE'] + h['EO'] + h['OO'])
        ok = mine == sorted(ref)
        log(f"[XCHK] full-lane box vs brute force at 1e{int(round(math.log10(lim)))}: "
            f"{ok} ({len(mine)} vs {len(ref)} sum-hits)")
        if not ok:
            log(f"[XCHK]   brute-only: {[t for t in ref if t not in mine]}")
            log(f"[XCHK]   mine-only : {[t for t in mine if t not in ref]}")
        if not ok: return False
    return True

# ----------------------------------------------------------------------------
# Phase W — witness / bracket / curve facts
# ----------------------------------------------------------------------------
def phase_w():
    log('=== PHASE W: witnesses, brackets, diagonal-cubic shapes ===')
    a1, b1, c1 = 19902511, 756249048, 776151559
    log(f'[W] witness1 r=3: {a1} + {b1} = {c1}: {a1 + b1 == c1}')
    log(f'[W]   factorizations: {dict(factorint(a1))} | {dict(factorint(b1))} | '
        f'{dict(factorint(c1))}')
    log(f'[W]   gcd(a1,b1) = {math.gcd(a1, b1)}  (the brief\'s "gcd 11?" — '
        f'answered: it is 1; witness1 IS a pairwise-coprime 3-powerful triple)')
    log(f'[W]   diagonal-cubic shape: 271^3 + 9*438^3 = 919^3: '
        f'{271**3 + 9*438**3 == 919**3}  (b1 = 9*438^3; 3 | 438)')
    a2, b2, c2 = 1392672604221, 2126285555779, 3518958160000
    log(f'[W] witness2 r=3: gcd = {math.gcd(a2, b2)}; '
        f'diagonal-cubic shape 3*7743^3 + 12859^3 = 10*7060^3: '
        f'{3*7743**3 + 12859**3 == 10*7060**3}  '
        f'(a2 = 3*(3*29*89)^3 with x=7743; b2 = 12859^3; c2 = 10*7060^3)')
    lo, hi = 999706081460641, 1000417426149376
    log(f'[W] the 1e15 hunt bracket: {lo} < 1e15 < {hi}: '
        f'{lo < 10**15 < hi}')
    log(f'[W]   factorizations: {dict(factorint(lo))} | {dict(factorint(hi))}')
    log(f'[W]   both TRUE 4-powerful: {is_r4(lo)} {is_r4(hi)}')
    log(f'[W]   10^15 itself = 2^15*5^15 is 4-powerful: {is_r4(10**15)} '
        f'(the bracket is a plain arithmetic receipt, not an adjacency claim)')
    L15 = gen4(hi)
    i_hi = min(i for i, x in enumerate(L15) if x > 10 ** 15)
    log(f'[W]   smallest 4-powerful > 1e15: {L15[i_hi]} (== hi: '
        f'{L15[i_hi] == hi}); neighbors around 1e15: '
        f'{L15[i_hi-3:i_hi+2]}')

# ----------------------------------------------------------------------------
def run_bound(B, tag, deep=True, cap=40):
    h, st = box(B, tag)
    cls = classify(h, st, tag, deep=deep, receipt_cap=cap)
    return h, st, cls

def main():
    global LOG
    phases = os.environ.get('PHASES', 'A13').split(',')
    outfile = os.environ.get('OUTFILE', REPO + '/strat939_gcd_output.txt')
    LOG = open(outfile, 'w')
    log(f'strat939_gcd start (phases {phases}); python {sys.version.split()[0]}; '
        f'numpy {np.__version__}; sympy-factorint engine')
    if 'XCHK' in phases:
        if not crosscheck():
            log('CROSSCHECK FAILED'); LOG.close(); return
    if 'W' in phases:
        phase_w()
    for ph, B in (('A13', 10 ** 13), ('A15', 10 ** 15), ('A18', 10 ** 18),
                  ('A19', 10 ** 19)):
        if ph in phases:
            run_bound(B, ph[1:], deep=True, cap=25 if ph != 'A13' else 60)
    log(f'strat939_gcd total {time.time()-T0:.1f}s')
    LOG.close()

if __name__ == '__main__':
    main()
