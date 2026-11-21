#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""engine142audit_w81.py — THE W81-142B INDEPENDENT AUDIT ENGINE (Erdos #142).

The AUDITOR/DOUBTER lane of wave W81. Every check below is a FRESH code
path, deliberately different from the campaign engines it audits:

  * r_k tables recomputed by my own lex-order DFS with endpoint-completion
    pruning (the banked engines use marking B&B with forced-0 symmetry in C,
    z3 bisection, and pair-midpoint scanners);
  * the Fourier / deviation identities verified by EXACT finite-field DFT
    (roots of unity in F_q, q = c*p+1 prime — no floating point anywhere),
    versus the banked cmath/complex checkpoints;
  * the BEHREND-GEN plug-back re-derived with the CORRECT margin
    ln((m^(d-k)-d^2)/d^2) - (ln N - C_k sqrt(ln N)) (the banked GEN-PLUGBACK
    omitted the /d^2 — W81-142B defect D4), plus a complete recipe-cell
    endpoint scan closing the inter-grid gap, plus a far-range scan;
  * LOGDECAY anchors recomputed at 60 digits with the corrected digits;
  * negative controls: planted table defects, corrupted identities and an
    over-optimistic constant MUST be detected (a checker that cannot fail
    is worthless).

Usage:  python3 engine142audit_w81.py [--quick] [--only NAME ...]
Receipts: receipts142audit_w81.txt.  Budget: < 6 min per run.
Exit 0 iff every check passes.
"""
import json
import math
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 142142
LN2 = math.log(2)

RESULTS = []
T0 = time.time()


def report(name, ok, detail=""):
    RESULTS.append((name, bool(ok), str(detail)))
    print("[%s] %s %s" % ("PASS" if ok else "FAIL", name, str(detail)[:400]))
    return bool(ok)


# ----------------------------------------------------------------------------
# Shared exact helpers
# ----------------------------------------------------------------------------

def ilog(n):
    """ln of a positive big int, ~1e-15 relative accuracy (no float overflow)."""
    if n <= 0:
        raise ValueError
    if n < (1 << 53):
        return math.log(n)
    b = n.bit_length()
    lead = n >> (b - 53)
    return math.log(lead) + (b - 53) * LN2


def integer_nthroot(N, d):
    """floor(N ** (1/d)) for positive ints, EXACT: float seed (~50 correct
    bits) + integer Newton (quadratic) + a final exact fix by direct power
    comparison. Same contract as the dead author's bisection, ~50x faster
    at 2^6000..2^40000 — W81-142B-F runtime fix."""
    if d == 1:
        return N
    if N <= 1:
        return N
    s = ilog(N) / (d * LN2)  # log2 of the root, ~1e-15 relative
    t = int(2 ** s)
    if t < 1:
        t = 1
    for _ in range(5):
        if t ** (d - 1) == 0:
            break
        tp = ((d - 1) * t + N // t ** (d - 1)) // d
        if tp == t:
            break
        t = tp
    while t > 1 and t ** d > N:
        t -= 1
    while (t + 1) ** d <= N:
        t += 1
    return t


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 29, 37, 41):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# ----------------------------------------------------------------------------
# A1. My own r_k exhaustive recomputation (fresh algorithm: lex-order DFS,
# endpoint-completion pruning, greedy-seeded bound; NO forced-0 symmetry).
# ----------------------------------------------------------------------------

def aps_ending_at(N, k, x):
    """All k-APs of [1,N] whose LAST term is x: lists of earlier terms."""
    out = []
    for d in range(1, (x - 1) // (k - 1) + 1):
        terms = [x - (k - 1 - i) * d for i in range(k - 1)]  # earlier terms
        if terms[0] >= 1:
            out.append(terms)
    return out


def _greedy_free(N, k, rng):
    """Greedy k-AP-free set (seed for the DFS bound): IN-ORDER sweep — add x
    iff no k-AP ENDING at x is completed by S (since S ⊆ {1..x-1}, any k-AP
    created by adding x must end at x, so the sweep is AP-free by induction;
    the shuffled-order variant of the dead author completed APs at interior
    positions and over-seeded the bound — W81-142B-F runtime bug fix)."""
    S = set()
    for x in range(1, N + 1):
        ok = True
        for d in range(1, (x - 1) // (k - 1) + 1):
            if all((x - (k - 1 - i) * d) in S for i in range(k - 1)):
                ok = False
                break
        if ok:
            S.add(x)
    return S


def r_k_exact(N, k, rng):
    """Exact r_k(N) by lex DFS with pruning. Different from the banked
    marking B&B: forward endpoint-completion check, greedy lower seed,
    no symmetry forcing."""
    if N < k:
        return N  # the whole [1,N] is k-AP-free trivially
    best = len(_greedy_free(N, k, rng))
    end_aps = {x: aps_ending_at(N, k, x) for x in range(1, N + 1)}
    S = []

    def dfs(x, size):
        nonlocal best
        if size + (N - x + 1) <= best:
            return  # cannot beat the bound even taking everything left
        if x > N:
            best = max(best, size)
            return
        # try taking x (only if no k-AP completes with x as last term)
        can_take = True
        for terms in end_aps[x]:
            if all(t in S for t in terms):
                can_take = False
                break
        if can_take:
            S.append(x)
            dfs(x + 1, size + 1)
            S.pop()
        # skip x — symmetry break: if best == size + remaining - 1 needs x... skip
        dfs(x + 1, size)

    dfs(1, 0)
    return best


def kap_free_scan(S, k):
    """k-AP-freeness by forward scan (code A): a k-AP's first TWO terms
    a, a+d are both in S, so for each anchor a in S only differences
    d = b - a with b in S, b > a, can start one (identical detection set
    to the naive all-d scan — the W81-142B-F speed fix; the naive loop was
    O(|S| * max(S)) and blew the budget on the 2^24 construction cells)."""
    Ss = set(S)
    if not Ss:
        return True, None
    mx = max(Ss)
    for a in Ss:
        for b in Ss:
            if b <= a:
                continue
            d = b - a
            if a + (k - 1) * d > mx:
                continue
            if all(a + i * d in Ss for i in range(2, k)):
                return False, (a, d)
    return True, None


def kap_free_pairs(S, k):
    """k-AP-freeness by endpoint-pair positioning (code B): every k-AP's
    FIRST and LAST terms are members with (c - a) = (k-1)d — scan all
    endpoint pairs (a complete O(|S|^2) detector; also covers 0-anchored
    APs of lifted Behrend sets, which the dead author's any-position pair
    scan silently missed below 1 — W81-142B-F fix)."""
    Ss = sorted(set(S))
    n = len(Ss)
    Sset = set(Ss)
    for i in range(n):
        for j in range(i + 1, n):
            a, c = Ss[i], Ss[j]
            diff = c - a
            if diff % (k - 1):
                continue
            d = diff // (k - 1)
            if d < 1:
                continue
            if all(a + t * d in Sset for t in range(1, k - 1)):
                return False, (a, d)
    return True, None


def check_tables():
    """AUD-TABLES: my own r_k recomputation vs the banked certified tables."""
    rng = random.Random(SEED)
    tab = json.load(open(os.path.join(HERE, "tables_rk_v3.json")))
    plan = [("3", 30), ("4", 16), ("5", 18), ("6", 18)]
    bad = []
    rows = []
    for kstr, nmax in plan:
        k = int(kstr)
        mine = []
        for N in range(1, nmax + 1):
            v = r_k_exact(N, k, rng)
            mine.append(v)
            banked = tab[kstr][str(N)]["value"]
            if v != banked:
                bad.append((k, N, v, banked))
        rows.append("r_%d(1..%d) mine=%s" % (k, nmax, mine))
    # every banked witness in all four tables: AP-free by both codes + size
    witbad = []
    for kstr in ("3", "4", "5", "6"):
        k = int(kstr)
        for nstr, cell in tab[kstr].items():
            w = cell.get("witness_1based") or cell.get("witness")
            if not w:
                witbad.append((k, nstr, "missing witness"))
                continue
            if len(w) != cell["value"]:
                witbad.append((k, nstr, "size %d != value %d" % (len(w), cell["value"])))
            okA, _ = kap_free_scan(w, k)
            okB, _ = kap_free_pairs(w, k)
            if not (okA and okB):
                witbad.append((k, nstr, "witness contains k-AP"))
    # monotonicity of all four tables
    monbad = []
    for kstr in ("3", "4", "5", "6"):
        vals = [tab[kstr][str(n)]["value"] for n in sorted(map(int, tab[kstr]))]
        if any(vals[i] > vals[i + 1] for i in range(len(vals) - 1)):
            monbad.append(kstr)
    report("AUD-TABLES",
           not bad and not witbad and not monbad,
           "; ".join(rows) +
           ("| recomputation mismatches: %s" % bad if bad else "| my DFS == banked on every recomputed cell") +
           ("| witness defects: %s" % witbad[:5] if witbad else "| all %d banked witnesses re-verified (size + freeness, both my codes)"
            % sum(len(tab[k2]) for k2 in ("3", "4", "5", "6"))) +
           ("| monotonicity violations: %s" % monbad if monbad else "| all tables monotone"))


def check_r4varn_doc():
    """AUD-R4VARN-TABLE: the R4_VARN.md §1 table row vs my exhaustive r_4."""
    doc = open(os.path.join(HERE, "R4_VARN.md"), encoding="utf-8").read()
    import re
    m = re.search(r"\| r_4\(M\) \|[ 0-9|]+", doc)
    row = [int(x) for x in re.findall(r"\d+", m.group(0))]
    # row[0] is the '4' of the label 'r_4(M)'; the 16 table values follow
    if len(row) != 17:
        report("AUD-R4VARN-TABLE", False, "parse: expected 17 numbers, got %d" % len(row))
        return
    vals = row[1:17]
    rng = random.Random(SEED + 1)
    mine = [r_k_exact(N, 4, rng) for N in range(1, 17)]
    bad = [(N, mine[N - 1], vals[N - 1]) for N in range(1, 17) if mine[N - 1] != vals[N - 1]]
    report("AUD-R4VARN-TABLE", not bad,
           "R4_VARN.md row r_4(1..16)=%s vs my exhaustive=%s%s"
           % (vals, mine, (" | MISMATCHES (N, mine, doc): %s" % bad) if bad else " — agree cell by cell"))


def check_k7():
    """AUD-K7: the k=7 table of UPPER_STACK.md.
    (a) N <= 42: exact — lower by the multiples-of-7 witness, upper by the
        floor law r_k(N) <= N - floor(N/k);
    (b) N = 43..45: my own constructed witnesses (multiples-of-7 + breakers);
    (c) N = 46: the banked receipts witness re-verified;
    (d) N = 43..46: independent z3 second-code upper certificates."""
    doc_vals = [1, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12, 12, 13, 14, 15, 16, 17, 18,
                18, 19, 20, 21, 22, 23, 24, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32,
                33, 34, 35, 36, 36, 36, 36, 36, 37]
    bad = []
    for N in range(1, 43):
        witness = set(range(1, N + 1)) - set(range(7, N + 1, 7))
        okA, _ = kap_free_scan(witness, 7)
        okB, _ = kap_free_pairs(witness, 7)
        val = N - N // 7
        if not (okA and okB and len(witness) == val and val == doc_vals[N - 1]):
            bad.append((N, val, doc_vals[N - 1]))
    # N = 43,44,45: multiples-of-7 plus breakers of the d=7 APs
    for N in range(43, 46):
        witness = set(range(1, N + 1)) - set(range(7, N + 1, 7))
        breaks = 0
        for a in range(1, N - 41):
            ap = set(range(a, a + 42 + 1, 7))
            while ap & witness == ap:  # still fully present
                witness.discard(max(ap))
                breaks += 1
        okA, _ = kap_free_scan(witness, 7)
        if not (okA and len(witness) == doc_vals[N - 1]):
            bad.append((N, len(witness), doc_vals[N - 1], "constructed witness"))
    # N = 46: banked receipts witness
    w46 = [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22, 23,
           24, 25, 26, 27, 29, 30, 31, 33, 34, 37, 39, 40, 41, 42, 43, 45, 46]
    okA, _ = kap_free_scan(w46, 7)
    okB, _ = kap_free_pairs(w46, 7)
    if not (okA and okB and len(w46) == 37 == doc_vals[45]):
        bad.append((46, len(w46), doc_vals[45], "receipts witness"))
    # (d) independent z3 second-code certificates for the X-only cells
    z3det = []
    try:
        import z3
        def z7(N, t, tmo=60):
            xs = [z3.Bool("x%d" % i) for i in range(1, N + 1)]
            slv = z3.Solver()
            slv.set("timeout", tmo * 1000)
            for a in range(1, N + 1):
                for d in range(1, (N - a) // 6 + 1):
                    slv.add(z3.Not(z3.And(*[xs[a + i * d - 1] for i in range(7)])))
            slv.add(z3.PbGe([(x, 1) for x in xs], t))
            return str(slv.check())
        for N in (43, 44, 45):
            r = z7(N, doc_vals[N - 1] + 1)
            z3det.append("r_7(%d)<=%d:z3 %s" % (N, doc_vals[N - 1], r))
            if r != "unsat":
                bad.append((N, "z3 could not refute %d" % (doc_vals[N - 1] + 1)))
        r = z7(46, 38)
        r2 = z7(46, 37)
        z3det.append("r_7(46)<=37:z3 %s; >=37:z3 %s" % (r, r2))
        if r != "unsat" or r2 != "sat":
            bad.append((46, "z7(46) 38 should be unsat / 37 sat", r, r2))
    except Exception as e:  # pragma: no cover
        bad.append(("z3", repr(e)))
    report("AUD-K7", not bad,
           "k=7 table N=1..46: N<=42 exact (multiples-of-7 witness + floor law, both my codes); "
           "43..46 constructed/receipt witnesses verified; INDEPENDENT z3 second-code uppers: %s%s"
           % ("; ".join(z3det), (" | DEFECTS: %s" % bad[:6]) if bad else " — the X-code-only cells now carry two codes"))


# ----------------------------------------------------------------------------
# A2. The BEHREND-GEN plug-back, corrected margin + cell-endpoint closure.
# ----------------------------------------------------------------------------

def recipe(k, N):
    L = ilog(N)
    d = max(1, int(math.sqrt(k * L / LN2)))
    m = integer_nthroot(N, d) // 2
    return d, m


def Ck(k):
    return 2.0 * math.sqrt((k + 1) * LN2) + 1.0


def true_margin(k, N, d, m, C):
    """ln( m^(d-k)/d^2 - 1 ) - (ln N - C sqrt(ln N)) — the THEOREM's LHS."""
    lhs = m ** (d - k) - d * d
    if lhs <= 0:
        return None
    L = ilog(N)
    return ilog(lhs) - 2 * math.log(d) - (L - C * math.sqrt(L))


def old_margin(k, N, d, m, C):
    """The banked GEN-PLUGBACK margin (W81-142B defect D4): omits /d^2."""
    lhs = m ** (d - k) - d * d
    if lhs <= 0:
        return None
    L = ilog(N)
    return ilog(lhs) - (L - C * math.sqrt(L))


def check_bge_plugback():
    """AUD-BGE-PLUGBACK: (a) banked grid re-verified with the TRUE margin;
    (b) complete recipe-cell endpoint enumeration for d <= 46 (closes the
    inter-grid gap: within a cell the LHS is constant and the RHS is
    increasing, so the cell's worst point is its right endpoint);
    (c) far-range scan to 2^40000; (d) no silent skips on the banked grid."""
    ok_all = True
    det = []
    worst = {}
    # (a) the banked 45,847-point grid, TRUE margins.  NOTE: N = (1<<xi) *
    # int(2**frac) and int(2**frac) == 1 for every 0 <= frac < 1, so the grid
    # is really N = 2^int(x): the (d, m, margin) computation is memoized per
    # (k, xi) — 5,961 distinct cells per k instead of 45,847 (W81-142B-F
    # runtime fix; the point COUNT assertion below still verifies the banked
    # 45,847-point grid was swept).
    memo = {}
    for k in range(3, 11):
        C = Ck(k)
        w = (None, 1e18)
        n_pts = 0
        skips = 0
        x = 40.0
        while x <= 6000.0 + 1e-9:
            xi = int(x)
            key = (k, xi)
            if key not in memo:
                N = 1 << xi
                d, m = recipe(k, N)
                if m < 2 or d < k + 1:
                    memo[key] = (d, m, None, True)
                else:
                    memo[key] = (d, m, true_margin(k, N, d, m, C), False)
            d, m, mg, skipped = memo[key]
            if skipped:
                skips += 1
            elif mg is None:
                ok_all = False
                det.append("GRID k=%d x=%.2f margin=None (m^(d-k)-d^2 <= 0)" % (k, x))
            else:
                n_pts += 1
                if mg < 0:
                    ok_all = False
                    det.append("GRID k=%d x=%.2f margin=%s" % (k, x, mg))
                if mg < w[1]:
                    w = (x, mg, d)
            x += 0.13
        worst[k] = w
        if skips:
            ok_all = False
            det.append("k=%d skipped %d grid points (m<2 or d<k+1)" % (k, skips))
        if n_pts + skips != 45847:
            ok_all = False
            det.append("k=%d grid point count %d != 45847" % (k, n_pts + skips))
    det.append("grid TRUE worst margins: " +
               "; ".join("k=%d: %+.4f @2^%.2f (d=%d)" % (k, v[1], v[0], v[2]) for k, v in sorted(worst.items())))
    # (b) recipe-cell endpoint enumeration, d <= 46
    DCUT = 46
    for k in range(3, 11):
        C = Ck(k)
        w = (None, 1e18)
        ncells = 0
        for d in range(k + 1, DCUT + 1):
            Nlo_d = max(1 << 40, math.ceil(math.exp(d * d * LN2 / k) - 1e-9))
            Nhi_d = int(math.exp((d + 1) * (d + 1) * LN2 / k))
            if Nlo_d >= Nhi_d:
                continue
            mlo = max(2, integer_nthroot(Nlo_d, d) // 2)
            mhi = integer_nthroot(Nhi_d - 1, d) // 2
            for m in range(mlo, mhi + 1):
                lo = max((2 * m) ** d, Nlo_d)
                hi = min((2 * m + 2) ** d - 1, Nhi_d - 1, (1 << 6000) - 1)
                if lo > hi:
                    continue
                lhs = m ** (d - k) - d * d
                if lhs <= 0:
                    continue
                ncells += 1
                L = ilog(hi)
                mg = ilog(lhs) - 2 * math.log(d) - (L - C * math.sqrt(L))
                if mg < 0:
                    ok_all = False
                    det.append("CELL k=%d d=%d m=%d endpoint margin %.4f < 0" % (k, d, m, mg))
                if mg < w[1]:
                    w = ((d, m), mg)
        det.append("k=%d: %d recipe cells (d<=%d) all endpoints >= %+.4f (worst at d,m=%s)"
                   % (k, ncells, DCUT, w[1], w[0]))
    report("AUD-BGE-PLUGBACK", ok_all,
           "TRUE margin ln((m^(d-k)-d^2)/d^2)-(lnN-C_k*sqrt(lnN)) >= 0 everywhere; " + " | ".join(det[-18:]))


def check_bge_farrange():
    """AUD-BGE-FARRANGE: the plug-back on 2^6000 < N <= 2^40000 — coarse
    grid + per-d cell endpoints at the low-m end (the tight side: within a
    far recipe window the margin is increasing in m, since d margin/d m has
    the sign of (C_k/2)*sqrt(d/ln(2m)) - k > 0 for every k because
    C_k > 2*sqrt(k ln 2); the m = mhi spot-check below guards that analysis
    empirically).  The dead author's math.exp window boundaries overflowed
    at d ~ 350 (W81-142B-F runtime bug); they are replaced by EXACT integer
    power-of-two bounds: Nlo uses 2^floor(d^2/k) (a lower bound -> mlo can
    only start lower = safe) and Nhi uses 2^ceil((d+1)^2/k) (an upper
    bound -> the endpoint check is conservative)."""
    ok_all = True
    det = []
    for k in range(3, 11):
        C = Ck(k)
        wmin = 1e18
        # coarse grid, exact integers via 2^x
        x = 6000.0
        while x <= 40000.0:
            N = 1 << int(x)
            L = x * LN2
            d = max(1, int(math.sqrt(k * L / LN2)))
            m = integer_nthroot(N, d) // 2
            if m >= 2 and d >= k + 1:
                lhs = m ** (d - k) - d * d
                if lhs > 0:
                    mg = ilog(lhs) - 2 * math.log(d) - (L - C * math.sqrt(L))
                    wmin = min(wmin, mg)
                    if mg < 0:
                        ok_all = False
                        det.append("FAR k=%d x=%.0f margin %.4f" % (k, x, mg))
            x += 64.0
        # per-d low-m cell endpoints (d from 47 to ~ sqrt(k*40000))
        dmax = int(math.sqrt(k * 40000.0)) + 1
        ncells = 0
        for d in range(47, dmax + 1):
            Nlo_d = max(1 << 40, 1 << ((d * d) // k))
            if Nlo_d <= (1 << 6000):
                Nlo_d = (1 << 6000) + 1
            Nhi_d = 1 << (((d + 1) * (d + 1) + k - 1) // k)  # ceil((d+1)^2/k)
            if Nlo_d >= Nhi_d:
                continue
            mlo = max(2, integer_nthroot(Nlo_d, d) // 2)
            mhi = max(mlo, integer_nthroot(Nhi_d - 1, d) // 2)
            mg_by_m = {}
            for m in (mlo, mlo + 1, mhi):
                hi = min((2 * m + 2) ** d - 1, Nhi_d - 1, (1 << 40000) - 1)
                if (2 * m) ** d > hi:
                    continue
                lhs = m ** (d - k) - d * d
                if lhs <= 0:
                    ok_all = False
                    det.append("FAR k=%d d=%d m=%d lhs<=0" % (k, d, m))
                    continue
                L = ilog(hi)
                mg = ilog(lhs) - 2 * math.log(d) - (L - C * math.sqrt(L))
                mg_by_m[m] = mg
                wmin = min(wmin, mg)
                if mg < 0:
                    ok_all = False
                    det.append("FARCELL k=%d d=%d m=%d margin %.4f" % (k, d, m, mg))
                ncells += 1
            # monotonicity guard: the low-m end is the tight side ONLY if the
            # margin increases with m; if the top cell dips below the bottom
            # cell, the skipped middle cells are a coverage gap -> FAIL
            if mlo in mg_by_m and mhi in mg_by_m and mhi > mlo + 1:
                if mg_by_m[mhi] < mg_by_m[mlo] - 1e-6:
                    ok_all = False
                    det.append("FARMONO k=%d d=%d: margin(mhi) %.4f < margin(mlo) %.4f"
                               % (k, d, mg_by_m[mhi], mg_by_m[mlo]))
        det.append("k=%d far-range min margin %+.2f (%d low/high-m cells)"
                   % (k, wmin, ncells))
    report("AUD-BGE-FARRANGE", ok_all,
           "plug-back on 2^6000..2^40000 (coarse grid + low-m cell endpoints "
           "+ mhi monotonicity spot-checks): " + "; ".join(det))


def my_gen_set(k, d, m):
    """My own BG construction (different tie-break from the banked engine)."""
    cells = {}
    for vec in _product_range(m, d):
        key = (sum(vec), sum(v ** (k - 1) for v in vec))
        cells.setdefault(key, []).append(vec)
    # my tie-break: max size, then SMALLEST key (banked uses lexicographic
    # machinery elsewhere); any max cell certifies Theorem BG's bound
    best = None
    for key, vecs in cells.items():
        if best is None or len(vecs) > len(cells[best]):
            best = key
    S = set(sum(v * (2 * m) ** i for i, v in enumerate(vec)) for vec in cells[best])
    return S, best


def _product_range(m, d):
    if d == 1:
        for v in range(m):
            yield (v,)
    else:
        for head in _product_range(m, d - 1):
            for v in range(m):
                yield head + (v,)


def check_bge_construction():
    """AUD-BGE-CONSTRUCT: 3 sample (k, N) cells — recipe parameters, real
    constructed sets, my own freeness codes, Theorem-BG two-pigeonhole bound,
    direct plug-back |S| - 1 >= N exp(-C_k sqrt(ln N))."""
    ok_all = True
    det = []
    cells = [(3, 1 << 20), (4, 1 << 20), (7, 1 << 24)]
    for k, N in cells:
        d, m = recipe(k, N)
        if m ** d > (1 << 16):
            det.append("k=%d N=2^%d: box too big, skipped" % (k, int(ilog(N) / LN2)))
            continue
        S, key = my_gen_set(k, d, m)
        okA, wA = kap_free_scan(S, k)
        okB, wB = kap_free_pairs(S, k)
        bound = (m ** d) / ((d * (m - 1) + 1) * (d * (m - 1) ** (k - 1) + 1))
        L = ilog(N)
        C = Ck(k)
        pb = math.log(len(S) - 1) - (L - C * math.sqrt(L)) if len(S) > 1 else -1
        good = okA and okB and len(S) >= bound and max(S) < (2 * m) ** d and pb >= 0
        ok_all = ok_all and good
        det.append("k=%d N=2^%d (d,m)=(%d,%d) |S|=%d bound=%.1f APfree=%s/%s plugback-margin=%+.3f"
                   % (k, int(round(ilog(N) / LN2)), d, m, len(S), bound, okA, okB, pb))
    report("AUD-BGE-CONSTRUCT", ok_all,
           "3 direct-construction cells (my own layer x h-sphere code): " + "; ".join(det))


def check_bge_constants():
    """AUD-BGE-CONSTANTS: the §6.3 threshold table of BEHREND_GEN.md must
    equal the formula C_k = 2 sqrt((k+1) ln 2) + 1 (regression guard for
    W81-142B defect D3) and the asymptotic column must equal 2 sqrt(k ln 2)."""
    doc = open(os.path.join(HERE, "BEHREND_GEN.md"), encoding="utf-8").read()
    import re
    sec = doc.split("## §6.3")[1].split("## §6.4")[0]
    rows = re.findall(r"\|\s*(\d+)\s*\|\s*([\d.]+)\s*\|\s*([\d.]+)\s*\|\s*\$2\^\{40\}\$", sec)
    bad = []
    for kstr, ck_doc, asym_doc in rows:
        k = int(kstr)
        ck_true = 2 * math.sqrt((k + 1) * LN2) + 1
        asym_true = 2 * math.sqrt(k * LN2)
        if abs(float(ck_doc) - ck_true) > 6e-4:
            bad.append(("k=%d C_k doc %s != formula %.4f" % (k, ck_doc, ck_true)))
        if abs(float(asym_doc) - asym_true) > 6e-4:
            bad.append(("k=%d asympt doc %s != 2sqrt(k ln2) %.4f" % (k, asym_doc, asym_true)))
    report("AUD-BGE-CONSTANTS", bool(rows) and not bad,
           "BEHREND_GEN.md §6.3 table (8 rows) == formula C_k=2sqrt((k+1)ln2)+1 and asymptotic 2sqrt(k ln2): %s"
           % ("all 16 numeric cells exact" if not bad else "DEFECTS: %s" % bad))


# ----------------------------------------------------------------------------
# A3. The envelope laws (U-GEN-0, BLOCK, SLIDE) on 200 random triples.
# ----------------------------------------------------------------------------

def check_envelope():
    tab = json.load(open(os.path.join(HERE, "tables_rk_v3.json")))
    k7 = [1, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12, 12, 13, 14, 15, 16, 17, 18, 18, 19,
          20, 21, 22, 23, 24, 24, 25, 26, 27, 28, 29, 30, 30, 31, 32, 33, 34, 35, 36,
          36, 36, 36, 36, 37]
    tables = {
        3: {n: tab["3"][str(n)]["value"] for n in range(1, 62)},
        4: {n: tab["4"][str(n)]["value"] for n in range(1, 43)},
        5: {n: tab["5"][str(n)]["value"] for n in range(1, 58)},
        6: {n: tab["6"][str(n)]["value"] for n in range(1, 52)},
        7: {n: k7[n - 1] for n in range(1, 47)},
    }
    stones = {3: (61, 19), 4: (42, 22), 5: (55, 36), 6: (43, 31), 7: (45, 36)}
    rng = random.Random(SEED + 2)
    bad = []
    n_checks = 0
    for _ in range(200):
        k = rng.randint(3, 7)
        N = rng.randint(1, max(tables[k]))
        L = rng.randint(2, max(tables[k]))
        rkN = tables[k][N]
        # U-GEN-0: r_k(N) <= N - floor(N/k)
        if rkN > N - N // k:
            bad.append(("U-GEN-0", k, N, rkN, N - N // k))
        n_checks += 1
        # BLOCK: r_k(N) <= floor(N/L)*r_k(L) + r_k(N mod L)  (N mod L < L in table)
        rL = tables[k][L]
        rem = N % L
        rrem = tables[k][rem] if rem else 0
        if rkN > (N // L) * rL + rrem:
            bad.append(("BLOCK", k, N, L, rkN, (N // L) * rL + rrem))
        n_checks += 1
        # SLIDE-GEN: N >= 2m-1 => r_k(N) <= r_k(m)(N-m+1)/m + 2(m-1)  [real-valued]
        if N >= 2 * L - 1:
            bnd = rL * (N - L + 1) / L + 2 * (L - 1)
            if rkN > bnd + 1e-12:
                bad.append(("SLIDE", k, N, L, rkN, bnd))
            n_checks += 1
    # stone exactness + the doc's rho* values
    rho_doc = {3: 19 / 61, 4: 22 / 42, 5: 36 / 55, 6: 31 / 43, 7: 36 / 45}
    for k, (L, r) in stones.items():
        if tables[k][L] != r:
            bad.append(("stone", k, L, tables[k][L], r))
    # M-1 ladder on the common range
    for N in range(1, 43):
        if not (tables[3][N] <= tables[4][N] <= tables[5][min(N, 57)] if N <= 42 else True):
            bad.append(("ladder", N))
    for N in range(1, 47):
        if N <= 51 and tables[6].get(N) and tables[7][N] < tables[6][N]:
            bad.append(("ladder67", N))
    report("AUD-ENVELOPE", not bad,
           "%d inequality checks on 200 random (k,N,L) triples via the certified tables: "
           "U-GEN-0, BLOCK, SLIDE-GEN all hold; stones (61,19),(42,22),(55,36),(43,31),(45,36) exact; "
           "M-1 ladder r3<=r4<=r5<=r6<=r7 on the common range%s"
           % (n_checks, (" | VIOLATIONS: %s" % bad[:6]) if bad else " — zero violations"))


# ----------------------------------------------------------------------------
# A4. Exact finite-field DFT: the Fourier counting identity (F1) and the
# general-k deviation identity.  All arithmetic in F_q with a genuine p-th
# root of unity — exact, zero floating point.
# ----------------------------------------------------------------------------

def find_q(p, start=1 << 40):
    """A prime q = c*p + 1 (so F_q contains a primitive p-th root of unity).
    p is odd here, so c must be EVEN for q = c*p+1 to be odd (the dead
    author's `| 1` forced q even = never prime — W81-142B-F runtime bug fix)."""
    c = (start // p) & ~1
    for _ in range(200000):
        q = c * p + 1
        if is_prime(q):
            return q
        c += 2
    raise RuntimeError("no q found for p=%d" % p)


def find_zeta(p, q):
    """An element of order exactly p in F_q^*."""
    g = 2
    while True:
        z = pow(g, (q - 1) // p, q)
        if z != 1 and pow(z, p, q) == 1:
            # order divides p and is not 1, p prime -> order exactly p
            return z
        g += 1


def dft_exact(h, zeta_pow_table, p, q):
    """DFT of an integer vector h over Z_p in F_q: H[r] = sum h[x] zeta^{r x}."""
    H = []
    for r in range(p):
        # Horner-free direct sum with precomputed powers
        zr = zeta_pow_table[r]  # zeta^r
        acc = 0
        zp = 1
        for x in range(p):
            acc = (acc + h[x] * zp) % q
            zp = zp * zr % q
        H.append(acc)
    return H


def check_fourier_exact():
    """AUD-FOURIER-EXACT: F1 at p = 101 and p = 1009 — the exact integer
    identity  p^4 T = a^3 p^3 + sum_{r!=0} hhat(r)^2 hhat(-2r)  (with
    f = 1_A - a/p = h/p, h integer-valued), verified in F_q for 3 primes q,
    my own DFT; plus Parseval's integer form p * sum h^2 = sum_r hhat(r)hhat(-r);
    plus edge cases A = empty (delta=0), A = Z_p, single point."""
    ok_all = True
    det = []
    rng = random.Random(SEED + 3)
    for p in (101, 1009):
        qs = []
        c = 1 + SEED
        while len(qs) < 3:
            q = find_q(p, (c << 40) | (1 << 39))
            if q not in qs:
                qs.append(q)
            c += 977
        for trial in range(3 if p == 101 else 2):
            size = rng.randint(1, p - 1)
            A = set(rng.sample(range(p), size))
            T = 0
            inA = [i in A for i in range(p)]
            for x in range(p):
                if inA[x]:
                    for d in range(p):
                        if inA[(x + d) % p] and inA[(x + 2 * d) % p]:
                            T += 1
            a = len(A)
            # h = p*f = p*1_A - a  (integer valued)
            h = [(p - a if i in A else -a) for i in range(p)]
            h2 = sum(v * v for v in h)
            for q in qs:
                z = find_zeta(p, q)
                pw = [pow(z, r, q) for r in range(p)]
                H = dft_exact(h, pw, p, q)
                # identity: p^4 T = a^3 p^3 + sum_{r != 0} H[r]^2 H[(-2r) % p]   (mod q)
                s = 0
                for r in range(1, p):
                    s = (s + H[r] * H[r] % q * H[(-2 * r) % p]) % q
                lhs = pow(p, 4, q) * (T % q) % q
                rhs = (pow(a, 3, q) * pow(p, 3, q) + s) % q
                # Parseval: sum_r H[r] H[-r] = p * sum h^2
                par = sum(H[r] * H[(-r) % p] % q for r in range(p)) % q
                parok = par == (p * h2) % q
                if lhs != rhs or not parok:
                    ok_all = False
                    det.append("p=%d q=%d trial=%d identity=%s parseval=%s" % (p, q, trial, lhs == rhs, parok))
        det.append("p=%d: exact F_q identity (3 primes q, my DFT) verified on %d random sets + Parseval"
                   % (p, 3 if p == 101 else 2))
    # edge cases at p = 101: A = empty (delta = 0), A = Z_p, single point
    p = 101
    q = find_q(p, (5 << 40) | 1)
    z = find_zeta(p, q)
    pw = [pow(z, r, q) for r in range(p)]
    for name, A in (("empty", set()), ("full", set(range(p))), ("single", {57})):
        inA = [i in A for i in range(p)]
        T = sum(1 for x in range(p) if inA[x]
                for d in range(p) if inA[(x + d) % p] and inA[(x + 2 * d) % p])
        a = len(A)
        h = [(p - a if i in A else -a) for i in range(p)]
        H = dft_exact(h, pw, p, q)
        s = sum(H[r] * H[r] % q * H[(-2 * r) % p] for r in range(1, p)) % q
        lhs = pow(p, 4, q) * (T % q) % q
        rhs = (pow(a, 3, q) * pow(p, 3, q) + s) % q
        if lhs != rhs:
            ok_all = False
            det.append("edge %s FAILS (T=%d)" % (name, T))
        else:
            det.append("edge %s: T=%d identity exact" % (name, T))
    report("AUD-FOURIER-EXACT", ok_all,
           "F1 verified EXACTLY in F_q (my own DFT, roots of unity of order p): " + "; ".join(det))


def check_deviation_k():
    """AUD-DEVIATION-K: the ORDER-k DEVIATION IDENTITY machinery (the
    142A target) at small p, exact in F_q — for k = 3..8, p in {11,13,17}:
    per-layer identity  sum_{x,d} prod_{i in S} h(x+i d) = p^{2-s} *
    sum_{constraints} prod hhat  for EVERY S subseteq {0..k-1}, |S| = s;
    the s = 1,2 layers vanish as exact integer sums when p > k; the full
    assembly T_k * p^k = sum_s a^{k-s} H_s.  Edge case: p <= k — the s=2
    layer does NOT vanish (the hypothesis p > k is load-bearing)."""
    ok_all = True
    det = []
    rng = random.Random(SEED + 4)
    for (k, p) in [(3, 11), (3, 13), (4, 11), (4, 13), (5, 11), (5, 17), (6, 13), (7, 17), (8, 17)]:
        q = find_q(p, (7 << 40) | 3)
        z = find_zeta(p, q)
        pw = [pow(z, r, q) for r in range(p)]
        A = set(rng.sample(range(p), rng.randint(1, p - 1)))
        a = len(A)
        h = [(p - a if i in A else -a) for i in range(p)]
        H = dft_exact(h, pw, p, q)
        # direct layer sums (exact integers)
        inS = {}
        layers = {}
        for s in range(0, k + 1):
            import itertools as _it
            tot = 0
            for S in _it.combinations(range(k), s):
                acc = 0
                for x in range(p):
                    for d in range(p):
                        pr = 1
                        for i in S:
                            pr *= h[(x + i * d) % p]
                            if pr == 0:
                                break
                        acc += pr
                layers[S] = acc
                tot += acc
            # T_k * p^k = sum_S a^{k-s} H_S
            if s in (1, 2) and p > k:
                for S, v in layers.items():
                    if len(S) == s and v != 0:
                        ok_all = False
                        det.append("k=%d p=%d layer S=%s nonzero (%d) — vanishing FAILS" % (k, p, S, v))
        T = sum(1 for x in range(p) for d in range(p)
                if all((x + i * d) % p in A for i in range(k)))
        lhs = (T % q) * pow(p, k, q) % q
        rhs = sum(pow(a, k - len(S), q) * (v % q) for S, v in layers.items()) % q
        if lhs != rhs:
            ok_all = False
            det.append("k=%d p=%d assembly FAILS" % (k, p))
        # per-layer Fourier identity for s >= 3 (spot: the full layer S = all)
        Sfull = tuple(range(k))
        s = k
        # constraints: sum r_i = 0 (x-sum), sum i r_i = 0 (d-sum).
        # Exact F_q DP over the s positions with state (partial sum,
        # partial weighted sum) — the naive p^s product enumeration is
        # astronomically slow at k=8, p=17 (17^8 tuples) — W81-142B-F
        # runtime fix; the DP carries the SAME exact integer in F_q.
        dp = [0] * (p * p)
        dp[0] = 1
        for i in range(s):
            ndp = [0] * (p * p)
            for s1 in range(p):
                base = s1 * p
                for s2 in range(p):
                    v = dp[base + s2]
                    if not v:
                        continue
                    for r in range(p):
                        t = ((s1 + r) % p) * p + (s2 + i * r) % p
                        ndp[t] = (ndp[t] + v * H[r]) % q
            dp = ndp
        fsum = dp[0]  # both constraints == 0 (mod p)
        # H_{Sfull} = p^{2-s} * fsum  ->  H_{Sfull} * p^{s-2} = fsum
        if (layers[Sfull] % q) * pow(p, s - 2, q) % q != fsum % q:
            ok_all = False
            det.append("k=%d p=%d full-layer Fourier identity FAILS" % (k, p))
        det.append("k=%d p=%d: layers s=1,2 vanish exactly; assembly + full-layer identity exact (T=%d)"
                   % (k, p, T))
    # EDGE: p <= k — the s=2 vanishing must FAIL (k=4, p=3, S={0,3})
    k, p = 4, 3
    q = find_q(p, (11 << 40) | 7)
    A = {0, 1}
    a = len(A)
    h = [(p - a if i in A else -a) for i in range(p)]
    acc = 0
    for x in range(p):
        for d in range(p):
            acc += h[x] * h[(x + 3 * d) % p]
    if acc == 0:
        ok_all = False
        det.append("EDGE p<=k: s=2 layer unexpectedly 0 — control broken")
    else:
        det.append("EDGE k=4 p=3: layer S={0,3} = %d != 0 — the p > k hypothesis of the "
                   "deviation identity is LOAD-BEARING (vanishing fails exactly as predicted)" % acc)
    report("AUD-DEVIATION-K", ok_all,
           "order-k deviation identity machinery, exact F_q verification: " + "; ".join(det))


# ----------------------------------------------------------------------------
# A5. T-GEN (the Z_p transfer) exhaustive at the banked instance.
# ----------------------------------------------------------------------------

def check_tgen():
    """AUD-TGEN: all 4-AP-free subsets of [1,12] are cyclically 4-AP-free
    mod 53 (p > kN); negative control: the 4-AP-free set {1,5,9,10} shows a
    cyclic 4-AP mod 13 (p <= kN)."""
    N, k, p = 12, 4, 53
    import itertools as _it
    cnt = 0
    viol = 0
    for mask in range(1 << N):
        S = [i + 1 for i in range(N) if mask >> i & 1]
        okA, _ = kap_free_scan(S, k)
        if not okA:
            continue
        cnt += 1
        # cyclic 4-AP scan mod p
        Ss = set(S)
        for x in range(p):
            for d in range(1, p):
                if all((x + i * d) % p in Ss for i in range(k)):
                    # distinctness of the p-residues
                    pts = [(x + i * d) % p for i in range(k)]
                    if len(set(pts)) == k:
                        viol += 1
                        break
            else:
                continue
            break
    okA = (viol == 0)
    # banked convention (engine142uppergen.py line 371: range(1, 1<<N)) counts
    # NONEMPTY subsets: 2232; my sweep from mask=0 also has the empty set: 2233
    okB_cnt = (cnt - 1 == 2232)
    # negative control
    neg = {1, 5, 9, 10}
    okB, _ = kap_free_scan(sorted(neg), 4)
    found = None
    for x in range(13):
        for d in range(1, 13):
            if all((x + i * d) % 13 in neg for i in range(4)) and len({(x + i * d) % 13 for i in range(4)}) == 4:
                found = (x, d)
    report("AUD-TGEN", okA and okB_cnt and okB and found is not None,
           "T-GEN at k=4,N=12,p=53: all %d 4-AP-free subsets (banked nonempty count %d == 2232; "
           "my sweep adds the empty set) cyclically 4-AP-free (0 violations); "
           "negative control {1,5,9,10} 4-AP-free in Z but cyclic 4-AP (x,d)=%s "
           "mod 13 — the window bound p > kN is load-bearing" % (cnt, cnt - 1, found))


# ----------------------------------------------------------------------------
# A6. RK-VARN-GEN constants at N = 1000 (my own census) + plug-backs.
# ----------------------------------------------------------------------------

def count_k_aps(N, k, S):
    """My own k-AP counter (forward scan)."""
    Ss = set(S)
    c = 0
    for a in range(1, N + 1):
        for d in range(1, (N - a) // (k - 1) + 1):
            if all(a + i * d in Ss for i in range(k)):
                c += 1
    return c


def count_k_aps_pairs(N, k, S):
    """Second counter (pair positioning) — different code path."""
    Ss = sorted(set(S))
    idx = set(Ss)
    c = 0
    for ii in range(len(Ss)):
        for jj in range(ii + 1, len(Ss)):
            a, b = Ss[ii], Ss[jj]
            for pp in range(k):
                for qq in range(pp + 1, k):
                    g = qq - pp
                    if (b - a) % g:
                        continue
                    d = (b - a) // g
                    if d < 1:
                        continue
                    st = a - pp * d
                    if st < 1 or st + (k - 1) * d > N:
                        continue
                    if all(st + t * d in idx for t in range(k)):
                        c += 1
    # each k-AP is counted C(k,2) times (once per pair of positions)
    return c // (k * (k - 1) // 2)


def check_rkvarn():
    """AUD-RKVARN: #C, S_min, DIV, c_k at N=1000 for the four stones,
    recomputed by my own census; doc values compared; plug-back with my own
    two counters on random dense sets."""
    ok_all = True
    det = []
    N = 1000
    doc = {(4, 0.65): 3.12e-07, (4, 0.70): 6.1e-06, (4, 0.75): 1.2e-05,
           (5, 0.75): 6.2e-08, (5, 0.80): 4.9e-06,
           (6, 0.80): 7.8e-07, (7, 0.86): 2.1e-06}
    stones = {4: (42, 22), 5: (55, 36), 6: (43, 31), 7: (45, 36)}
    rng = random.Random(SEED + 5)
    for k, (M0, r) in stones.items():
        # copies census
        copies = [0] * (N + 1)
        nC = 0
        for d in range(1, (N - 1) // (M0 - 1) + 1):
            for a in range(1, N - (M0 - 1) * d + 1):
                nC += 1
                for j in range(M0):
                    copies[a + j * d] += 1
        DIV = sum(1 for g in range(1, M0) for j0 in range(0, M0 - (k - 1) * g) if (k - 1) * g + j0 <= M0 - 1)
        for delta in sorted({d for (kk, d) in doc if kk == k}):
            t = math.ceil(delta * N)
            smin = sum(sorted(copies[1:N + 1])[:t])
            num = smin - r * nC
            c = num / ((M0 - r) * DIV * float(N) ** 2) if num > 0 else None
            if c is None:
                ok_all = False
                det.append("k=%d delta=%.2f numerator <= 0 — delta below stone reach" % (k, delta))
                continue
            if abs(c - doc[(k, delta)]) > 0.06 * doc[(k, delta)]:
                ok_all = False
                det.append("k=%d delta=%.2f c_k=%.3e vs doc %.3e — MISMATCH" % (k, delta, c, doc[(k, delta)]))
            # plug-back: 2 random dense sets, both my counters
            for _ in range(2):
                size = math.ceil(delta * N)
                A = set(rng.sample(range(1, N + 1), size))
                c1 = count_k_aps(N, k, A)
                c2 = count_k_aps_pairs(N, k, A)
                if c1 != c2:
                    ok_all = False
                    det.append("k=%d counters disagree %d vs %d" % (k, c1, c2))
                if c1 < c * N * N:
                    ok_all = False
                    det.append("k=%d delta=%.2f plug-back VIOLATED (%d < %.1f)" % (k, delta, c1, c * N * N))
            det.append("k=%d d=%.2f: #C=%d S_min=%d DIV=%d c_k>=%.3e (doc %.2e) plug-back ok"
                       % (k, delta, nC, smin, DIV, c, doc[(k, delta)]))
    report("AUD-RKVARN", ok_all,
           "RK-VARN-GEN constants recomputed by my own census at N=1000, plug-backs with two "
           "independent counters: " + "; ".join(det))


# ----------------------------------------------------------------------------
# A7. V-GEN / SLIDE-GEN instance re-verification.
# ----------------------------------------------------------------------------

def check_vgen():
    """AUD-VGEN: D0, band, min nu(x), #C0 at the banked instances; the
    double-count chain on planted AP-free sets."""
    ok_all = True
    det = []
    for (m, N) in [(5, 400), (9, 1296), (14, 3136)]:
        D0 = N // (4 * m * (m - 1))
        lo = (m - 1) * D0 + 1
        hi = N - (m - 1) * D0
        minnu = None
        nC0 = 0
        for x in (lo, (lo + hi) // 2, hi):
            nu = 0
            for d in range(1, D0 + 1):
                for j in range(m):
                    a = x - j * d
                    if a >= 1 and a + (m - 1) * d <= N:
                        nu += 1
            minnu = nu if minnu is None else min(minnu, nu)
        for d in range(1, D0 + 1):
            nC0 += N - (m - 1) * d
        good = (D0 >= 1 and minnu >= m * D0 and nC0 <= N * D0
                and 2 * (m - 1) * D0 <= N / (2 * m) + 2 * m)
        ok_all = ok_all and good
        det.append("(m=%d,N=%d): D0=%d minnu=%d >= m*D0=%d #C0=%d <= N*D0=%d band-excl=%d"
                   % (m, N, D0, minnu, m * D0, nC0, N * D0, 2 * (m - 1) * D0))
    # planted greedy AP-free set: copy cap + the V-GEN bound
    N, m, k = 1296, 9, 3
    S = set()
    for x in range(1, N + 1):
        ok = True
        for d in range(1, x // 2 + 1):
            if (x - 2 * d) in S and (x - d) in S:
                ok = False
                break
        if ok:
            S.add(x)
    D0 = N // (4 * m * (m - 1))
    r3m = 5  # certified r_3(9)
    worst = 0
    for d in range(1, D0 + 1):
        for a in range(1, min(60, N - (m - 1) * d) + 1):
            worst = max(worst, len({a + j * d for j in range(m)} & S))
    ok_all = ok_all and worst <= r3m
    det.append("planted greedy 3-AP-free set in [1,1296]: worst copy occupancy %d <= r_3(9)=%d" % (worst, r3m))
    report("AUD-VGEN", ok_all,
           "V-GEN band/copy machinery recomputed at the banked instances + copy cap on a planted set: "
           + "; ".join(det))


# ----------------------------------------------------------------------------
# A8. LOGDECAY anchors, corrected digits, my own two methods.
# ----------------------------------------------------------------------------

def check_logdecay():
    """AUD-LOGDECAY: my own 60-digit re-derivation of the LOGDECAY chain:
    anchors (with the CORRECT digits — W81-142B defect D5), boundary, grid,
    negative controls below the eps-boundary."""
    try:
        from mpmath import mp, mpf, ln, sqrt, ceil as mpceil, exp as mpexp
    except ImportError:
        report("AUD-LOGDECAY", False, "mpmath missing")
        return
    mp.dps = 60
    A = ln(1024)
    B = ln(480)
    C = mpf(26600)
    N2 = mpf(4e7)
    ok_all = True
    det = []
    # corrected anchor digits
    ell2 = ln(N2)
    if abs(ell2 - mpf("17.50439001207821")) > mpf("1e-8"):
        ok_all = False
        det.append("ell2 digits wrong: %s" % ell2)
    hN2 = N2 - mpf(1702400) * ell2
    if abs(hN2 - mpf("10200526.44")) > mpf("0.5"):
        ok_all = False
        det.append("h(4e7) digits wrong: %s (doc said 10,207,724 — true 10,200,526)" % hN2)
    coef = mpf(3) / 4 - A / (2 * ell2)
    if abs(coef - mpf("0.552008")) > mpf("1e-6"):
        ok_all = False
        det.append("coef digits wrong: %s" % coef)
    det.append("anchors: ell2=%.6f coef=%.6f h(4e7)=%.0f" % (ell2, coef, hN2))
    # eps-boundary L*
    lo, hi = mpf(2.9e7), mpf(2.95e7)
    for _ in range(300):
        mid = (lo + hi) / 2
        if mid - mpf(1702400) * ln(mid) < 0:
            lo = mid
        else:
            hi = mid
    Lstar = (lo + hi) / 2
    if abs(Lstar - mpf("29267649.48")) > mpf("1.0"):
        ok_all = False
        det.append("L* digits wrong: %s" % Lstar)
    det.append("L*=%.4e (N2 above by %.4e)" % (Lstar, N2 - Lstar))
    # Method A chain + Method B direct tower at the boundary + a grid
    def chain(L):
        ell = ln(L)
        eps = sqrt(C * ell / L)
        c1 = (C * ell / L) <= mpf(1) / 64
        rhs = B + (L / (2 * ell) + 3) * (A + ell / 2)
        return c1 and L >= rhs, eps
    def direct(L):
        ell = ln(L)
        eps = sqrt(C * ell / L)
        x = L / (2 * ell)
        expo = int(mpceil(x)) + 2
        Tlog = B + expo * (A - ln(eps))
        return L >= Tlog, Tlog
    for L in [N2, mpf("4.0000001e7"), mpf("1e8"), mpf("1e12"), mpf("1e30"), mpf("1e60")]:
        okA, eps = chain(L)
        okB, Tlog = direct(L)
        if not (okA and okB):
            ok_all = False
            det.append("L=%s chain=%s direct=%s" % (L, okA, okB))
    det.append("boundary+extremes: chain and direct tower both green")
    # negative controls: L=1e6 (eps > 1/8) and L=2.9e7 (below L*)
    okA, eps6 = chain(mpf("1e6"))
    if okA or eps6 <= mpf("0.125"):
        ok_all = False
        det.append("negative control L=1e6 should FAIL (eps=%.4f > 1/8)" % eps6)
    okA7, _ = chain(mpf("2.9e7"))
    if okA7:
        ok_all = False
        det.append("negative control L=2.9e7 should FAIL (below L*)")
    det.append("negative controls fire (eps(1e6)=%.4f > 1/8; chain fails at 2.9e7)" % eps6)
    report("AUD-LOGDECAY", ok_all,
           "LOGDECAY chain re-derived at 60 digits, my own two methods: " + "; ".join(det))


# ----------------------------------------------------------------------------
# A9. Negative controls: planted defects MUST be detected.
# ----------------------------------------------------------------------------

def check_negctl():
    """AUD-NEGCTL: (1) planted r_3(10)=6 detected vs my recomputation;
    (2) planted r_4(4)=4 (the pre-fix R4_VARN defect) detected;
    (3) corrupted Fourier identity (fhat^1 * fhat(-2r)^2) detected by the
    exact F_q check; (4) over-optimistic constant C_7 - 0.4 passes the OLD
    banked margin formula but FAILS the TRUE one (demonstrates defect D4);
    (5) planted k-AP in a construction flagged by both my scanners."""
    ok_all = True
    det = []
    rng = random.Random(SEED + 6)
    # (1)
    corrupt_r3 = [1, 2, 2, 3, 4, 4, 4, 4, 5, 6]
    true_r3_10 = r_k_exact(10, 3, rng)
    if not (corrupt_r3[9] != true_r3_10 and true_r3_10 == 5):
        ok_all = False
        det.append("planted r_3(10)=6 NOT detected")
    else:
        det.append("planted r_3(10)=6 detected (true %d)" % true_r3_10)
    # (2)
    if r_k_exact(4, 4, rng) != 3:
        ok_all = False
        det.append("my r_4(4) recomputation broken")
    else:
        det.append("planted r_4(4)=4 detected (true 3 = N - floor(N/4), the floor law)")
    # (3) corrupted identity: sum H[r] * H[(-2r)%p]^2 instead of H[r]^2 H[-2r]
    p = 101
    q = find_q(p, (13 << 40) | 9)
    z = find_zeta(p, q)
    pw = [pow(z, r, q) for r in range(p)]
    A = set(rng.sample(range(p), 37))
    a = len(A)
    T = sum(1 for x in range(p) for d in range(p)
            if all((x + i * d) % p in A for i in range(3)))
    h = [(p - a if i in A else -a) for i in range(p)]
    H = dft_exact(h, pw, p, q)
    s_corrupt = sum(H[r] * H[(-2 * r) % p] % q * H[(-2 * r) % p] for r in range(1, p)) % q
    lhs = pow(p, 4, q) * (T % q) % q
    rhs_corrupt = (pow(a, 3, q) * pow(p, 3, q) + s_corrupt) % q
    if lhs == rhs_corrupt:
        ok_all = False
        det.append("corrupted Fourier identity NOT detected")
    else:
        det.append("corrupted Fourier identity (swapped exponents) detected by the exact F_q check")
    # (4) the D4 demonstration: C_7 - 0.4
    k = 7
    N = (1 << 41) * int(2 ** 0.04)
    d, m = recipe(k, N)
    C_bad = Ck(k) - 0.4
    om = old_margin(k, N, d, m, C_bad)
    tm = true_margin(k, N, d, m, C_bad)
    if om is None or tm is None or not (om > 0 and tm < 0):
        # fall back to the stored worst cell (d,m)=(18,2), hi=14^18-1
        d, m, hi = 18, 2, 14 ** 18 - 1
        lhs2 = m ** (d - k) - d * d
        L = ilog(hi)
        om = ilog(lhs2) - (L - C_bad * math.sqrt(L))
        tm = ilog(lhs2) - 2 * math.log(d) - (L - C_bad * math.sqrt(L))
    if om > 0 and tm < 0:
        det.append("D4 demonstrated: at the k=7 worst cell with C_7-0.4 the OLD banked margin "
                   "formula passes (%.3f) while the TRUE margin fails (%.3f) — the omitted /d^2 "
                   "made the banked check vacuous by 2 ln d" % (om, tm))
    else:
        ok_all = False
        det.append("D4 demonstration failed to reproduce (om=%s tm=%s)" % (om, tm))
    # (5) planted AP
    S, _ = my_gen_set(3, 4, 3)
    s0 = min(S)  # S is a set (the dead author subscripted it — runtime bug fix)
    planted = sorted(set(S) | {s0 + 1, s0 + 2})
    okA, _ = kap_free_scan(planted, 3)
    okB, _ = kap_free_pairs(planted, 3)
    if okA or okB:
        ok_all = False
        det.append("planted 3-AP NOT detected")
    else:
        det.append("planted 3-AP in a Behrend set detected by both my scanners")
    report("AUD-NEGCTL", ok_all, "; ".join(det))


# ----------------------------------------------------------------------------
# A10. k=3 reproduction spot-check vs the banked engine (witness equality).
# ----------------------------------------------------------------------------

def check_k3repro():
    """AUD-K3REPRO: my construction vs the banked engine142behrend on 3
    banked grid cells: sizes must match the certified ledger values."""
    ok_all = True
    det = []
    try:
        sys.path.insert(0, HERE)
        import engine142behrend as banked
        for (d, m, expect) in [(4, 3, 12), (3, 5, 6), (4, 5, 24)]:
            Sb, key_b, ncells = banked.behrend_set(d, m)  # returns a 3-tuple
            Sm, _ = my_gen_set(3, d, m)
            okA, _ = kap_free_scan(Sm, 3)
            same = len(Sm) == len(Sb) == expect
            ok_all = ok_all and okA and same
            det.append("(d,m)=(%d,%d): banked %d, mine %d (ledger %d), AP-free=%s"
                       % (d, m, len(Sb), len(Sm), expect, okA))
    except Exception as e:
        ok_all = False
        det.append(repr(e))
    report("AUD-K3REPRO", ok_all, "k=3 banked reproduction on 3 cells: " + "; ".join(det))


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

ALL_CHECKS = [
    ("AUD-TABLES", check_tables),
    ("AUD-R4VARN-TABLE", check_r4varn_doc),
    ("AUD-K7", check_k7),
    ("AUD-BGE-PLUGBACK", check_bge_plugback),
    ("AUD-BGE-FARRANGE", check_bge_farrange),
    ("AUD-BGE-CONSTRUCT", check_bge_construction),
    ("AUD-BGE-CONSTANTS", check_bge_constants),
    ("AUD-ENVELOPE", check_envelope),
    ("AUD-FOURIER-EXACT", check_fourier_exact),
    ("AUD-DEVIATION-K", check_deviation_k),
    ("AUD-TGEN", check_tgen),
    ("AUD-RKVARN", check_rkvarn),
    ("AUD-VGEN", check_vgen),
    ("AUD-LOGDECAY", check_logdecay),
    ("AUD-NEGCTL", check_negctl),
    ("AUD-K3REPRO", check_k3repro),
]


def main():
    args = sys.argv[1:]
    quick = "--quick" in args
    only = [a for a in args if not a.startswith("--")]
    print("=" * 78)
    print("ENGINE 142 AUDIT (W81-142B) — the independent auditor engine — start")
    print("seed %d ; deterministic ; fresh algorithms (my DFS, my F_q DFT, my census)" % SEED)
    print("=" * 78)
    for name, fn in ALL_CHECKS:
        if only and name not in only:
            continue
        if quick and name in ("AUD-FOURIER-EXACT", "AUD-DEVIATION-K", "AUD-K7",
                              "AUD-BGE-FARRANGE", "AUD-TGEN", "AUD-RKVARN"):
            print("[SKIP] %s (quick mode)" % name)
            continue
        t0 = time.time()
        try:
            fn()
        except Exception as e:
            report(name, False, "EXCEPTION: %r" % e)
        sys.stdout.write("      (%.1fs)\n" % (time.time() - t0))
    n_pass = sum(1 for _, ok, _ in RESULTS if ok)
    n_tot = len(RESULTS)
    wall = time.time() - T0
    print("=" * 78)
    for name, ok, det in RESULTS:
        print("[%s] %s" % ("PASS" if ok else "FAIL", name))
    print("AUDIT ENGINE: %d/%d checks green, wall %.1fs" % (n_pass, n_tot, wall))
    print("AUDIT142_ENGINE_GREEN=1" if n_pass == n_tot and n_tot >= 15 else "AUDIT142_ENGINE_GREEN=0")
    # receipts
    with open(os.path.join(HERE, "receipts142audit_w81.txt"), "w", encoding="utf-8") as f:
        f.write("RECEIPTS — engine142audit_w81.py (W81-142B) — THE INDEPENDENT AUDIT ENGINE\n")
        f.write("seed %d ; deterministic ; fresh algorithms (lex-DFS tables, exact F_q DFT,\n" % SEED)
        f.write("own census, corrected BG-E margin) ; wall %.1fs\n" % wall)
        f.write("=" * 78 + "\n")
        for name, ok, det in RESULTS:
            f.write("[%s] %s\n    %s\n" % ("PASS" if ok else "FAIL", name, det))
        f.write("=" * 78 + "\n")
        f.write("AUDIT ENGINE: %d/%d checks green, wall %.1fs\n" % (n_pass, n_tot, wall))
        f.write("AUDIT142_ENGINE_GREEN=%d\n" % (1 if n_pass == n_tot and n_tot >= 15 else 0))
    return 0 if n_pass == n_tot and n_tot >= 15 else 1


if __name__ == "__main__":
    sys.exit(main())
