#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W67-142D -- Erdos Problem #142 DOUBTER MIRROR BATTERY (Task ID W67-142D)
=========================================================================
Frozen statement: "Let r_k(N) be the largest possible size of a subset of
{1,...,N} that does not contain any non-trivial k-term arithmetic
progression. Prove an asymptotic formula for r_k(N)." (Erdos, $10000,
erdosproblems.com/142.)

CONVENTION (pinned, the kernel header must pin the same): a non-trivial
k-term arithmetic progression is  a, a+d, ..., a+(k-1)d  with d >= 1
(distinct terms). Under this convention r_2(N) = 1 for N >= 2 (any two
distinct elements are a 2-AP). Under the alternative convention
"non-trivial means k >= 3" the r_2 claim is void.

KILLER CLAIMS UNDER AUDIT (this battery re-runs everything end-to-end and
exits nonzero on ANY failure):
  C1  T = ternary-digit-{0,1} set is 3-AP-free            (dual scan, k<=8)
  C2  r_3(3^k - 1) >= 2^k - 1 (Cantor lower bound)        (exact B&B table)
  C3  r_k(N) <= (k-1)*floor(N/k) + (N mod k)              (domination audit)
  C4  r_2(N) = 1 for N >= 2                               (exact k=2 table)
  C5  exact small r_3(N) values                           (independent table)

ENGINES (exact integer arithmetic only; no floats in any verification claim):
  Engine A  branch-and-bound DFS over elements 1..N with AP-completion
            propagation pruning (maintained forbidden set) + exact-suffix
            bounds from the incrementally built table (translation invariance:
            an AP-free set inside [i,N] has at most r_k(N-i+1) elements).
  Engine B  z3 SAT/UNSAT certificates: SAT at the claimed value
            (feasibility) + UNSAT at claimed+1 (optimality proof). Any z3
            counterexample is independently re-validated in exact python.
  Engine C  exhaustive 2^N brute force (N <= 12, 100% agreement required).
  Cantor census digitizers (three independent methods): digit-free divmod
            integer scan, digit-vector cartesian product, gmpy2.digits(.,3).

Artifacts written next to this file (deterministic, no timestamps):
  r3_exact_table.json   exact r_3 (N<=30) + r_4/r_5 (N<=20) + r_2 (N<=30)
                        tables with witnesses, block-bound margins, exact
                        ratios, Cantor-vs-true gap, OEIS-printed diffs.
  cantor_cert.txt       dual-method T_k certification (k<=8) + the
                        complement (maximality-niche) scan for T_8.

Success line (printed iff every check passes): E142_DOUBTER_BATTERY_GREEN
"""

import json
import sys
import time
from fractions import Fraction
from itertools import product
from pathlib import Path

try:
    import z3
    HAVE_Z3 = True
    Z3_ERR = ""
except Exception as exc:  # pragma: no cover
    HAVE_Z3 = False
    Z3_ERR = repr(exc)

try:
    import gmpy2
    HAVE_GMPY2 = True
    GMPY2_ERR = ""
except Exception as exc:  # pragma: no cover
    HAVE_GMPY2 = False
    GMPY2_ERR = repr(exc)

ART = Path(__file__).resolve().parent
T0 = time.time()

R3_NMAX = 30      # exact r_3 table (mission: N <= 30)
R4_NMAX = 20      # exact r_4 frontier (mission: N <= 20)
R5_NMAX = 20      # exact r_5 frontier (mission: N <= 20)
R2_NMAX = 30      # k=2 edge audit
BRUTE_NMAX = 12   # brute-force cross-check range (mission: N <= 12)
CANTOR_KMAX = 8   # 3^8 - 1 = 6560, |T_8| = 256

FAILURES = []
NOTES = []


def log(msg=""):
    print(msg, flush=True)


def fail(claim, msg):
    FAILURES.append("[%s] %s" % (claim, msg))
    log("  [FAIL][%s] %s" % (claim, msg))


def note(msg):
    NOTES.append(msg)
    log("  [intel] %s" % msg)


def elapsed():
    return "[t+%6.1fs]" % (time.time() - T0)


# ============================================================================
# AP machinery (exact integers only)
# ============================================================================

def all_k_aps(N, k):
    """All k-APs (a, a+d, ..., a+(k-1)d) with d>=1, a>=1, a+(k-1)d<=N.
    (a,d)-driven enumeration."""
    aps = []
    if k >= 2 and N >= k:
        for d in range(1, (N - 1) // (k - 1) + 1):
            top = N - (k - 1) * d
            for a in range(1, top + 1):
                aps.append(tuple(a + j * d for j in range(k)))
    return aps


def all_k_aps_endpoint_method(N, k):
    """Independent AP census: endpoint-driven. Every k-AP is uniquely
    determined by its first and last elements (span divisible by k-1)."""
    aps = set()
    if k >= 2:
        for a in range(1, N + 1):
            for z in range(a + k - 1, N + 1):
                span = z - a
                if span % (k - 1) == 0:
                    d = span // (k - 1)
                    aps.add(tuple(a + j * d for j in range(k)))
    return aps


def aps_through_index(N, k, aps=None):
    """aps_through[i] = list of k-APs containing element i (1-based)."""
    if aps is None:
        aps = all_k_aps(N, k)
    through = [[] for _ in range(N + 1)]
    for ap in aps:
        for t in ap:
            through[t].append(ap)
    return through


def is_ap_free(S, k):
    """Independent validator: no k-AP of [1, max(S)] is fully inside S."""
    if not S:
        return True
    Sset = set(S)
    for ap in all_k_aps(max(S), k):
        for t in ap:
            if t not in Sset:
                break
        else:
            return False
    return True


def block_bound(N, k):
    """The killer's block upper bound: (k-1)*floor(N/k) + (N mod k)."""
    return (k - 1) * (N // k) + (N % k)


# ============================================================================
# Engine A: branch-and-bound with AP-completion propagation
# ============================================================================

def greedy_rk(N, k):
    """Smallest-first greedy k-AP-free subset of [1,N] (a valid witness)."""
    through = aps_through_index(N, k)
    S = set()
    for x in range(1, N + 1):
        ok = True
        for ap in through[x]:
            complete = True
            for t in ap:
                if t != x and t not in S:
                    complete = False
                    break
            if complete:
                ok = False
                break
        if ok:
            S.add(x)
    return len(S), sorted(S)


def bb_exact_rk(N, k, suffix_exact, seed_best, seed_wit):
    """Maximum size of a k-AP-free subset of [1,N] by branch-and-bound.

    suffix_exact: {L: r_k(L)} for L < N (exact values, translation invariance
    gives the sound future bound r_k(N-i+1) for the undecided suffix).
    seed_best/seed_wit: a validated k-AP-free witness inside [1,N].
    Pruning: (1) include only if not AP-completion-forbidden; including an
    element propagates new forbiddances (every future element that would
    complete a k-AP with the chosen set); (2) prune when size + min(avail,
    exact suffix bound) <= best (cannot strictly improve).
    """
    through = aps_through_index(N, k)
    best = seed_best
    bestwit = list(seed_wit)
    inS = set()
    S = []
    forbidden = {}

    def dfs(i, size, avail):
        nonlocal best, bestwit
        if i > N:
            if size > best:
                best = size
                bestwit = list(S)
            return
        L = N - i + 1
        sb = suffix_exact.get(L)
        poss = avail if sb is None else (avail if avail < sb else sb)
        if size + poss <= best:
            return
        # INCLUDE branch (only if i is not forbidden: S + {i} stays AP-free)
        if i not in forbidden:
            S.append(i)
            inS.add(i)
            touched = []
            for ap in through[i]:
                nmiss = 0
                miss = 0
                for t in ap:
                    if t != i and t not in inS:
                        nmiss += 1
                        miss = t
                if nmiss == 1 and miss > i:
                    t = miss
                    c = forbidden.get(t, 0)
                    forbidden[t] = c + 1
                    if c == 0:
                        avail -= 1
                    touched.append(t)
            dfs(i + 1, size + 1, avail)
            for t in touched:
                c = forbidden[t] - 1
                if c == 0:
                    del forbidden[t]
                    avail += 1
                else:
                    forbidden[t] = c
            inS.discard(i)
            S.pop()
        # EXCLUDE branch
        if i not in forbidden:
            dfs(i + 1, size, avail - 1)
        else:
            dfs(i + 1, size, avail)

    dfs(1, 0, N)
    return best, bestwit


def build_exact_table(k, Nmax):
    """Engine A: incremental exact r_k(N) table for N = 1..Nmax."""
    table = {}
    for N in range(1, Nmax + 1):
        suffix_exact = {L: table[L][0] for L in range(1, N)}
        suffix_exact[0] = 0
        seed_best, seed_wit = 0, []
        if N - 1 in table and table[N - 1][0] > seed_best:
            seed_best, seed_wit = table[N - 1]
        g = greedy_rk(N, k)
        if g[0] > seed_best:
            seed_best, seed_wit = g
        r, wit = bb_exact_rk(N, k, suffix_exact, seed_best, seed_wit)
        table[N] = (r, wit)
    return table


# ============================================================================
# Engine B: z3 SAT/UNSAT certificates
# ============================================================================

def z3_certificate(N, k, claimed):
    """Return (status, payload).
    CONFIRMED          : SAT at `claimed`, UNSAT at `claimed+1` (optimality)
    SAT_ABOVE_CLAIMED  : payload = z3's larger AP-free set (to be validated)
    UNSAT_AT_CLAIMED   : payload = None (claimed value infeasible per z3)
    ERROR              : payload = message
    """
    if not HAVE_Z3:
        return ("ERROR", "z3 not importable: %s" % Z3_ERR)
    xs = [z3.Bool("x_%d_%d_%d" % (N, k, i)) for i in range(1, N + 1)]
    aps = all_k_aps(N, k)

    def solver_at_least(v):
        s = z3.Solver()
        for ap in aps:
            s.add(z3.Not(z3.And([xs[t - 1] for t in ap])))
        s.add(z3.PbGe([(x, 1) for x in xs], v))
        return s

    lo = solver_at_least(claimed)
    if lo.check() != z3.sat:
        return ("UNSAT_AT_CLAIMED", None)
    hi = solver_at_least(claimed + 1)
    res = hi.check()
    if res == z3.unsat:
        return ("CONFIRMED", None)
    if res == z3.sat:
        m = hi.model()
        wit = [i + 1 for i in range(N)
               if z3.is_true(m.eval(xs[i], model_completion=True))]
        return ("SAT_ABOVE_CLAIMED", wit)
    return ("ERROR", "z3 check() returned %r at N=%d k=%d v=%d"
            % (res, N, k, claimed + 1))


def z3_engine_agreement(k, Nmax, table, claim):
    """Engine B dual: z3 must confirm every B&B value (SAT@r, UNSAT@r+1)."""
    ok_all = True
    for N in range(1, Nmax + 1):
        claimed = table[N][0]
        status, payload = z3_certificate(N, k, claimed)
        if status == "CONFIRMED":
            continue
        if status == "SAT_ABOVE_CLAIMED":
            wit = payload
            valid = (wit is not None
                     and len(wit) >= claimed + 1
                     and all(1 <= t <= N for t in wit)
                     and is_ap_free(wit, k))
            if valid:
                fail(claim,
                     "ENGINE DISAGREEMENT k=%d N=%d: z3 exhibits an AP-free "
                     "set of size %d > B&B value %d; witness=%s"
                     % (k, N, len(wit), claimed, wit))
            else:
                fail(claim,
                     "z3 model INVALID k=%d N=%d claimed=%d model=%s"
                     % (k, N, claimed, wit))
        else:
            fail(claim,
                 "z3 certificate trouble k=%d N=%d claimed=%d status=%s "
                 "payload=%s" % (k, N, claimed, status, payload))
        ok_all = False
    return ok_all


# ============================================================================
# Engine C: exhaustive brute force
# ============================================================================

def brute_rk(N, k):
    """Exhaustive 2^N scan; returns (best, witness)."""
    ap_masks = []
    for ap in all_k_aps(N, k):
        m = 0
        for t in ap:
            m |= 1 << (t - 1)
        ap_masks.append(m)
    best, bestmask = 0, 0
    for S in range(1 << N):
        ok = True
        for m in ap_masks:
            if (S & m) == m:
                ok = False
                break
        if ok:
            c = S.bit_count()
            if c > best:
                best, bestmask = c, S
    wit = [i + 1 for i in range(N) if (bestmask >> i) & 1]
    return best, wit


# ============================================================================
# Cantor set T_k (ternary digits in {0,1}) -- three digitizers
# ============================================================================

def cantor_T_methodA(k):
    """Digit-free: integer divmod scan over [0, 3^k)."""
    T = []
    for n in range(3 ** k):
        m = n
        ok = True
        while m:
            if m % 3 == 2:
                ok = False
                break
            m //= 3
        if ok:
            T.append(n)
    return T


def cantor_T_methodB(k):
    """Digit-list: cartesian product of {0,1}^k, value = sum d_i * 3^i."""
    vals = set()
    for digits in product((0, 1), repeat=k):
        v = 0
        for i, d in enumerate(digits):
            v += d * (3 ** i)
        vals.add(v)
    return sorted(vals)


def cantor_T_methodC(k):
    """gmpy2.digits(n, 3) base-3 string scan (third digitizer)."""
    if not HAVE_GMPY2:
        return None
    T = []
    for n in range(3 ** k):
        if '2' not in gmpy2.digits(n, 3):
            T.append(n)
    return T


def digits_of(n, k):
    """Base-3 digit tuple (little-endian, exactly k positions)."""
    ds = []
    for _ in range(k):
        ds.append(n % 3)
        n //= 3
    return tuple(ds)


def cantor_apfree_scan_A(T):
    """Integer method: for all x < z in T with (x+z) even, (x+z)//2 not in T."""
    Tset = set(T)
    tl = list(T)
    pairs = 0
    even_pairs = 0
    violations = []
    for i in range(len(tl)):
        x = tl[i]
        for j in range(i + 1, len(tl)):
            z = tl[j]
            s = x + z
            pairs += 1
            if s % 2 == 0:
                even_pairs += 1
                m = s // 2
                if m in Tset:
                    violations.append((x, m, z))
    return pairs, even_pairs, violations


def cantor_apfree_scan_B(T, k):
    """Digit-vector method: digit-decomposed pairs, digit-tuple membership,
    plus the no-carry digit-addition lemma (digits of x+z are the component-
    wise sums, each in {0,1,2})."""
    tup = {digits_of(n, k) for n in T}
    tl = sorted(T)
    pairs = 0
    even_pairs = 0
    violations = []
    nocarry_bad = []
    for xi in range(len(tl)):
        for zi in range(xi + 1, len(tl)):
            x, z = tl[xi], tl[zi]
            dx = digits_of(x, k)
            dz = digits_of(z, k)
            pairs += 1
            s = x + z
            ds = digits_of(s, k + 1)
            comp = tuple(dx[i] + dz[i] for i in range(k)) + (0,)
            if ds != comp:
                nocarry_bad.append((x, z, ds, comp))
            if s % 2 == 0:
                even_pairs += 1
                m = s // 2
                if digits_of(m, k) in tup:
                    violations.append((x, m, z))
    return pairs, even_pairs, violations, nocarry_bad


def complement_scan_method1(B, Nlim):
    """Pair-product dicts over B x B: for every u in [1,Nlim]\\B the minimal-d
    3-AP inside B + {u} containing u (u middle / first / last), or None."""
    Bset = set(B)
    Bl = sorted(B)
    best = {}
    n = len(Bl)
    for i in range(n):
        a = Bl[i]
        for j in range(i + 1, n):
            b = Bl[j]
            d0 = b - a
            if (a + b) % 2 == 0:
                u = (a + b) // 2
                if 1 <= u <= Nlim and u not in Bset:
                    d = d0 // 2
                    if u not in best or d < best[u][0]:
                        best[u] = (d, (a, u, b))
            u = 2 * a - b           # u as first term: (u, a, b)
            if 1 <= u and u not in Bset:
                if u not in best or d0 < best[u][0]:
                    best[u] = (d0, (u, a, b))
            w = 2 * b - a           # w as last term: (a, b, w)
            if w <= Nlim and w not in Bset:
                if w not in best or d0 < best[w][0]:
                    best[w] = (d0, (a, b, w))
    return best


def complement_scan_method2(B, Nlim):
    """Direct d-scan per u (independent of method 1)."""
    Bset = set(B)
    best = {}
    for u in range(1, Nlim + 1):
        if u in Bset:
            continue
        d = 1
        found = None
        while d <= Nlim:
            if (u - d >= 1 and u + d <= Nlim
                    and (u - d) in Bset and (u + d) in Bset):
                found = (d, (u - d, u, u + d))
                break
            if (u + 2 * d <= Nlim
                    and (u + d) in Bset and (u + 2 * d) in Bset):
                found = (d, (u, u + d, u + 2 * d))
                break
            if (u - 2 * d >= 1
                    and (u - d) in Bset and (u - 2 * d) in Bset):
                found = (d, (u - 2 * d, u - d, u))
                break
            d += 1
        if found is not None:
            best[u] = found
    return best


def valid_ap_triple(ap, u, Bset):
    """(x,y,z) is a genuine 3-AP containing u with the other two in B."""
    x, y, z = sorted(ap)
    if (y - x) == (z - y) and (y - x) >= 1 and u in (x, y, z):
        return all(t in Bset for t in (x, y, z) if t != u)
    return False


# ============================================================================
# MAIN BATTERY
# ============================================================================

def main():
    log("=" * 78)
    log("W67-142D DOUBTER MIRROR BATTERY -- Erdos #142 r_k(N) AP-free")
    log("convention: non-trivial k-AP = a, a+d, ..., a+(k-1)d, d >= 1")
    log("engines: A=B&B(AP-completion+suffix bounds)  B=z3(SAT/UNSAT certs)"
        "  C=brute(2^N, N<=12)")
    log("=" * 78)

    if not HAVE_Z3:
        log("FATAL: z3 is required (dual-method law); import failed: %s" % Z3_ERR)
        return 2
    log("env: z3 %s, gmpy2 %s" % (
        z3.get_version_string(),
        gmpy2.version() if HAVE_GMPY2 else ("MISSING (%s)" % GMPY2_ERR)))
    if not HAVE_GMPY2:
        note("gmpy2 unavailable: Cantor digitizer C skipped "
             "(dual methods A+B still run)")

    cert_lines = []
    artifact = {
        "problem": "Erdos-142 r_k(N) largest k-AP-free subset of {1..N}",
        "convention": "non-trivial k-AP: a, a+d, ..., a+(k-1)d with d >= 1",
        "task_id": "W67-142D",
        "engines": {
            "A": "branch-and-bound DFS, AP-completion propagation + exact "
                 "suffix bounds",
            "B": "z3 SAT@r + UNSAT@(r+1) certificates",
            "C": "exhaustive 2^N brute force for N <= %d" % BRUTE_NMAX,
        },
    }

    # ------------------------------------------------------------------ C1 --
    log("")
    log("---- C1: Cantor T_k (ternary digits {0,1}) 3-AP-freeness, "
        "dual method, k <= %d ----" % CANTOR_KMAX)
    c1_ok = True
    cert_lines.append("W67-142D CANTOR CERTIFICATION (dual method, k <= %d)"
                      % CANTOR_KMAX)
    cert_lines.append("=" * 60)
    cert_lines.append("T_k = {n in [0, 3^k) : every base-3 digit of n is in "
                      "{0,1}}; |T_k| = 2^k; max(T_k) = (3^k-1)/2.")
    cert_lines.append("Claim under audit (C1): T_k is 3-AP-free.")
    cert_lines.append("")
    cantor_sets = {}
    for k in range(1, CANTOR_KMAX + 1):
        A = cantor_T_methodA(k)
        B = cantor_T_methodB(k)
        C = cantor_T_methodC(k)
        if A != B:
            fail("C1", "digitizer disagreement k=%d: methodA != methodB" % k)
            c1_ok = False
        if C is not None and C != A:
            fail("C1", "digitizer disagreement k=%d: gmpy2 methodC != A" % k)
            c1_ok = False
        if len(A) != 2 ** k:
            fail("C1", "k=%d: |T_k| = %d != 2^k" % (k, len(A)))
            c1_ok = False
        if max(A) != (3 ** k - 1) // 2:
            fail("C1", "k=%d: max(T_k) = %d != (3^k-1)/2" % (k, max(A)))
            c1_ok = False
        pA, eA, vA = cantor_apfree_scan_A(A)
        pB, eB, vB, ncb = cantor_apfree_scan_B(B, k)
        if (pA, eA) != (pB, eB):
            fail("C1", "k=%d: dual scan disagreement (pairs/even) "
                 "A=(%d,%d) B=(%d,%d)" % (k, pA, eA, pB, eB))
            c1_ok = False
        if vA or vB:
            fail("C1", "k=%d: 3-AP VIOLATION inside T_k: %s"
                 % (k, (vA or vB)[:5]))
            c1_ok = False
        if ncb:
            fail("C1", "k=%d: no-carry digit lemma failed for %d pairs"
                 % (k, len(ncb)))
            c1_ok = False
        cert_lines.append(
            "k=%d: |T_k|=%d (2^k ok), max=%d ((3^k-1)/2 ok), "
            "digitizers A/B%s identical, pair-scan=%d pairs (%d even-sum), "
            "3-AP violations=0, no-carry lemma=OK"
            % (k, len(A), max(A), "/C" if C is not None else "",
               pA, eA))
        cantor_sets[k] = A
        log("  k=%d: |T_k|=%d max=%d pairs=%d even=%d violations=%d "
            "nocarry_bad=%d" % (k, len(A), max(A), pA, eA,
                                len(vA) + len(vB), len(ncb)))
    cert_lines.append("")
    log("  %s C1 dual scans complete" % elapsed())

    # ------------------------------------------------- C1 complement scan --
    log("")
    log("---- C1-complement (sanity intel, not a kill-claim): for every u in "
        "[1,6560] \\ T_8, the minimal-d 3-AP inside (T_8\\{0}) + {u} ----")
    T8 = cantor_sets[CANTOR_KMAX]
    Nlim = 3 ** CANTOR_KMAX - 1
    base = [t for t in T8 if 1 <= t <= Nlim]      # T_8 minus {0}: 255 elems
    cert_lines.append("Complement scan (niche maximality sanity): base B = "
                      "T_8 \\ {0} inside [1, %d], |B| = %d." % (Nlim, len(base)))
    if len(base) != 2 ** CANTOR_KMAX - 1:
        fail("C1", "|T_8 \\ {0}| = %d != 2^8 - 1" % len(base))
        c1_ok = False
    m1 = complement_scan_method1(base, Nlim)
    t_m2 = time.time()
    m2 = complement_scan_method2(base, Nlim)
    log("  method1(pair-product): %d blocked; method2(direct d-scan): "
        "%d blocked [%0.1fs]" % (len(m1), len(m2), time.time() - t_m2))
    Bset = set(base)
    unblocked = [u for u in range(1, Nlim + 1)
                 if u not in Bset and u not in m1]
    if set(m1.keys()) != set(m2.keys()):
        fail("C1", "complement scan disagreement: method1/2 blocked sets "
             "differ (sym diff %s)"
             % sorted(set(m1.keys()) ^ set(m2.keys()))[:20])
        c1_ok = False
    d_mismatch = [u for u in m1
                  if u in m2 and m1[u][0] != m2[u][0]]
    if d_mismatch:
        fail("C1", "complement scan minimal-d disagreement at u=%s"
             % d_mismatch[:20])
        c1_ok = False
    bad_ap = []
    for u, (d, ap) in m1.items():
        if not valid_ap_triple(ap, u, Bset):
            bad_ap.append((u, d, ap))
    for u, (d, ap) in m2.items():
        if not valid_ap_triple(ap, u, Bset):
            bad_ap.append(("m2", u, d, ap))
    if bad_ap:
        fail("C1", "complement scan produced invalid APs: %s" % bad_ap[:5])
        c1_ok = False
    n_outside = Nlim - len(base)
    if unblocked:
        note("T_8\\{0} is NOT maximal in [1,%d]: %d of %d non-members cannot "
             "be blocked (0 is needed for their APs): %s"
             % (Nlim, len(unblocked), n_outside, unblocked[:20]))
    else:
        note("T_8\\{0} IS maximal in [1,%d]: all %d non-members are blocked "
             "by a 3-AP over the base" % (Nlim, n_outside))
    cert_lines.append("Blocked (a 3-AP through the base appears when u is "
                      "added): %d / %d non-members; dual-method agreement: "
                      "identical blocked sets + identical minimal d."
                      % (len(m1), n_outside))
    if unblocked:
        cert_lines.append("Unblocked non-members (niche non-maximality, "
                          "intel only): %s" % unblocked)
    maxd_u = max(m1.items(), key=lambda kv: kv[1][0]) if m1 else None
    hist = {}
    for u, (d, ap) in m1.items():
        hist[d] = hist.get(d, 0) + 1
    cert_lines.append("Minimal blocking difference d: min=%s, max=%s "
                      "(at u=%s), distinct d values=%d"
                      % (min(hist) if hist else None,
                         maxd_u[1][0] if maxd_u else None,
                         maxd_u[0] if maxd_u else None,
                         len(hist)))
    cert_lines.append("Example first APs: %s"
                      % [(u, m1[u][1]) for u in sorted(m1)[:5]])
    cert_lines.append("Largest-d example: u=%d -> AP %s"
                      % (maxd_u[0], maxd_u[1][1]) if maxd_u else "")
    log("  complement: blocked=%d/%d unblocked=%d max minimal-d=%s"
        % (len(m1), n_outside, len(unblocked),
           maxd_u[1][0] if maxd_u else None))

    # ------------------------------------------------------------- tables --
    log("")
    log("---- Exact r_k tables: Engine A (B&B) ----")
    tables = {}
    for k, Nmax in ((3, R3_NMAX), (4, R4_NMAX), (5, R5_NMAX), (2, R2_NMAX)):
        t_start = time.time()
        tables[k] = build_exact_table(k, Nmax)
        log("  r_%d table N<=%d built in %0.1fs: %s"
            % (k, Nmax, time.time() - t_start,
               [tables[k][N][0] for N in range(1, Nmax + 1)]))

    # witness validation + monotonicity (Engine A self-audit)
    log("")
    log("---- Witness validation + monotonicity (independent validator) ----")
    val_ok = True
    for k, Nmax in ((3, R3_NMAX), (4, R4_NMAX), (5, R5_NMAX), (2, R2_NMAX)):
        tab = tables[k]
        for N in range(1, Nmax + 1):
            r, wit = tab[N]
            if len(wit) != r or not all(1 <= t <= N for t in wit) \
                    or not is_ap_free(wit, k):
                fail("C5", "witness invalid k=%d N=%d r=%d wit=%s"
                     % (k, N, r, wit))
                val_ok = False
            if N > 1 and tab[N][0] < tab[N - 1][0]:
                fail("C5", "monotonicity violated k=%d: r(%d)=%d < r(%d)=%d"
                     % (k, N, tab[N][0], N - 1, tab[N - 1][0]))
                val_ok = False
    log("  all witnesses validated: %s" % ("OK" if val_ok else "BROKEN"))

    # Engine C brute cross-check (N <= 12, 100% agreement required)
    log("")
    log("---- Engine C: brute force cross-check (N <= %d, 100%% agreement) "
        "----" % BRUTE_NMAX)
    brute_ok = True
    for k, Nmax in ((3, R3_NMAX), (4, R4_NMAX), (5, R5_NMAX), (2, R2_NMAX)):
        for N in range(1, min(Nmax, BRUTE_NMAX) + 1):
            b, wit = brute_rk(N, k)
            if b != tables[k][N][0]:
                fail("C5", "BRUTE DISAGREEMENT k=%d N=%d: brute=%d B&B=%d"
                     % (k, N, b, tables[k][N][0]))
                brute_ok = False
            elif not is_ap_free(wit, k) or len(wit) != b:
                fail("C5", "brute witness invalid k=%d N=%d" % (k, N))
                brute_ok = False
    log("  brute cross-check: %s" % ("100% AGREEMENT" if brute_ok
                                      else "BROKEN"))

    log("")
    log("---- AP-census dual check ((a,d)-driven vs endpoint-driven) ----")
    census_ok = True
    for k, Nmax in ((3, R3_NMAX), (4, R4_NMAX), (5, R5_NMAX), (2, R2_NMAX)):
        for N in range(1, Nmax + 1):
            if set(all_k_aps(N, k)) != all_k_aps_endpoint_method(N, k):
                fail("C5", "AP census dual disagreement k=%d N=%d" % (k, N))
                census_ok = False
    log("  AP census (all audited N,k): %s"
        % ("identical (both methods)" if census_ok else "BROKEN"))

    # Engine B z3 dual certificates
    log("")
    log("---- Engine B: z3 SAT/UNSAT dual certificates ----")
    z3_ok = True
    for k, Nmax in ((3, R3_NMAX), (4, R4_NMAX), (5, R5_NMAX), (2, R2_NMAX)):
        t_start = time.time()
        okk = z3_engine_agreement(k, Nmax, tables[k], "C5")
        z3_ok = z3_ok and okk
        log("  r_%d (N<=%d): z3 %s [%0.1fs]"
            % (k, Nmax, "ALL CONFIRMED (SAT@r + UNSAT@r+1)" if okk
               else "DISAGREEMENT", time.time() - t_start))
    log("  %s z3 dual engine complete" % elapsed())

    r3tab = tables[3]
    r4tab = tables[4]
    r5tab = tables[5]
    r2tab = tables[2]

    # ------------------------------------------------------------------ C2 --
    log("")
    log("---- C2: Cantor lower bound r_3(3^k - 1) >= 2^k - 1 (k <= 3) "
        "+ gap analysis ----")
    c2_ok = True
    gap_rows = []
    for kk in (1, 2, 3):
        N = 3 ** kk - 1
        cantor_wit = [t for t in cantor_sets[kk] if 1 <= t <= N]
        cw_ok = (len(cantor_wit) == 2 ** kk - 1
                 and all(1 <= t <= N for t in cantor_wit)
                 and is_ap_free(cantor_wit, 3))
        true_r = r3tab[N][0]
        if not cw_ok:
            fail("C2", "k=%d: Cantor witness T_k\\{0} invalid in [1,%d]"
                 % (kk, N))
            c2_ok = False
        if true_r < 2 ** kk - 1:
            fail("C2", "k=%d: exact r_3(%d) = %d < 2^k - 1 = %d "
                 "(Cantor bound BROKEN)" % (kk, N, true_r, 2 ** kk - 1))
            c2_ok = False
        ratio = Fraction(true_r, 2 ** kk - 1)
        gap_rows.append({
            "k": kk, "N": N, "cantor_lower_bound": 2 ** kk - 1,
            "true_r3": true_r, "gap_true_over_cantor": "%d/%d"
            % (ratio.numerator, ratio.denominator),
            "gap_decimal_intel": float(ratio),
        })
        log("  k=%d: N=%d, Cantor=%d, TRUE r_3(N)=%d, gap=true/cantor=%s "
            "(~%.4f intel)" % (kk, N, 2 ** kk - 1, true_r, ratio, float(ratio)))
    artifact["cantor_gap"] = gap_rows
    cert_lines.append("")
    cert_lines.append("Gap analysis (true r_3(3^k - 1) vs Cantor 2^k - 1):")
    for row in gap_rows:
        cert_lines.append(
            "  k=%d: N=%d cantor=%d true=%d ratio=%s (~%.4f)"
            % (row["k"], row["N"], row["cantor_lower_bound"], row["true_r3"],
               row["gap_true_over_cantor"], row["gap_decimal_intel"]))
    log("  %s C2 certified" % elapsed())

    # ------------------------------------------------------------------ C3 --
    log("")
    log("---- C3: block bound r_k(N) <= (k-1)*floor(N/k) + (N mod k) "
        "domination audit ----")
    c3_ok = True
    margins = {}
    for k, Nmax, tab in ((3, R3_NMAX, r3tab), (4, R4_NMAX, r4tab),
                         (5, R5_NMAX, r5tab), (2, R2_NMAX, r2tab)):
        rows = []
        for N in range(1, Nmax + 1):
            bb = block_bound(N, k)
            ex = tab[N][0]
            if ex > bb:
                fail("C3", "k=%d N=%d: exact r_k = %d > block bound %d "
                     "(killer lemma BROKEN -- reproduce: witness %s)"
                     % (k, N, ex, bb, tab[N][1]))
                c3_ok = False
            rows.append({"N": N, "block_bound": bb, "exact": ex,
                         "margin": bb - ex})
        margins["k%d" % k] = rows
    tight = [(k, r["N"]) for k in (3, 4, 5) for r in margins["k%d" % k]
             if r["margin"] == 0]
    log("  domination: %s; block bound TIGHT (margin 0) at %d points, "
        "e.g. %s"
        % ("OK (all exact values <= block bound)" if c3_ok else "BROKEN",
           len(tight), tight[:12]))
    artifact["block_bound_margins"] = margins
    artifact["block_bound_tight_points"] = [
        {"k": k, "N": N} for (k, N) in tight]
    ratios = [{"N": N,
               "exact_fraction_r3_times_3_over_2N": "%d/%d"
               % (r3tab[N][0] * 3, 2 * N),
               "decimal_intel": float(Fraction(r3tab[N][0] * 3, 2 * N))}
              for N in range(1, R3_NMAX + 1)]
    artifact["ratio_r3_3_over_2N"] = ratios
    log("  honest ratio r_3(N)*3/(2N): N=5 -> %s, N=30 -> %s"
        % (ratios[4]["exact_fraction_r3_times_3_over_2N"],
           ratios[29]["exact_fraction_r3_times_3_over_2N"]))

    # ------------------------------------------------------------------ C4 --
    log("")
    log("---- C4: r_2(N) = 1 for N >= 2 (d >= 1 convention) ----")
    c4_ok = True
    for N in range(2, R2_NMAX + 1):
        if r2tab[N][0] != 1:
            fail("C4", "r_2(%d) = %d != 1" % (N, r2tab[N][0]))
            c4_ok = False
    if r2tab[1][0] != 1:
        fail("C4", "r_2(1) = %d != 1 (trivial anchor)" % r2tab[1][0])
        c4_ok = False
    log("  r_2(N) = 1 for all 2 <= N <= %d: %s" % (R2_NMAX, "OK" if c4_ok
                                                    else "BROKEN"))
    log("  convention pin (kernel header MUST pin d >= 1): under d >= 1 any "
        "2 distinct elements {a, a+d} form a 2-AP, so r_2(N) = 1 for N >= 2; "
        "under the alternative 'non-trivial means k >= 3' convention the r_2 "
        "claim is void.")
    log("  %s C4 certified" % elapsed())

    # ------------------------------------------------------------------ C5 --
    log("")
    log("---- C5: exact r_3(N) table (N <= %d) ----" % R3_NMAX)
    seq = [r3tab[N][0] for N in range(1, R3_NMAX + 1)]
    log("  r_3 = %s" % seq)
    for N in range(1, R3_NMAX + 1):
        log("    N=%2d r_3=%2d witness=%s" % (N, r3tab[N][0], r3tab[N][1]))

    # OEIS-printed reference comparison (intel; own computation is truth)
    OEIS_PRINTED = [1, 2, 2, 3, 4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 7, 8,
                    8, 8, 8, 9]
    mism = []
    for i, pv in enumerate(OEIS_PRINTED):
        N = i + 1
        if seq[i] != pv:
            mism.append({"N": N, "printed": pv, "computed": seq[i],
                         "witness": r3tab[N][1]})
    if mism:
        note("OEIS-printed reference string (as given in MISSION.md) "
             "DEVIATES from the dual-engine-certified truth at %s -- "
             "our computation is the truth (mission law); witnesses above"
             % [m["N"] for m in mism])
        for m in mism:
            log("    MISMATCH N=%d: printed %d, certified %d, witness %s"
                % (m["N"], m["printed"], m["computed"], m["witness"]))
    else:
        note("OEIS-printed reference string agrees with the certified table "
             "on all %d printed values" % len(OEIS_PRINTED))
    artifact["oeis_printed_reference"] = OEIS_PRINTED
    artifact["oeis_printed_mismatches"] = mism

    # ---------------------------------------------------------- artifacts --
    artifact["r3_table"] = [{"N": N, "r3": r3tab[N][0],
                             "witness": r3tab[N][1]}
                            for N in range(1, R3_NMAX + 1)]
    artifact["r4_table"] = [{"N": N, "r4": r4tab[N][0],
                             "witness": r4tab[N][1]}
                            for N in range(1, R4_NMAX + 1)]
    artifact["r5_table"] = [{"N": N, "r5": r5tab[N][0],
                             "witness": r5tab[N][1]}
                            for N in range(1, R5_NMAX + 1)]
    artifact["r2_table"] = [{"N": N, "r2": r2tab[N][0],
                             "witness": r2tab[N][1]}
                            for N in range(1, R2_NMAX + 1)]
    artifact["dual_engine_agreement"] = {
        "A_vs_B_z3": z3_ok, "A_vs_C_brute_N_le_%d" % BRUTE_NMAX: brute_ok,
        "witness_validation": val_ok, "ap_census_dual": census_ok}

    status = "BROKEN" if FAILURES else "GREEN"
    artifact["battery_status"] = status
    artifact["failures"] = FAILURES
    (ART / "r3_exact_table.json").write_text(
        json.dumps(artifact, indent=1) + "\n")

    cert_lines.append("")
    cert_lines.append("C1 verdict: %s"
                      % ("CERTIFIED (dual method, k <= %d, zero violations)"
                         % CANTOR_KMAX if c1_ok else "BROKEN"))
    cert_lines.append("C2 verdict: %s"
                      % ("CERTIFIED (r_3(3^k-1) >= 2^k-1 for k <= 3, exact "
                         "B&B+z3)" if c2_ok else "BROKEN"))
    cert_lines.append("C3 verdict: %s"
                      % ("CERTIFIED (block bound dominates every exact value "
                         "in audited ranges)" if c3_ok else "BROKEN"))
    cert_lines.append("C4 verdict: %s"
                      % ("CERTIFIED (r_2(N)=1 for N >= 2 under d >= 1; "
                         "kernel must pin d >= 1)" if c4_ok else "BROKEN"))
    cert_lines.append("C5 verdict: %s"
                      % ("CERTIFIED (engines A/B/C agree; AP census dual; "
                         "witnesses valid)"
                         if (val_ok and brute_ok and z3_ok and census_ok)
                         else "BROKEN"))
    cert_lines.append("Battery status: %s" % status)
    (ART / "cantor_cert.txt").write_text("\n".join(cert_lines) + "\n")

    # ------------------------------------------------------------- verdict --
    log("")
    log("=" * 78)
    log("VERDICT SUMMARY (W67-142D doubter lane, Erdos #142)")
    log("  C1 Cantor T 3-AP-free (dual method, k<=%d):      %s"
        % (CANTOR_KMAX, "CERTIFIED" if c1_ok else "BROKEN"))
    log("  C2 r_3(3^k-1) >= 2^k-1 (k<=3, exact table):     %s"
        % ("CERTIFIED" if c2_ok else "BROKEN"))
    log("  C3 block bound domination (k=3 N<=30, k=4/5 "
        "N<=20):           %s" % ("CERTIFIED" if c3_ok else "BROKEN"))
    log("  C4 r_2(N)=1 for N>=2 (d>=1 convention):         %s"
        % ("CERTIFIED" if c4_ok else "BROKEN"))
    log("  C5 exact r_3 table N<=30 (A/B/C engines):       %s"
        % ("CERTIFIED" if (val_ok and brute_ok and z3_ok and census_ok)
           else "BROKEN"))
    for m in mism:
        log("  INTEL: printed-reference mismatch at N=%d: printed %d vs "
            "certified %d (witness %s)"
            % (m["N"], m["printed"], m["computed"], m["witness"]))
    for n in NOTES:
        log("  INTEL: %s" % n)
    if FAILURES:
        log("BATTERY_VERDICT: BROKEN")
        for f in FAILURES:
            log("  FAILURE: %s" % f)
        return 1
    log("BATTERY_VERDICT: GREEN")
    log("E142_DOUBTER_BATTERY_GREEN")
    log("total battery time: %0.1fs" % (time.time() - T0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
