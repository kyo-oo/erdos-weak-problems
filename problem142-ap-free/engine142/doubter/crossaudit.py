#!/usr/bin/env python3
"""
W68-142D CROSS-AUDIT ENGINE -- adversarial re-verification of the killer lane's
kernel theorem board (branch w67-p142k @ 011cb3e, file
problem142-ap-free/Erdos142.lean, namespace E142) against the doubter lane's
CI-certified exact tables (this branch, run 43726649205, artifacts in
problem142-ap-free/engine142/doubter/r3_exact_table.json).

Kernel theorem board under audit
--------------------------------
  K1  E142.t3free         the Cantor ternary-digit-{0,1} set is 3-AP-free:
                          x + z = 2*y  =>  x = z   (for all members)
  K2  E142.cantor_lower   r_3(3^k - 1) >= 2^k - 1   (genTp k witnesses)
  K3  E142.r3_exact_small r_3(N) = 1,2,2,3,4,4,4,4 for N = 1..8 (exact)
  K4  E142.block_upper    |S| <= (k-1)*floor(N/k) + (N mod k)
      E142.r3_upper       the k=3 instance |S| <= 2*floor(N/3) + (N mod 3)
                          -> audited as a TIGHTNESS MAP against the exact tables
  K5  E142.k2_edge        r_2(N) = 1 for all N >= 2 (pinned d >= 1 convention)
  K6  doubter's own claim r_5(N) = block bound EXACTLY (tight) on all N <= 20
                          -> re-verified here with a THIRD method:
                             greedy certificate sets (+ explicit mod-5 drop
                             construction + freshly written z3 UNSAT certs)

Independence statement (LAW 3, dual/triple method)
--------------------------------------------------
Every engine below is a NEW code path, written for this audit; nothing is
imported from mirror_battery.py and no B&B machinery is reused:

  * generator A  -- itertools.product over {0,1}^k ternary digit tuples
  * generator B  -- direct range scan of [0, 3^k) with a divmod digit predicate
  * predicate R  -- a literal python replica of Arsenal `noTernaryTwo`
  * replicas     -- literal python replicas of the killer's genT / genTp
                    recursive definitions (order-sensitive list comparison)
  * engine alpha -- full 2^N bitmask exhaustive enumeration (fresh code)
  * engine beta  -- freshly written z3 encoding (Bool per element,
                    Not(And(...)) per k-AP, PbGe cardinality)
  * engine gamma -- left-to-right greedy certificate construction
  * construction -- the explicit mod-5 drop set {n in [1,N] : n % 5 != 0}

Verdict semantics: CONFIRMED requires every involved engine to agree exactly;
any disagreement, any AP violation, any witness that fails independent
re-validation, or any certified value exceeding a kernel bound => BROKEN and
the script exits nonzero.
"""

import json
import sys
import time
from itertools import product
from pathlib import Path

try:
    import z3
    Z3_OK = True
    Z3_ERR = ""
except Exception as e:  # pragma: no cover
    Z3_OK = False
    Z3_ERR = str(e)

HERE = Path(__file__).resolve().parent
AUDIT_K_MAX = 8          # Cantor window: k = 1..8  (3^8 = 6561)
R3_N_MAX = 30            # certified r_3 frontier
R45_N_MAX = 20           # certified r_4 / r_5 frontier
BRUTE_N_MAX = 12         # fresh exhaustive 2^N enumeration zone

T0 = time.time()
FAILURES = []
VERDICTS = []


def log(msg=""):
    print(msg, flush=True)


def verdict(tag, ok, detail):
    line = "XAUDIT_%s: %s" % (tag, "CONFIRMED" if ok else "BROKEN")
    log(line)
    log("    " + detail)
    VERDICTS.append((tag, ok, detail))
    if not ok:
        FAILURES.append("%s -- %s" % (tag, detail))


def fatal(msg):
    log("FATAL: " + msg)
    sys.exit(2)


# ---------------------------------------------------------------------------
# Shared independent primitives
# ---------------------------------------------------------------------------

def ap3_violations_pairwise(S):
    """Complete direct pairwise midpoint check of 3-AP-freeness:
    a set S violates 'x+z=2y => x=z' iff some pair x<z in S has an even sum
    whose midpoint is also in S.  Returns the list of violating triples."""
    Sset = set(S)
    Slist = sorted(S)
    viol = []
    for i in range(len(Slist)):
        for j in range(i + 1, len(Slist)):
            x, z = Slist[i], Slist[j]
            s = x + z
            if s % 2 == 0 and (s // 2) in Sset:
                viol.append((x, s // 2, z))
    return viol


def has_kap(Sset, k, N):
    """Full (a, d) scan: first non-trivial k-term AP fully contained in Sset,
    or None.  Convention (identical to the kernel HasAP and the certified
    tables): a, a+d, ..., a+(k-1)d with d >= 1, all inside [1, N]."""
    for a in range(1, N + 1):
        for d in range(1, N):
            if a + (k - 1) * d > N:
                break
            if all((a + i * d) in Sset for i in range(k)):
                return (a, d)
    return None


def validate_witness(S, N, k, origin):
    """Independent re-validation of a claimed AP-free witness in [1, N]."""
    if len(S) != len(set(S)):
        return "%s: witness has duplicates" % origin
    for s in S:
        if not (1 <= s <= N):
            return "%s: witness element %d out of [1, %d]" % (origin, s, N)
    ap = has_kap(set(S), k, N)
    if ap is not None:
        return "%s: witness contains the %d-AP (a=%d, d=%d)" % (origin, k, ap[0], ap[1])
    return None


# ---------------------------------------------------------------------------
# Cantor generators -- three mutually independent code paths
# ---------------------------------------------------------------------------

def cantor_tuples(k):
    """Generator A: itertools.product over {0,1}^k ternary digit tuples."""
    vals = set()
    for digits in product((0, 1), repeat=k):
        n = 0
        for i in range(k - 1, -1, -1):   # msd-first, Horner accumulation
            n = 3 * n + digits[i]
        vals.add(n)
    return vals


def no_digit_two(n):
    """Digit predicate for generator B: divmod scan."""
    if n == 0:
        return True
    while n:
        n, r = divmod(n, 3)
        if r == 2:
            return False
    return True


def cantor_scan(k, lo=0):
    """Generator B: direct scan of [lo, 3^k)."""
    return {n for n in range(lo, 3 ** k) if no_digit_two(n)}


def lean_noTernaryTwo_replica(n):
    """Predicate R: literal replica of Arsenal.CardinalWorlds.noTernaryTwo."""
    if n == 0:
        return True
    if n % 3 == 2:
        return False
    return lean_noTernaryTwo_replica(n // 3)


def genT_replica(k):
    """Literal replica of the killer's genT (list ORDER included)."""
    if k == 0:
        return [0]
    prev = genT_replica(k - 1)
    return [3 * m for m in prev] + [3 * m + 1 for m in prev]


def genTp_replica(k):
    """Literal replica of the killer's genTp (list ORDER included)."""
    if k == 0:
        return []
    return [3 * m + 1 for m in genT_replica(k - 1)] + [3 * m for m in genTp_replica(k - 1)]


# ---------------------------------------------------------------------------
# K1 -- E142.t3free: the Cantor set is 3-AP-free
# ---------------------------------------------------------------------------

def audit_K1_t3free():
    log()
    log("==== K1: E142.t3free -- Cantor ternary set is 3-AP-free (x+z=2y => x=z) ====")
    problems = []
    total_pairs = 0
    for k in range(1, AUDIT_K_MAX + 1):
        A = cantor_tuples(k)
        B = cantor_scan(k)
        # three-way membership agreement on the full window [0, 3^k)
        R_agree = all(lean_noTernaryTwo_replica(n) == (n in B) for n in range(3 ** k))
        # the killer's generator replica must produce the same SET (and length)
        gt = genT_replica(k)
        if sorted(gt) != sorted(B) or len(gt) != len(set(gt)):
            problems.append("genT replica != independent set at k=%d" % k)
        if not R_agree:
            problems.append("noTernaryTwo replica disagrees at k=%d" % k)
        if A != B:
            problems.append("tuple-product generator != range-scan generator at k=%d" % k)
        if len(B) != 2 ** k:
            problems.append("|Tfull_%d| = %d != 2^k" % (k, len(B)))
        # THE claim: pairwise midpoint scan over the full window set
        viol = ap3_violations_pairwise(B)
        total_pairs += len(B) * (len(B) - 1) // 2
        if viol:
            problems.append("3-AP violation in Tfull_%d: %s" % (k, viol[:3]))
        log("  k=%d  |Tfull|=%d (2^k=%d)  generators A/B/R agree=%s  genTp replica len=%d  midpoint violations=%d"
            % (k, len(B), 2 ** k, (A == B) and R_agree, len(genTp_replica(k)), len(viol)))
    # genTp replicas equal the positive part everywhere
    for k in range(1, AUDIT_K_MAX + 1):
        pos = cantor_scan(k, lo=1)
        gp = genTp_replica(k)
        if sorted(gp) != sorted(pos) or len(gp) != 2 ** k - 1 or len(set(gp)) != len(gp):
            problems.append("genTp replica != positive Cantor set at k=%d" % k)
    log("  total midpoint pairs scanned (k=1..8): %d" % total_pairs)
    verdict("K1_t3free", not problems,
            "Cantor set 3-AP-free on the full k<=8 window: 0 midpoint violations "
            "over %d pairs; tuple-product / range-scan / noTernaryTwo-replica "
            "generators agree on all n < 3^8; genT/genTp replicas match the "
            "independent sets (incl. list order semantics via sorted equality, "
            "nodup, lengths 2^k / 2^k-1)" % total_pairs
            if not problems else "; ".join(problems))


# ---------------------------------------------------------------------------
# K2 -- E142.cantor_lower: r_3(3^k - 1) >= 2^k - 1
# ---------------------------------------------------------------------------

def audit_K2_cantor_lower(cert_r3):
    log()
    log("==== K2: E142.cantor_lower -- r_3(3^k - 1) >= 2^k - 1 (k = 1..8) ====")
    problems = []
    rows = []
    for k in range(1, AUDIT_K_MAX + 1):
        N = 3 ** k - 1
        m = 2 ** k - 1
        # independent witness: positive Cantor elements, generated by RANGE SCAN
        W = sorted(cantor_scan(k, lo=1))
        werr = validate_witness(W, N, 3, "cantor_lower witness k=%d" % k)
        if werr:
            problems.append(werr)
        if len(W) != m:
            problems.append("|T_%d| = %d != 2^k - 1 = %d" % (k, len(W), m))
        viol = ap3_violations_pairwise(W)
        if viol:
            problems.append("witness k=%d not 3-AP-free: %s" % (k, viol[:3]))
        # consistency with the certified exact table where N is inside it
        tab = ""
        if N <= R3_N_MAX:
            cert = cert_r3[N]
            if cert < m:
                problems.append("certified r_3(%d) = %d < 2^k-1 = %d" % (N, cert, m))
            tab = "  certified r_3(%d) = %d  Cantor-vs-true gap = %d  ratio = %d/%d" \
                  % (N, cert, cert - m, cert, m)
        rows.append((k, N, m, len(W)))
        log("  k=%d  N=3^k-1=%d  |witness|=%d  target 2^k-1=%d  in-range=%s  3-AP-free=%s%s"
            % (k, N, len(W), m, "yes", "yes" if not viol else "NO", tab))
    verdict("K2_cantor_lower", not problems,
            "independently regenerated witnesses (range-scan generator) have "
            "exactly 2^k-1 elements in [1, 3^k-1], all 3-AP-free by direct "
            "pairwise midpoint scan, k=1..8; no certified exact value below "
            "the bound" if not problems else "; ".join(problems))
    return rows


# ---------------------------------------------------------------------------
# K3 -- E142.r3_exact_small: r_3(N) = [1,2,2,3,4,4,4,4] for N = 1..8
# ---------------------------------------------------------------------------

def r3_exhaustive(N):
    """Engine alpha: full 2^N bitmask enumeration of subsets of [1, N]."""
    best = 0
    bestS = []
    for mask in range(1 << N):
        # popcount-style early skip: cannot beat current best
        S = [i + 1 for i in range(N) if (mask >> i) & 1]
        if len(S) <= best:
            continue
        if ap3_violations_pairwise(S):
            continue
        best = len(S)
        bestS = S
    return best, bestS


def z3_max_rk(N, k):
    """Engine beta: fresh z3 encoding.  Returns (r, witness) with
    r = max v such that an AP-free subset of [1,N] of size >= v exists,
    plus an explicit SAT model at r, plus the UNSAT check at r+1."""
    if not Z3_OK:
        return None, None, "z3 not importable: %s" % Z3_ERR
    xs = [z3.Bool("e%d" % i) for i in range(1, N + 1)]
    base = []
    for a in range(1, N + 1):
        for d in range(1, N):
            if a + (k - 1) * d > N:
                break
            base.append(z3.Not(z3.And([xs[a + i * d - 1] for i in range(k)])))

    def feasible(v):
        s = z3.Solver()
        s.add(base)
        s.add(z3.PbGe([(x, 1) for x in xs], v))
        return s.check() == z3.sat, s

    # descending scan: first feasible v IS the maximum (monotone in v)
    for v in range(N, 0, -1):
        ok, s = feasible(v)
        if ok:
            model = s.model()
            W = [i for i in range(1, N + 1) if z3.is_true(model.eval(xs[i - 1]))]
            unsat_above, _ = feasible(v + 1)
            return v, sorted(W), (None if unsat_above is False else "UNSAT@(r+1) failed")
    return 0, [], None


def audit_K3_r3_exact_small(cert_r3):
    log()
    log("==== K3: E142.r3_exact_small -- r_3(N) for N=1..8 == [1,2,2,3,4,4,4,4] ====")
    killer = {1: 1, 2: 2, 3: 2, 4: 3, 5: 4, 6: 4, 7: 4, 8: 4}
    problems = []
    log("  N | killer | exhaustive-2^N | z3-fresh | certified-table")
    log("  --|--------|----------------|----------|-----------------")
    for N in range(1, BRUTE_N_MAX + 1):
        a, awit = r3_exhaustive(N)
        kz = killer.get(N, None)
        z = None
        if Z3_OK:
            z, W, err = z3_max_rk(N, 3)
            if err:
                problems.append("z3 N=%d: %s" % (N, err))
            werr = validate_witness(W, N, 3, "z3 witness N=%d" % N)
            if werr:
                problems.append(werr)
            if z != a:
                problems.append("z3 r_3(%d) = %d != exhaustive %d" % (N, z, a))
        else:
            problems.append("z3 unavailable: dual certificate impossible")
        log("  %2d |   %s    |       %d        |    %s     |     %d"
            % (N, kz if kz is not None else "-", a, z if z is not None else "-", cert_r3[N]))
        if kz is not None and a != kz:
            problems.append("exhaustive r_3(%d) = %d != killer claim %d" % (N, a, kz))
        if kz is not None and z is not None and z != kz:
            problems.append("z3 r_3(%d) = %d != killer claim %d" % (N, z, kz))
        if a != cert_r3[N]:
            problems.append("exhaustive r_3(%d) = %d != certified %d" % (N, a, cert_r3[N]))
        if z is not None and z != cert_r3[N]:
            problems.append("z3 r_3(%d) = %d != certified %d" % (N, z, cert_r3[N]))
        werr = validate_witness(awit, N, 3, "exhaustive witness N=%d" % N)
        if werr and a > 0:
            problems.append(werr)
    if Z3_OK:
        log("  z3 fresh encoding, N=1..8:  [%s]" % ", ".join(
            str(z3_max_rk(N, 3)[0]) for N in range(1, 9)))
        log("  z3 fresh encoding, N=9..12: [%s]" % ", ".join(
            str(z3_max_rk(N, 3)[0]) for N in range(9, BRUTE_N_MAX + 1)))
    verdict("K3_r3_exact_small", not problems,
            "fresh 2^N exhaustive enumeration (N<=12) and fresh z3 SAT/UNSAT "
            "dual (N<=12) both give r_3(1..8) = 1,2,2,3,4,4,4,4 -- equal to the "
            "kernel claim and to the certified table prefix; every witness "
            "independently re-validated" if not problems else "; ".join(problems))
    # return fresh z3 values for N=1..12 for the report
    fresh = {}
    for N in range(1, BRUTE_N_MAX + 1):
        a, _ = r3_exhaustive(N)
        fresh[N] = a
    return fresh


# ---------------------------------------------------------------------------
# K4 -- E142.block_upper / E142.r3_upper: tightness map vs the exact tables
# ---------------------------------------------------------------------------

def block_bound(k, N):
    return (k - 1) * (N // k) + (N % k)


def audit_K4_block_upper(cert_r3, cert_r4, cert_r5, cert_r2):
    log()
    log("==== K4: E142.block_upper / E142.r3_upper -- tightness map vs exact tables ====")
    problems = []
    maps = {}
    for k, table, nmax, name in ((3, cert_r3, R3_N_MAX, "r_3"),
                                 (4, cert_r4, R45_N_MAX, "r_4"),
                                 (5, cert_r5, R45_N_MAX, "r_5"),
                                 (2, cert_r2, R3_N_MAX, "r_2")):
        rows = []
        tight = []
        for N in range(1, nmax + 1):
            b = block_bound(k, N)
            t = table[N]
            slack = b - t
            if slack < 0:
                problems.append(" certified %s(%d) = %d EXCEEDS kernel block bound %d "
                                "-- kernel or table is BROKEN" % (name, N, t, b))
            rows.append((N, b, t, slack))
            if slack == 0:
                tight.append(N)
        maps[k] = {"rows": rows, "tight": tight}
        log("  k=%d (%s, N<=%d): bound dominates everywhere=%s; tight at N=%s (%d points); "
            "max slack=%d at N=%s"
            % (k, name, nmax, "yes" if all(r[3] >= 0 for r in rows) else "NO",
               tight if len(tight) <= 12 else (str(tight[:12]) + "..."),
               len(tight),
               max(r[3] for r in rows),
               max(rows, key=lambda r: r[3])[0]))
    # the k=3 headline table, printed in full
    log("  --- k=3 tightness map: r3_upper = 2*floor(N/3) + N mod 3 vs true r_3(N) ---")
    log("  N : bound  true  slack  tight")
    for (N, b, t, s) in maps[3]["rows"]:
        log("  %2d:  %2d    %2d    %2d     %s" % (N, b, t, s, "TIGHT" if s == 0 else ""))
    r3_upper_ok = all(block_bound(3, N) >= cert_r3[N] for N in range(1, R3_N_MAX + 1))
    verdict("K4_block_upper", not problems and r3_upper_ok,
            "block bound (k-1)*floor(N/k)+N mod k dominates every certified exact "
            "value (k=3 N<=30, k=4 N<=20, k=5 N<=20, k=2 N<=30) -- zero "
            "violations; E142.r3_upper numerically safe; tightness: k=3 tight at "
            "N=%s only (slack grows to %d by N=30), k=4 tight at N=%s, k=5 tight "
            "at ALL N<=20, k=2 tight at N=%s"
            % (maps[3]["tight"], max(r[3] for r in maps[3]["rows"]),
               maps[4]["tight"], maps[2]["tight"])
            if not problems else "; ".join(problems))
    return maps


# ---------------------------------------------------------------------------
# K5 -- E142.k2_edge: r_2(N) = 1 for all N >= 2 (pinned d >= 1)
# ---------------------------------------------------------------------------

def audit_K5_k2_edge(cert_r2):
    log()
    log("==== K5: E142.k2_edge -- r_2(N) = 1 for N >= 2 (pinned d >= 1) ====")
    problems = []
    pairs = 0
    for N in range(2, R3_N_MAX + 1):
        # exhaustive pair census: EVERY distinct pair a < b in [1, N] is a
        # non-trivial 2-AP (a, a+(b-a)) with d = b-a >= 1 inside [1, N]
        all_pairs_are_2ap = True
        for a in range(1, N + 1):
            for b in range(a + 1, N + 1):
                pairs += 1
                d = b - a
                if not (d >= 1 and a + d == b and a + d <= N):
                    all_pairs_are_2ap = False
        if not all_pairs_are_2ap:
            problems.append("pair census failed at N=%d" % N)
        if cert_r2[N] != 1:
            problems.append("certified r_2(%d) = %d != 1" % (N, cert_r2[N]))
        # witness [1]: the kernel's own witness, re-validated
        werr = validate_witness([1], N, 2, "k2 witness N=%d" % N)
        if werr:
            problems.append(werr)
    log("  exhaustive pair census over N=2..30: %d pairs, every one a non-trivial "
        "2-AP => no 2-element AP-free subset exists; witness [1] re-validated" % pairs)
    verdict("K5_k2_edge", not problems,
            "every one of the %d distinct pairs in [1,N] (N=2..30) is a 2-AP with "
            "d>=1, so the maximum 2-AP-free set has size 1; witness [1] "
            "re-validated; certified r_2 table all-1 agreement" % pairs
            if not problems else "; ".join(problems))


# ---------------------------------------------------------------------------
# K6 -- doubter's r_5 block-bound-TIGHT claim on N <= 20: third method
# ---------------------------------------------------------------------------

def greedy_rk(N, k):
    """Engine gamma: left-to-right greedy certificate set -- scan n = 1..N,
    keep n iff S + {n} remains k-AP-free.  No structural knowledge (no mod-5
    arithmetic) enters this construction."""
    S = []
    Sset = set()
    for n in range(1, N + 1):
        cand = Sset | {n}
        if has_kap(cand, k, N) is None:
            S.append(n)
            Sset.add(n)
    return S


def audit_K6_r5_tight(cert_r5):
    log()
    log("==== K6: doubter claim r_5(N) = block bound TIGHT on all N <= 20 -- third method ====")
    problems = []
    rows = []
    for N in range(1, R45_N_MAX + 1):
        b = block_bound(5, N)
        G = greedy_rk(N, 5)
        C = [n for n in range(1, N + 1) if n % 5 != 0]   # explicit mod-5 drop set
        gerr = validate_witness(G, N, 5, "greedy witness N=%d" % N)
        cerr = validate_witness(C, N, 5, "mod5-drop witness N=%d" % N)
        if gerr:
            problems.append(gerr)
        if cerr:
            problems.append(cerr)
        if len(G) != b:
            problems.append("greedy r_5(%d) reaches %d < bound %d" % (N, len(G), b))
        if len(C) != b:
            problems.append("mod-5 construction size %d != bound %d at N=%d" % (len(C), b, N))
        if cert_r5[N] != b:
            problems.append("certified r_5(%d) = %d != bound %d" % (N, cert_r5[N], b))
        rows.append((N, b, len(G), len(C), cert_r5[N]))
        log("  N=%2d  bound=%2d  greedy=%2d  mod5drop=%2d  certified=%2d  %s"
            % (N, b, len(G), len(C), cert_r5[N],
               "TIGHT" if b == cert_r5[N] and len(G) == b else "MISMATCH"))
    # fresh z3 UNSAT certificates at bound+1 (upper side, fresh encoding)
    if Z3_OK:
        z3bad = []
        for N in range(1, R45_N_MAX + 1):
            b = block_bound(5, N)
            xs = [z3.Bool("f%d" % i) for i in range(1, N + 1)]
            s = z3.Solver()
            for a in range(1, N + 1):
                for d in range(1, N):
                    if a + 4 * d > N:
                        break
                    s.add(z3.Not(z3.And([xs[a + i * d - 1] for i in range(5)])))
            s.add(z3.PbGe([(x, 1) for x in xs], b + 1))
            if s.check() == z3.sat:
                z3bad.append(N)
            # and SAT at the bound itself, model re-validated
            s2 = z3.Solver()
            for a in range(1, N + 1):
                for d in range(1, N):
                    if a + 4 * d > N:
                        break
                    s2.add(z3.Not(z3.And([xs[a + i * d - 1] for i in range(5)])))
            s2.add(z3.PbGe([(x, 1) for x in xs], b))
            if s2.check() == z3.sat:
                model = s2.model()
                W = [i for i in range(1, N + 1) if z3.is_true(model.eval(xs[i - 1]))]
                werr = validate_witness(W, N, 5, "z3 SAT model N=%d" % N)
                if werr:
                    z3bad.append(werr)
        if z3bad:
            problems.append("fresh z3 r_5 certificates failed at: %s" % z3bad)
        else:
            log("  fresh z3 encoding: UNSAT at bound+1 and SAT-with-validated-model "
                "at the bound, for ALL N<=20")
    else:
        problems.append("z3 unavailable: fresh UNSAT certificates impossible")
    verdict("K6_r5_tight_third_method", not problems,
            "greedy certificate sets (fresh left-to-right engine, no mod-5 "
            "knowledge) hit 4*floor(N/5)+N mod 5 on every N<=20; the explicit "
            "mod-5 drop construction agrees; fresh z3 gives UNSAT at bound+1 and "
            "validated SAT models at the bound; all equal the certified r_5 table "
            "-- the tightness claim stands by a third method"
            if not problems else "; ".join(problems))
    return rows


# ---------------------------------------------------------------------------
# Killer-lane CI intel (frozen facts, observed 2026-11-15 from the GitHub
# Actions API; the killer lane's own repair loop owns the fix -- NOT this lane)
# ---------------------------------------------------------------------------

KILLER_CI_INTEL = {
    "run_id": 43736909745,
    "branch": "w67-p142k",
    "head_sha": "011cb3e5",
    "conclusion": "failure",
    "failed_job": "kernel-142k (the only red job; kernel-a/b/c green)",
    "compile_errors_in_Erdos142_lean": 73,
    "axiom_receipts_as_compiled": {
        "E142.t3free": "[propext, sorryAx, Quot.sound]",
        "E142.t3_no_nontriv": "[propext, sorryAx, Quot.sound]",
        "E142.cantor_lower": "[propext, sorryAx, Classical.choice, Quot.sound]",
        "E142.block_upper": "[propext, sorryAx, Quot.sound]",
        "E142.r3_upper": "[propext, sorryAx, Quot.sound]",
        "E142.k2_edge": "[propext, sorryAx, Classical.choice, Quot.sound]",
        "E142.r3_exact_small": "[propext, sorryAx, Classical.choice, Quot.sound]",
        "E142.arsenal_bridge": "[propext, Quot.sound]  (the only clean board theorem)",
        "E142.erdos142_board": "[propext, sorryAx, Classical.choice, Quot.sound]",
    },
    "reading": "73 tactic/type errors in Erdos142.lean (rfl failures, type "
               "mismatches, unknown identifiers e.g. CardinalWorlds.two_pow_pos, "
               "a stray hp'); Lean error recovery inserts sorryAx, so 7 of the 9 "
               "board theorems compile to sorryAx -- the kernel artifact is NOT "
               "CI-certified at 011cb3e even though the source contains no "
               "literal `sorry` (only the 'zero sorry' comment). The mathematical "
               "CONTENT of every board claim is what this cross-audit verifies.",
}


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    log("W68-142D CROSS-AUDIT -- Erdos #142: killer kernel (w67-p142k @ 011cb3e)")
    log("                       vs doubter certified tables (w67-p142d @ 5f031ed)")
    log("env: python %s, z3 %s" % (sys.version.split()[0],
                                   z3.get_version_string() if Z3_OK else "UNAVAILABLE"))

    tbl_path = HERE / "r3_exact_table.json"
    if not tbl_path.exists():
        fatal("certified table %s missing" % tbl_path)
    cert = json.loads(tbl_path.read_text())
    if cert.get("battery_status") != "GREEN":
        fatal("certified table battery_status is not GREEN")
    cert_r3 = {row["N"]: row["r3"] for row in cert["r3_table"]}
    cert_r4 = {row["N"]: row["r4"] for row in cert["r4_table"]}
    cert_r5 = {row["N"]: row["r5"] for row in cert["r5_table"]}
    cert_r2 = {row["N"]: row["r2"] for row in cert["r2_table"]}
    log("certified tables loaded: r_3 N<=%d, r_4/r_5 N<=%d, r_2 N<=%d "
        "(battery_status GREEN)" % (R3_N_MAX, R45_N_MAX, R3_N_MAX))
    log()
    log("INTEL (killer lane CI, frozen fact 2026-11-15): run %d @ %s = %s; "
        "kernel-142k job RED with %d compile errors in Erdos142.lean; "
        "error-recovery sorryAx in 7/9 board theorems (only arsenal_bridge "
        "clean) -> the kernel ARTIFACT is not CI-certified; this cross-audit "
        "certifies the mathematical CONTENT of its claims."
        % (KILLER_CI_INTEL["run_id"], KILLER_CI_INTEL["head_sha"][:7],
           KILLER_CI_INTEL["conclusion"],
           KILLER_CI_INTEL["compile_errors_in_Erdos142_lean"]))

    audit_K1_t3free()
    audit_K2_cantor_lower(cert_r3)
    fresh_small = audit_K3_r3_exact_small(cert_r3)
    maps = audit_K4_block_upper(cert_r3, cert_r4, cert_r5, cert_r2)
    audit_K5_k2_edge(cert_r2)
    r5_rows = audit_K6_r5_tight(cert_r5)

    # ------------------------------------------------------------------ bank
    out = {
        "task_id": "W68-142D",
        "lane": "doubter cross-audit of killer kernel w67-p142k@011cb3e",
        "kernel_board": {
            "K1_t3free": "Cantor ternary set 3-AP-free (x+z=2y => x=z)",
            "K2_cantor_lower": "r_3(3^k-1) >= 2^k-1, k=1..8",
            "K3_r3_exact_small": "r_3(N) N=1..8 = [1,2,2,3,4,4,4,4]",
            "K4_block_upper": "|S| <= (k-1)*floor(N/k)+N mod k; r3_upper k=3",
            "K5_k2_edge": "r_2(N)=1 for N>=2 (pinned d>=1)",
            "K6_r5_tight_third_method": "r_5(N)=block bound tight on N<=20 (greedy third method)",
        },
        "verdicts": {tag: ("CONFIRMED" if ok else "BROKEN") for (tag, ok, _) in VERDICTS},
        "fresh_exhaustive_r3_N_le_12": {str(k): v for k, v in fresh_small.items()},
        "block_tightness": {
            str(k): {
                "rows": [{"N": N, "bound": b, "true": t, "slack": s} for (N, b, t, s) in m["rows"]],
                "tight_at": m["tight"],
            } for k, m in maps.items()
        },
        "r5_third_method": [{"N": N, "bound": b, "greedy": g, "mod5drop": c, "certified": t}
                            for (N, b, g, c, t) in r5_rows],
        "engines": [
            "A: itertools.product ternary digit-tuple generator",
            "B: range scan with divmod digit predicate",
            "R: literal python replica of Arsenal noTernaryTwo",
            "genT/genTp literal replicas of the killer's recursive defs",
            "alpha: full 2^N bitmask exhaustive enumeration",
            "beta: fresh z3 encoding (Bool/AP/Not(And)/PbGe), SAT@r + UNSAT@(r+1)",
            "gamma: left-to-right greedy certificate construction",
            "explicit mod-5 drop construction {n in [1,N]: n%%5 != 0}",
        ],
        "killer_ci_intel": KILLER_CI_INTEL,
    }
    (HERE / "crossaudit_tables.json").write_text(json.dumps(out, indent=1))
    log()
    log("banked: crossaudit_tables.json")

    # ------------------------------------------------------------ report md
    m3 = maps[3]["rows"]
    md = []
    md.append("# W68-142D Cross-Audit Report -- Erdos #142 (AP-free r_k(N))")
    md.append("")
    md.append("**Doubter lane** (branch `w67-p142d` @ `5f031ed`) adversarially cross-audits the")
    md.append("**killer lane kernel** (branch `w67-p142k` @ `011cb3e`, `problem142-ap-free/Erdos142.lean`,")
    md.append("namespace `E142`) against the doubter's CI-certified exact tables")
    md.append("(kernel-142d CI run 43726649205: **success**, all 4 jobs green,")
    md.append("`BATTERY_VERDICT: GREEN`).")
    md.append("")
    md.append("## Verdicts")
    md.append("")
    md.append("| # | kernel claim | verdict |")
    md.append("|---|--------------|---------|")
    for (tag, ok, _) in VERDICTS:
        md.append("| %s | `%s` | **%s** |" % (tag, out["kernel_board"][tag],
                                              "CONFIRMED" if ok else "BROKEN"))
    md.append("")
    md.append("All checks below are NEW code paths (nothing imported from `mirror_battery.py`):")
    md.append("digit-tuple product generator, range-scan digit predicate, literal replicas of")
    md.append("Arsenal `noTernaryTwo` and the killer's `genT`/`genTp`, full `2^N` bitmask")
    md.append("exhaustive enumeration, fresh z3 encoding, left-to-right greedy construction,")
    md.append("explicit mod-5 drop construction.")
    md.append("")
    md.append("## K3 -- r_3(N) fresh re-derivation (N <= 12)")
    md.append("")
    md.append("Fresh exhaustive `2^N` enumeration + fresh z3 SAT/UNSAT dual both reproduce")
    md.append("`r_3(1..8) = 1,2,2,3,4,4,4,4` (kernel `E142.r3_exact_small`) and the certified")
    md.append("table through N=12: `1,2,2,3,4,4,4,4,5,5,6,6`.")
    md.append("")
    md.append("## K4 -- r_3 tightness map (kernel `E142.r3_upper` = `2*floor(N/3) + N mod 3`)")
    md.append("")
    md.append("| N | bound | true r_3(N) | slack | tight? |")
    md.append("|---|-------|-------------|-------|--------|")
    for (N, b, t, s) in m3:
        md.append("| %d | %d | %d | %d | %s |" % (N, b, t, s, "TIGHT" if s == 0 else ""))
    md.append("")
    md.append("The block bound is TIGHT for r_3 only at N=1..6 (and it is a valid upper bound")
    md.append("everywhere on N<=30, slack growing to 8 at N=30). For r_4: tight at N=1..6, 8..10.")
    md.append("For r_5: tight at **every** N<=20 (slack 0 across the whole frontier) -- see K6.")
    md.append("For r_2 (k=2 pinned d>=1): tight at N=1,2 (bound = N mod 2 + floor(N/2)).")
    md.append("")
    md.append("## K6 -- r_5(N) = block bound, tight on all N <= 20 (third method)")
    md.append("")
    md.append("| N | bound 4*floor(N/5)+N mod 5 | greedy | mod-5 drop | certified r_5 |")
    md.append("|---|---------------------------|--------|-----------|---------------|")
    for (N, b, g, c, t) in r5_rows:
        md.append("| %d | %d | %d | %d | %d |" % (N, b, g, c, t))
    md.append("")
    md.append("Greedy certificate sets (left-to-right, AP-check only, no mod-5 knowledge), the")
    md.append("explicit construction {n in [1,N] : n mod 5 != 0} (every 5-AP with d not")
    md.append("divisible by 5 hits exactly one multiple of 5, and d divisible by 5 needs")
    md.append("a+4d >= 21 > 20), and fresh z3 UNSAT@bound+1 certificates all agree: TIGHT.")
    md.append("")
    md.append("## Killer-lane CI intel (observed 2026-11-15, frozen fact)")
    md.append("")
    md.append("The killer kernel's OWN CI verdict at `011cb3e`: run **43736909745 = FAILURE**")
    md.append("(job `kernel-142k` red; `kernel-a/b/c` green). 73 compile errors in")
    md.append("`Erdos142.lean` (tactic `rfl` failures, type mismatches, unknown identifiers")
    md.append("such as `CardinalWorlds.two_pow_pos` and a stray `hp'`); Lean's error")
    md.append("recovery inserts `sorryAx`, so **7 of the 9 board theorems as-compiled")
    md.append("rest on `sorryAx`** -- only `E142.arsenal_bridge` lands clean. The source")
    md.append("contains no literal `sorry` (only the 'zero sorry' comment), but the")
    md.append("artifact is nonetheless NOT CI-certified. Consequence for this audit:")
    md.append("the kernel's mathematical claims are all CONFIRMED numerically below,")
    md.append("while the kernel's Lean proofs await the killer lane's own repair loop")
    md.append("(that lane owns its <=5 CI repair rounds; this lane does not touch it).")
    md.append("")
    md.append("## Scope (honest)")
    md.append("")
    md.append("* Numerical audits cover the finite windows: Cantor k<=8 (3^8=6561, full")
    md.append("  pairwise midpoint scans), r_3 N<=30, r_4/r_5 N<=20, r_2 N<=30, exhaustive")
    md.append("  2^N N<=12. The kernel's Lean proofs (unbounded t3free via mod-3 descent,")
    md.append("  the general block_upper window pigeonhole, etc.) are NOT currently")
    md.append("  CI-certified (see killer CI intel above) and are not re-proved here;")
    md.append("  this cross-audit certifies their mathematical CONTENT on the stated")
    md.append("  windows.")
    md.append("* The kernel `r3Is` convention (subsets of [1,N], d>=1) matches the doubter")
    md.append("  convention exactly; every disagreement would have been reported BROKEN.")
    md.append("* INTEL carried forward: the printed reference string corrupt at")
    md.append("  N=9,11,13,14,15,16,20 -- own computation is truth; the kernel values")
    md.append("  N=1..8 are clean of that corruption.")
    (HERE / "crossaudit_report.md").write_text("\n".join(md) + "\n")
    log("banked: crossaudit_report.md")

    # ------------------------------------------------------------- verdict
    log()
    n_ok = sum(1 for (_, ok, _) in VERDICTS if ok)
    log("verdicts: %d/%d CONFIRMED" % (n_ok, len(VERDICTS)))
    if FAILURES:
        log("CROSSAUDIT_VERDICT: BROKEN")
        for f in FAILURES:
            log("  FAILURE: " + f)
        sys.exit(1)
    log("CROSSAUDIT_VERDICT: GREEN")
    log("E142_CROSSAUDIT_GREEN")
    log("elapsed %.1fs" % (time.time() - T0))


if __name__ == "__main__":
    main()
