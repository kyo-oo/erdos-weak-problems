#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
COMPARATOR 142 — the DeepMind-style DIRECT verifier for Erdos #142 (W70-B)
===========================================================================
Lane W70-B (branch w70-b-p142comp, base campaign 4c4a072). BOSS ordered the
DeepMind comparator methodology INSTEAD of Lean for this lane: a challenge
file (challenge.json — the frozen spec), a solution file (solution.json —
the campaign's honestly-labeled claims), and THIS comparator, which verifies
the solution DIRECTLY against the challenge by computation — FunSearch's
"systematic evaluator" loop and AlphaCode's test-based grading, applied to
#142. NO Lean anywhere in this lane. Pure python3 + z3 (required) + gmpy2
(opportunistic, exact-identical fallback), exact integer arithmetic only.

CONVENTION (pinned by the campaign, identical in both json files):
  non-trivial k-term AP: a, a+d, ..., a+(k-1)d, a >= 1, d >= 1;
  r_k(N) = max {|S| : S ⊆ [1,N], S contains no non-trivial k-AP}.

WHAT THE COMPARATOR CERTIFIES (each check prints a receipt + VERDICT):
  C0  spec parse + stack report + checker self-tests (incl. negative
      controls proving the checkers are not vacuous).
  C1  r_3 exact table N=1..30 by THREE fresh methods:
      M1 iterative-deepening DFS branch-and-bound with pair-ban
         propagation + exact-suffix bounds + memoization;
      M2 z3 SAT/UNSAT dual certificates N<=16 (every SAT model
         re-validated, every upper bound a cardinality-UNSAT);
      M3 exhaustive 2^N subset brute force N<=12.
      All three must agree with solution.json R3-TABLE exactly.
      Negative control: a corrupted table MUST be rejected.
  C2  r_4 table N=1..20 and r_5 table N=1..20 by the generalized k-AP
      B&B (M1') + z3 dual certificates N<=12 (M2'); agreement with
      solution.json; the monotonicity law r_2 <= r_3 <= r_4 <= r_5 on
      N=1..20; r_5 tightness (== block bound on all N<=20).
  C3  Cantor lower-bound family k=1..10: ternary-{0,1}-digit integers in
      [1,3^k-1]; two independent generation routes; |T_k| = 2^k-1;
      containment; 3-AP-freeness by FULL pair-midpoint scan (all k<=10)
      + independent (a,d)-scan (k<=8); hence r_3(3^k-1) >= 2^k-1 (exact
      table tie-in for 3^k-1 <= 30). Negative control: the ternary-{1,2}
      family MUST be rejected as AP-containing.
  C4  Block upper bound k=3..6, N=1..60: every k-AP-free S ⊆ [1,N]
      satisfies |S| <= (k-1)*floor(N/k) + (N mod k). Exhaustive N<=16
      (maxima from the generalized B&B, cross-matched for k=3 against
      the C1 pair-ban engine); r_3 maximum witnesses N=17..30 tortured;
      randomized greedy + dense-sieve + leave-one-residue + Cantor
      constructions for N=17..60, every set re-validated by an
      independent (a,d)-scan. Negative controls: crippled bound (rhs-1)
      MUST trigger; an AP-containing witness MUST be rejected.
  C5  k=2 edge: r_2(1)=1, r_2(N)=1 for N>=2 (2^N brute N<=12 +
      exhaustive 435-pair scan N<=30 + witness [1] re-validated).
  C6  Context shadows (machine-checkable parts of the DeepMind/SOTA
      context block): the cap-set record arithmetic sanity (512 = 2^9
      points of 3^8 = 6561 in F_3^8, vs our integer-interval Cantor
      T_8: 255 of 6561 — related constructions, DISTINCT problems);
      the honest gap map r_3(N)/N vs the certified envelope for N<=30.
  C7  Honest-label audit: the solution's claim ids are exactly the
      expected set, every claim carries a nonempty exact label, and the
      OPEN-SCOPE declaration (asymptotic OPEN for every k >= 3) is
      present and uncontradicted.
  C8  Final gate.

EXIT CODES: 0 = COMPARATOR_142_GREEN; 1 = any failure; 2 = CRITICAL
(table disagreement with solution.json). Any disagreement with
solution.json, any checker failure, any failed negative control => RED.
"""

import sys
import os
import json
import math
import time

T0 = time.time()
SEED = 70142  # deterministic comparator

# ---------------------------------------------------------------------------
# stack report: z3 REQUIRED, gmpy2 opportunistic (identical exact results)
# ---------------------------------------------------------------------------
Z3_OK = False
GMPY2_OK = False
try:
    import z3
    Z3_OK = True
except Exception as e:
    sys.stderr.write("FATAL: z3 not importable (%s)\n" % e)

if Z3_OK:
    try:
        import gmpy2
        GMPY2_OK = True
    except Exception:
        GMPY2_OK = False


def popcount(x):
    """Exact integer popcount (gmpy2-accelerated when available)."""
    if GMPY2_OK:
        return int(gmpy2.popcount(x))
    return bin(x).count("1")


def stamp():
    return "t=%+7.1fs" % (time.time() - T0)


# ---------------------------------------------------------------------------
# harness: every check prints a receipt line with VERDICT
# ---------------------------------------------------------------------------
FAILURES = []
CRITICALS = []
CHECKS = [0, 0]  # [passed, failed]


def check(cid, desc, ok, detail=""):
    """One comparator check + receipt + VERDICT."""
    CHECKS[0 if ok else 1] += 1
    line = "[%s] %s%s — VERDICT: %s" % (cid, desc,
                                        (" | " + detail) if detail else "",
                                        "PASS" if ok else "FAIL")
    print(line, flush=True)
    if not ok:
        FAILURES.append(line)
    return ok


def critical(cid, desc, detail=""):
    """A disagreement with solution.json (or engine-vs-engine) = CRITICAL."""
    CHECKS[1] += 1
    line = "[%s] CRITICAL_FINDING: %s%s — VERDICT: FAIL" % (
        cid, desc, (" | " + detail) if detail else "")
    print(line, flush=True)
    CRITICALS.append(line)
    FAILURES.append(line)
    return False


def info(msg):
    print("      %s" % msg, flush=True)


# ---------------------------------------------------------------------------
# §INDEPENDENT CHECKERS (disjoint code paths from the search engines)
# ---------------------------------------------------------------------------

def kap_scan(S, k, N):
    """Literal (a,d)-scan k-AP detector over the pinned definition.
    Returns (True, (a,d)) iff S contains a non-trivial k-AP inside [1,N]."""
    if not S:
        return (False, None)
    if k < 2:
        return (False, None)
    for a in sorted(S):
        dmax = (N - a) // (k - 1)
        for d in range(1, dmax + 1):
            hit = True
            for j in range(k):
                if (a + j * d) not in S:
                    hit = False
                    break
            if hit:
                return (True, (a, d))
    return (False, None)


def kap_free(S, k, N):
    return not kap_scan(set(S), k, N)[0]


def ap3_free_pairmid(S):
    """3-AP check by full pair-midpoint scan: for every pair x < z with
    x+z even, (x+z)/2 must lie outside S."""
    A = sorted(set(S))
    Sset = set(A)
    n = len(A)
    for i in range(n):
        xi = A[i]
        for j in range(i + 1, n):
            s = xi + A[j]
            if s & 1:
                continue
            m = s >> 1
            if xi < m < A[j] and m in Sset:
                return False
    return True


def ap3_free_literal(S):
    """3-AP check by literal nested triple enumeration."""
    A = sorted(set(S))
    n = len(A)
    for i in range(n):
        for j in range(i + 1, n):
            for l in range(j + 1, n):
                if A[i] + A[l] == 2 * A[j]:
                    return False
    return True


def block_rhs(N, k):
    """The block upper bound right-hand side (challenge BLOCK-UPPER)."""
    return (k - 1) * (N // k) + (N % k)


def valid_witness(S, N, k):
    """A maximum-size witness must be a subset of [1,N], distinct, and
    k-AP-free under the independent (a,d)-scan."""
    S = list(S)
    if len(set(S)) != len(S):
        return False
    if not all(1 <= v <= N for v in S):
        return False
    return kap_free(S, k, N)


# ---------------------------------------------------------------------------
# §ENGINES (three fresh, mutually independent search methods)
# ---------------------------------------------------------------------------

def r3_pairban_search(N, t, Rsuf):
    """M1: find a 3-AP-free S ⊆ [1..N] with |S| = t, or None.

    Iterative-deepening DFS over elements 1..N in increasing order
    (include-first). PAIR-BAN PROPAGATION: element v is banned iff
    v = 2b - a for two already-selected a < b (v would complete the AP
    (a,b,v) as its top term). When v is selected, every w = 2v - u
    (u selected, w in (v,N]) is banned (v is the midpoint of (u,v,w));
    APs with v as the bottom term are banned when their midpoint m is
    selected later (m bans 2m - v). All three roles of every element in
    every future AP are covered. EXACT-SUFFIX BOUNDS: additions from
    [i..N] are capped by min(avail, Rsuf[N-i+1]) — the EXACT r_3 value
    of a length-(N-i+1) interval (translation invariance), known
    inductively for all proper suffixes. NO block bound of the audited
    claim is used anywhere in the pruning (zero circularity).
    MEMOIZATION: failed states cached under (i, sel, banned >> i)."""
    if t <= 0:
        return []
    if t > N:
        return None
    sys.setrecursionlimit(200000)
    banned = 0
    sel = 0
    S = []
    found = [None]
    memo = set()

    def dfs(i, avail):
        nonlocal banned, sel
        if len(S) == t:
            found[0] = list(S)
            return True
        if i > N:
            return False
        rem = N - i + 1
        cap = Rsuf[rem] if rem < N else avail
        if cap > avail:
            cap = avail
        if len(S) + cap < t:
            return False
        key = (i, sel, banned >> i)
        if key in memo:
            return False
        if not ((banned >> i) & 1):
            # include i: ban every w = 2i - u (u selected, i < w <= N)
            newbits = 0
            for u in S:
                w = 2 * i - u
                if i < w <= N and not ((banned >> w) & 1) \
                        and not ((newbits >> w) & 1):
                    newbits |= (1 << w)
            banned |= newbits
            S.append(i)
            sel |= (1 << i)
            if dfs(i + 1, avail - 1 - popcount(newbits)):
                return True
            S.pop()
            sel &= ~(1 << i)
            banned &= ~newbits
            # exclude i (i was available)
            if dfs(i + 1, avail - 1):
                return True
        else:
            # i banned: forced exclude, does not consume avail
            if dfs(i + 1, avail):
                return True
        memo.add(key)
        return False

    if dfs(1, N):
        return found[0]
    return None


def r3_table(Nmax):
    """Exact r_3(0..Nmax) via M1 + the monotone +1 lemma
    (R[N] ∈ {R[N-1], R[N-1]+1}: drop N from any optimal set), itself
    cross-checked against brute force in C1."""
    R = [0] * (Nmax + 1)
    W = [[] for _ in range(Nmax + 1)]
    for N in range(1, Nmax + 1):
        t = R[N - 1] + 1
        w = r3_pairban_search(N, t, R)
        if w is not None:
            R[N] = t
            W[N] = w
        else:
            R[N] = R[N - 1]
            W[N] = list(W[N - 1])
    return R, W


def brute_rk(N, k):
    """M3: exhaustive 2^N subset enumeration (fully independent)."""
    apmasks = []
    if k >= 2:
        for d in range(1, (N - 1) // (k - 1) + 1):
            for a in range(1, N - (k - 1) * d + 1):
                m = 0
                for j in range(k):
                    m |= 1 << (a + j * d - 1)
                apmasks.append(m)
    best = 0
    bestmask = 0
    for mask in range(1 << N):
        ok = True
        for am in apmasks:
            if mask & am == am:
                ok = False
                break
        if ok:
            c = popcount(mask)
            if c > best:
                best = c
                bestmask = mask
    wit = [v + 1 for v in range(N) if (bestmask >> v) & 1]
    return best, wit


def z3_rk(N, k):
    """M2: z3 SAT/UNSAT dual certificate for r_k(N).
    Bools x_v (v in [1,N]); clause: not all of any k-AP. Deepening by
    PbGe cardinality. Returns (r, model, unsat_flag): r = max feasible
    size; the model is re-validated by the INDEPENDENT (a,d)-scan by the
    caller; unsat_flag = the r+1 check returned UNSAT (the upper-bound
    certificate)."""
    x = [z3.Bool("x%d" % v) for v in range(1, N + 1)]
    s = z3.Solver()
    for d in range(1, (N - 1) // (k - 1) + 1):
        for a in range(1, N - (k - 1) * d + 1):
            s.add(z3.Or([z3.Not(x[a + j * d - 1]) for j in range(k)]))
    r = 0
    model = []
    while True:
        s.push()
        s.add(z3.PbGe([(x[v], 1) for v in range(N)], r + 1))
        res = s.check()
        if res == z3.sat:
            m = s.model()
            model = sorted(v + 1 for v in range(N)
                           if z3.is_true(m.eval(x[v], model_completion=True)))
            r += 1
            s.pop()
        elif res == z3.unsat:
            s.pop()
            return r, model, True
        else:
            s.pop()
            return None, None, False


def ap_masks(N, k):
    """All non-trivial k-AP masks inside [1..N] (bit v = element v)."""
    out = []
    if k < 2:
        return out
    for d in range(1, (N - 1) // (k - 1) + 1):
        for a in range(1, N - (k - 1) * d + 1):
            m = 0
            for j in range(k):
                m |= 1 << (a + j * d)
            out.append(m)
    return out


def masks_by_element(N, k):
    by = [[] for _ in range(N + 1)]
    for m in ap_masks(N, k):
        for v in range(1, N + 1):
            if (m >> v) & 1:
                by[v].append(m)
    return by


def rk_mask_search(N, t, k, Rsuf, by_elem):
    """M1': generalized k-AP B&B (a SECOND engine design: AP-mask
    include-checks, no pair-ban propagation; shares no code path with
    the C1 pair-ban engine). Element i may be added iff no k-AP mask M
    containing i has M \\ {i} ⊆ selected. Every k-AP is therefore
    blocked at its maximum element. Same exact-suffix bound + memo."""
    if t <= 0:
        return []
    if t > N:
        return None
    sys.setrecursionlimit(200000)
    sel = 0
    S = []
    found = [None]
    memo = set()

    def dfs(i, avail):
        nonlocal sel
        if len(S) == t:
            found[0] = list(S)
            return True
        if i > N:
            return False
        rem = N - i + 1
        cap = Rsuf[rem] if rem < N else avail
        if cap > avail:
            cap = avail
        if len(S) + cap < t:
            return False
        key = (i, sel)
        if key in memo:
            return False
        ok = True
        bi = 1 << i
        for M in by_elem[i]:
            rest = M & ~bi
            if rest & sel == rest:
                ok = False
                break
        if ok:
            S.append(i)
            sel |= bi
            if dfs(i + 1, avail - 1):
                return True
            S.pop()
            sel &= ~bi
        if dfs(i + 1, avail - 1):
            return True
        memo.add(key)
        return False

    if dfs(1, N):
        return found[0]
    return None


def rk_mask_table(Nmax, k, by_elem):
    R = [0] * (Nmax + 1)
    W = [[] for _ in range(Nmax + 1)]
    for N in range(1, Nmax + 1):
        t = R[N - 1] + 1
        w = rk_mask_search(N, t, k, R, by_elem)
        if w is not None:
            R[N] = t
            W[N] = w
        else:
            R[N] = R[N - 1]
            W[N] = list(W[N - 1])
    return R, W


def greedy_from_order(order, by_elem):
    """Greedy k-AP-free construction in a given element order (mask
    include-checks)."""
    sel = 0
    S = []
    for v in order:
        ok = True
        bv = 1 << v
        for M in by_elem[v]:
            rest = M & ~bv
            if rest & sel == rest:
                ok = False
                break
        if ok:
            S.append(v)
            sel |= bv
    return S


def sieve_to_apfree(S, N, k, rng):
    """Dense sieve: while any k-AP lies fully in S, delete a random
    member of one (bitmask arithmetic)."""
    masks = ap_masks(N, k)
    smask = 0
    for v in S:
        smask |= 1 << v
    while True:
        hit = None
        for M in masks:
            if smask & M == M:
                hit = M
                break
        if hit is None:
            out = set()
            for v in range(1, N + 1):
                if (smask >> v) & 1:
                    out.add(v)
            return out
        members = [v for v in range(1, N + 1) if (hit >> v) & 1]
        drop = members[rng.randrange(len(members))]
        smask &= ~(1 << drop)


# ---------------------------------------------------------------------------
# §C0 spec parse + stack + checker self-tests
# ---------------------------------------------------------------------------

def load_json(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def section_c0(chal, sol):
    print("=" * 76, flush=True)
    print("COMPARATOR 142 — DeepMind-style direct verification of Erdos #142",
          flush=True)
    print("challenge: %s" % chal["statement_frozen"], flush=True)
    print("convention: %s" % chal["conventions"]["non_trivial_k_ap"],
          flush=True)
    print("=" * 76, flush=True)
    print("[C0] SPEC PARSE + STACK + CHECKER SELF-TESTS", flush=True)

    check("C0.1", "challenge.json parsed with frozen statement + conventions",
          chal["statement_frozen"].startswith("Let r_k(N)")
          and "d >= 1" in chal["conventions"]["non_trivial_k_ap"],
          "statement frozen verbatim; d >= 1 pinned")

    ids = [c["id"] for c in sol["claims"]]
    expected_ids = ["R3-TABLE", "R4-TABLE", "R5-TABLE", "CANTOR-LOWER",
                    "BLOCK-UPPER", "K2-EDGE", "MONO-LAW", "OPEN-SCOPE"]
    check("C0.2", "solution.json parsed; claim ids exactly the expected set",
          sorted(ids) == sorted(expected_ids),
          "ids=%s" % ",".join(sorted(ids)))

    check("C0.3", "stack: python %s, z3 %s (REQUIRED), gmpy2 %s (optional)"
          % (sys.version.split()[0],
             z3.get_version_string() if Z3_OK else "MISSING",
             "present" if GMPY2_OK else "absent (pure-python fallback, "
             "identical exact results)"),
          Z3_OK,
          "z3 %s" % (z3.get_version_string() if Z3_OK else "NOT IMPORTABLE"))

    # checker self-tests on known AP / non-AP sets
    cases = [
        ({1, 2, 3}, 3, True), ({1, 2, 4}, 3, False), ({1, 3, 5}, 3, True),
        ({1, 5, 9}, 3, True), ({1, 2, 4, 5}, 3, False),
        ({1, 2, 4, 5, 10, 11, 13, 14}, 3, False),
        ({1, 2, 3, 4}, 4, True), ({1, 2, 3, 5}, 4, False),
        ({1, 3, 5, 7}, 4, True), (set(range(1, 7)), 6, True),
        ({1, 2, 3, 4, 5}, 6, False), ({2, 4, 6, 8, 10, 12}, 6, True),
    ]
    ok = True
    for (S, k, expect_ap) in cases:
        got, _ = kap_scan(S, k, max(S))
        if got != expect_ap:
            ok = False
            info("kap_scan(%s, k=%d) = %s expected %s"
                 % (sorted(S), k, got, expect_ap))
    check("C0.4", "independent (a,d)-scan detector: %d known cases correct"
          % len(cases), ok)

    import random
    rng = random.Random(SEED)
    agree = 0
    ok = True
    for _ in range(300):
        S = set(v for v in range(1, 21) if rng.random() < 0.4)
        a = kap_free(S, 3, 20)
        b = ap3_free_pairmid(S)
        c = ap3_free_literal(S)
        if not (a == b == c):
            ok = False
            info("3-AP checker disagreement on %s: %s %s %s"
                 % (sorted(S), a, b, c))
            break
        agree += 1
    check("C0.5", "three 3-AP checkers agree on %d/300 random sets" % agree,
          ok and agree == 300)

    # negative control: the detector MUST detect a planted AP
    planted, wit = kap_scan({1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, 3, 10)
    check("C0.6", "negative control: planted 3-AP in [1,10] detected (%s)"
          % (wit,), planted and wit == (1, 1))

    # popcount exactness (gmpy2 vs builtin)
    if GMPY2_OK:
        ok = all(int(gmpy2.popcount(v)) == bin(v).count("1")
                 for v in (0, 1, 7, 255, 2 ** 64 - 1, 3 ** 40 + 12345))
        check("C0.7", "gmpy2.popcount identical to builtin on test vectors",
              ok)
    else:
        check("C0.7", "gmpy2 absent: builtin popcount path (exact) in use",
              True)
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C1 the r_3 table by three methods + corrupted-table negative control
# ---------------------------------------------------------------------------

def table_mismatch(derived, claimed, Nmin):
    """Indices N (actual element counts) where derived disagrees with
    the claimed table (claimed[0] corresponds to N = Nmin)."""
    return [Nmin + i for i in range(len(claimed))
            if derived[Nmin + i] != claimed[i]]


def section_c1(chal, sol):
    print("[C1] r_3 EXACT TABLE N=1..30 — THREE FRESH METHODS", flush=True)
    ps = chal["comparator_parameter_space"]["r3_exact_table"]
    NMAX = ps["N_max"]
    claim = sol["claims"][0]
    claimed = claim["table"]["values"]
    Nmin = claim["table"]["N_min"]

    R, W = r3_table(NMAX)
    derived = R[1:]

    check("C1.1", "M1 pair-ban B&B engine produced the full table N=1..%d"
          % NMAX, len(derived) == NMAX and all(0 <= R[n] - R[n - 1] <= 1
                                               for n in range(1, NMAX + 1)),
          "monotone +1 lemma held at every N")

    wit_ok = sum(1 for N in range(1, NMAX + 1)
                 if valid_witness(W[N], N, 3)
                 and len(W[N]) == R[N]
                 and ap3_free_pairmid(W[N]))
    check("C1.2", "M1 maximum witnesses re-validated: %d/%d subsets of "
          "[1,N], distinct, 3-AP-free ((a,d)-scan + pair-midpoint)"
          % (wit_ok, NMAX), wit_ok == NMAX)

    # M3 brute force N <= 12
    bmax = ps["method_3_N_max"]
    b_ok = 0
    ok = True
    for N in range(1, bmax + 1):
        b, _ = brute_rk(N, 3)
        if b == R[N]:
            b_ok += 1
        else:
            ok = False
            info("brute vs engine at N=%d: %d vs %d" % (N, b, R[N]))
    check("C1.3", "M3 exhaustive 2^N brute force N<=%d: %d/%d AGREE with M1"
          % (bmax, b_ok, bmax), ok and b_ok == bmax)

    # M2 z3 dual certificates N <= 16
    zmax = ps["method_2_N_max"]
    z_ok = 0
    z_unsat = 0
    ok = True
    for N in range(1, zmax + 1):
        zr, model, uflag = z3_rk(N, 3)
        if zr is None or not uflag:
            ok = False
            info("z3 no clean UNSAT certificate at N=%d" % N)
            continue
        if len(model) != zr or not valid_witness(model, N, 3):
            ok = False
            info("z3 model at N=%d failed independent re-validation" % N)
            continue
        if zr != R[N]:
            ok = False
            info("z3 vs M1 engine at N=%d: %d vs %d" % (N, zr, R[N]))
            continue
        z_ok += 1
        z_unsat += 1
    check("C1.4", "M2 z3 SAT/UNSAT dual certificates N<=%d: %d/%d AGREE "
          "(%d cardinality-UNSAT upper bounds, every SAT model "
          "re-validated)" % (zmax, z_ok, zmax, z_unsat),
          ok and z_ok == zmax)

    # the agreement law vs solution.json
    mism = table_mismatch(R, claimed, Nmin)
    if mism:
        for N in mism:
            info("N=%d: comparator derives r_3=%d, solution claims %d "
                 "(witness %s)" % (N, R[N], claimed[N - Nmin], W[N]))
        critical("C1.5", "r_3 table DISAGREES with solution.json at N=%s"
                 % mism)
    else:
        check("C1.5", "AGREEMENT LAW: comparator table == solution.json "
              "R3-TABLE, 30/30 values", True,
              "table=%s" % derived)

    # negative control: corrupted table MUST be rejected
    bad = list(claimed)
    bad[9] += 1  # N=10: 5 -> 6
    ctrl_mism = table_mismatch(R, bad, Nmin)
    check("C1.6", "negative control: corrupted r_3 table (N=10 bumped to "
          "%d) REJECTED (mismatch detected at N=%s)" % (bad[9], ctrl_mism),
          ctrl_mism == [10])
    bad2 = list(claimed)
    bad2[29] -= 1  # N=30: 12 -> 11
    ctrl2 = table_mismatch(R, bad2, Nmin)
    check("C1.7", "negative control: corrupted r_3 table (N=30 dropped to "
          "%d) REJECTED (mismatch detected at N=%s)" % (bad2[29], ctrl2),
          ctrl2 == [30])
    print("    %s" % stamp(), flush=True)
    return R, W


# ---------------------------------------------------------------------------
# §C2 r_4 / r_5 tables + monotonicity + r_5 tightness
# ---------------------------------------------------------------------------

def section_c2(chal, sol, R3):
    print("[C2] r_4 AND r_5 EXACT TABLES N=1..20 — GENERALIZED k-AP B&B + "
          "z3 DUAL CERTS", flush=True)
    ok_all = True
    tables = {}
    for idx, kid in ((1, 4), (2, 5)):
        ps_key = "r%d_exact_table" % kid
        ps = chal["comparator_parameter_space"][ps_key]
        NMAX = ps["N_max"]
        zmax = ps["method_2_N_max"]
        claim = sol["claims"][idx]
        claimed = claim["table"]["values"]
        Nmin = claim["table"]["N_min"]

        by = masks_by_element(NMAX, kid)
        R, W = rk_mask_table(NMAX, kid, by)
        tables[kid] = (R, W)
        check("C2.%d.1" % kid, "M1' generalized B&B engine produced the "
              "full r_%d table N=1..%d" % (kid, NMAX),
              all(0 <= R[n] - R[n - 1] <= 1 for n in range(1, NMAX + 1)))

        wit_ok = sum(1 for N in range(1, NMAX + 1)
                     if valid_witness(W[N], N, kid) and len(W[N]) == R[N])
        check("C2.%d.2" % kid, "M1' maximum witnesses re-validated: %d/%d "
              "k-AP-free subsets of [1,N] by independent (a,d)-scan"
              % (wit_ok, NMAX), wit_ok == NMAX)

        z_ok = 0
        ok = True
        for N in range(1, zmax + 1):
            zr, model, uflag = z3_rk(N, kid)
            if zr is None or not uflag or len(model) != zr \
                    or not valid_witness(model, N, kid) or zr != R[N]:
                ok = False
                info("z3 disagreement at k=%d N=%d: z3=%s engine=%d"
                     % (kid, N, zr, R[N]))
            else:
                z_ok += 1
        check("C2.%d.3" % kid, "M2 z3 SAT/UNSAT dual certificates N<=%d: "
              "%d/%d AGREE (models re-validated, cardinality-UNSAT uppers)"
              % (zmax, z_ok, zmax), ok and z_ok == zmax)

        mism = table_mismatch(R, claimed, Nmin)
        if mism:
            critical("C2.%d.4" % kid, "r_%d table DISAGREES with "
                     "solution.json at N=%s" % (kid, mism))
            ok_all = False
        else:
            check("C2.%d.4" % kid, "AGREEMENT LAW: comparator r_%d table =="
                  " solution.json %s, %d/%d values"
                  % (kid, claim["id"], NMAX, NMAX), True,
                  "table=%s" % R[1:])

    R4, _ = tables[4]
    R5, _ = tables[5]
    mono = all(R3[n] <= R4[n] <= R5[n] for n in range(1, 21))
    check("C2.5", "MONO-LAW (machine shadow of the context block): "
          "r_3(N) <= r_4(N) <= r_5(N) on N=1..20", mono,
          "a (k+1)-AP contains a k-AP, so k-AP-free => (k+1)-AP-free")

    tight = all(R5[n] == block_rhs(n, 5) for n in range(1, 21))
    check("C2.6", "r_5 TIGHTNESS (stated in the solution's R5-TABLE "
          "label): r_5(N) == (5-1)*floor(N/5) + (N mod 5) at every "
          "N=1..20", tight)
    print("    %s" % stamp(), flush=True)
    return tables


# ---------------------------------------------------------------------------
# §C3 the Cantor lower-bound family
# ---------------------------------------------------------------------------

def tern01(n):
    """Every base-3 digit of n lies in {0,1}."""
    while n:
        if n % 3 == 2:
            return False
        n //= 3
    return True


def tern_digits(n):
    ds = []
    while n:
        ds.append(n % 3)
        n //= 3
    return ds


def cantor_gen_product(k):
    """Route 1: digit-vector product."""
    import itertools
    vals = set()
    for digs in itertools.product((0, 1), repeat=k):
        v = 0
        for d in digs:
            v = 3 * v + d
        vals.add(v)
    return vals


def cantor_gen_scan(k):
    """Route 2: scan [0, 3^k - 1] with the digit predicate."""
    return set(v for v in range(3 ** k) if tern01(v))


def section_c3(chal, sol, R3):
    print("[C3] CANTOR LOWER-BOUND FAMILY k=1..10 (witness generator spec)",
          flush=True)
    ps = chal["comparator_parameter_space"]["cantor_lower_witness"]
    kmax = ps["k_max"]
    ok = True
    tiein = []
    for k in range(1, kmax + 1):
        M = 3 ** k
        if GMPY2_OK:
            Mg = int(gmpy2.mpz(3) ** k)
            Pg = int(gmpy2.mpz(2) ** k - 1)
            if Mg != M or Pg != 2 ** k - 1:
                ok = False
                info("gmpy2 exact-arithmetic cross-check failed at k=%d" % k)
        P = cantor_gen_product(k)
        Sc = cantor_gen_scan(k)
        if P != Sc:
            ok = False
            info("k=%d: two generation routes disagree" % k)
        T = P - {0}
        exp = 2 ** k - 1
        if len(T) != exp:
            ok = False
            info("k=%d: |T_k| = %d != 2^k-1 = %d" % (k, len(T), exp))
        if not all(1 <= v <= M - 1 for v in T):
            ok = False
            info("k=%d: T_k escapes [1, 3^k-1]" % k)
        if min(T) != 1:
            ok = False
            info("k=%d: min(T_k) != 1" % k)
        # FULL pair-midpoint 3-AP-freeness scan (all k <= kmax)
        if not ap3_free_pairmid(T):
            ok = False
            info("k=%d: pair-midpoint scan FOUND a 3-AP" % k)
        # independent (a,d)-scan re-validation (k <= 8)
        ad = None
        if k <= 8:
            ad = kap_free(T, 3, M - 1)
            if not ad:
                ok = False
                info("k=%d: (a,d)-scan re-validation FAILED" % k)
        # exact-table tie-in whenever 3^k - 1 <= 30
        note = ""
        if M - 1 <= 30:
            good = exp <= R3[M - 1]
            if not good:
                ok = False
                info("k=%d: 2^k-1 = %d > r_3(%d) = %d — table contradiction"
                     % (k, exp, M - 1, R3[M - 1]))
            note = " %d <= r_3(%d)=%d" % (exp, M - 1, R3[M - 1])
            tiein.append(note.strip())
        info("k=%2d: |T_k|=%5d (exp %5d) max=%7d pairmid=FREE ad=%s%s"
             % (k, len(T), exp, max(T),
                "FREE (<=k8)" if k <= 8 else "n/a (k>8 skipped)", note))
    check("C3.1", "Cantor family k=1..%d: two generation routes agree, "
          "|T_k| = 2^k - 1, T_k ⊆ [1, 3^k - 1], 3-AP-free by FULL "
          "pair-midpoint scan (all k) + independent (a,d)-scan (k<=8)"
          % kmax, ok,
          "hence r_3(3^k - 1) >= 2^k - 1 for k=1..%d (exact-table tie-ins:"
          " %s)" % (kmax, "; ".join(tiein) if tiein else "none"))

    # negative control: the ternary-{1,2} family MUST be rejected
    badT = set(v for v in range(1, 3 ** 2) if all(d in (1, 2)
                                                  for d in tern_digits(v)))
    got, wit = kap_scan(badT, 3, 3 ** 2 - 1)
    check("C3.2", "negative control: ternary-{1,2} family (k=2) REJECTED "
          "as 3-AP-containing (witness AP %s)" % (wit,),
          got and wit is not None,
          "family=%s" % sorted(badT))
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C4 the block upper bound torture
# ---------------------------------------------------------------------------

def section_c4(chal, sol, R3, W3, tables):
    print("[C4] BLOCK UPPER BOUND |S| <= (k-1)*floor(N/k) + (N mod k), "
          "k=3..6, N=1..60", flush=True)
    ps = chal["comparator_parameter_space"]["block_upper_envelope"]
    NEXH = ps["exhaustive_N_max"]
    NTOP = ps["N_max"]
    ks = ps["k_values"]
    ok = True
    total_exh = 0
    tight_exh = 0
    rk_small = {}
    for k in ks:
        by = masks_by_element(NEXH, k)
        Rk, Wk = rk_mask_table(NEXH, k, by)
        rk_small[k] = Rk
        for N in range(1, NEXH + 1):
            bb = block_rhs(N, k)
            total_exh += 1
            if Rk[N] > bb:
                ok = False
                info("EXHAUSTIVE VIOLATION k=%d N=%d: %d > %d"
                     % (k, N, Rk[N], bb))
            elif Rk[N] == bb:
                tight_exh += 1
            if not valid_witness(Wk[N], N, k):
                ok = False
                info("k=%d N=%d witness invalid" % (k, N))
        info("k=%d exhaustive N<=%d: R_k=%s (tight %d/%d)"
             % (k, NEXH, Rk[1:], sum(1 for N in range(1, NEXH + 1)
                                     if Rk[N] == block_rhs(N, k)), NEXH))
    check("C4.1", "EXHAUSTIVE N<=%d, k=3..6: every maximum k-AP-free size "
          "obeys the block bound (%d (k,N) points, %d tight, all maximum "
          "witnesses re-validated)" % (NEXH, total_exh, tight_exh),
          ok and total_exh == 4 * NEXH)

    # cross-engine: the k=3 mask-engine table must equal the C1 pair-ban
    # table (and hence the solution claim) on N <= NEXH
    cross = all(rk_small[3][N] == R3[N] for N in range(1, NEXH + 1))
    check("C4.2", "cross-engine k=3 N<=%d: mask-engine == pair-ban engine "
          "== solution R3-TABLE" % NEXH, cross)

    # r_3 maximum witnesses N=17..30 tortured against the k=3 bound
    ok = True
    for N in range(NEXH + 1, 31):
        if len(W3[N]) > block_rhs(N, 3):
            ok = False
            info("r_3 witness N=%d size %d exceeds block bound %d"
                 % (N, len(W3[N]), block_rhs(N, 3)))
    check("C4.3", "r_3 maximum witnesses N=%d..30 obey the k=3 block bound"
          % (NEXH + 1), ok)

    # randomized + structured torture, N = 17..60
    import random
    rng = random.Random(SEED)
    n_sets = 0
    n_apfree = 0
    viol = 0
    tight = 0
    ok = True
    for N in range(NEXH + 1, NTOP + 1):
        for k in ks:
            bb = block_rhs(N, k)
            by = masks_by_element(N, k)
            cands = []
            for _ in range(8):
                order = list(range(1, N + 1))
                rng.shuffle(order)
                cands.append(greedy_from_order(order, by))
            cands.append(greedy_from_order(list(range(1, N + 1)), by))
            cands.append(greedy_from_order(list(range(N, 0, -1)), by))
            for _ in range(3):
                p = rng.uniform(0.75, 0.97)
                S = set(v for v in range(1, N + 1) if rng.random() < p)
                cands.append(sorted(sieve_to_apfree(S, N, k, rng)))
            for r in range(k):
                base = set(v for v in range(1, N + 1) if v % k != r % k)
                cands.append(sorted(sieve_to_apfree(base, N, k, rng)))
            if k == 3:
                for kk in (3, 4):
                    T = sorted(cantor_gen_product(kk) - {0})
                    if T and T[-1] <= N:
                        cands.append(T)
            for S in cands:
                n_sets += 1
                Sset = set(S)
                if not kap_free(Sset, k, N):
                    ok = False
                    info("construction NOT k-AP-free (k=%d N=%d): %s"
                         % (k, N, sorted(S)))
                    continue
                n_apfree += 1
                if len(Sset) > bb:
                    viol += 1
                    ok = False
                    info("TORTURE VIOLATION k=%d N=%d: AP-free size %d > "
                         "bound %d: %s" % (k, N, len(Sset), bb,
                                           sorted(Sset)))
                elif len(Sset) == bb:
                    tight += 1
    check("C4.4", "TORTURE N=%d..%d, k=3..6: %d constructions, %d "
          "independently re-validated k-AP-free, %d bound violations "
          "(tight achieved %d times)" % (NEXH + 1, NTOP, n_sets, n_apfree,
                                         viol, tight),
          ok and viol == 0 and n_sets == n_apfree)

    # negative control A: crippled bound (rhs - 1) MUST trigger
    cripple = sum(1 for N in range(1, NEXH + 1)
                  if rk_small[5][N] > block_rhs(N, 5) - 1)
    check("C4.5", "negative control: crippled (rhs-1) block bound at k=5 "
          "correctly FLAGGED at %d/%d points N<=16" % (cripple, NEXH),
          cripple > 0)

    # negative control B: an AP-containing witness MUST be rejected
    badS = set(range(1, 7))  # contains (1,2,3,4,5,6) d=1 6-AP and 3-APs
    got6, _ = kap_scan(badS, 6, 6)
    got3, _ = kap_scan(badS, 3, 6)
    check("C4.6", "negative control: AP-containing witness {1..6} "
          "REJECTED (6-AP detected=%s, 3-AP detected=%s)" % (got6, got3),
          got6 and got3)
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C5 the k=2 edge
# ---------------------------------------------------------------------------

def section_c5(chal, sol):
    print("[C5] k=2 EDGE: r_2(1)=1, r_2(N)=1 for N>=2", flush=True)
    ok = True
    for N in range(1, 13):
        b, _ = brute_rk(N, 2)
        if b != 1:
            ok = False
            info("brute r_2(%d) = %d != 1" % (N, b))
    check("C5.1", "2^N brute force N<=12: r_2(N) = 1 everywhere", ok)

    pairs = 0
    ok = True
    for a in range(1, 31):
        for b in range(a + 1, 31):
            got, wit = kap_scan({a, b}, 2, b)
            if not got:
                ok = False
                info("pair {%d,%d} not detected as 2-AP" % (a, b))
            pairs += 1
    check("C5.2", "exhaustive %d-pair scan N<=30: every pair {a<b} is a "
          "non-trivial 2-AP (d = b-a >= 1) — no 2-AP-free set has size >= 2"
          % pairs, ok and pairs == 435)

    ok = all(kap_free({1}, 2, N) for N in range(1, 31))
    check("C5.3", "witness [1] is 2-AP-free inside [1,N] for all N=1..30 "
          "— hence r_2(N) >= 1, and with C5.2, r_2(N) = 1 (N>=2); "
          "r_2(1) = 1 by C5.1", ok)
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C6 context shadows (machine-checkable parts of the DeepMind/SOTA block)
# ---------------------------------------------------------------------------

def section_c6(chal, sol, R3):
    print("[C6] CONTEXT SHADOWS (machine-checkable parts of the DeepMind/"
          "SOTA context block — everything else is labeled context-only)",
          flush=True)
    # cap-set record arithmetic sanity + honest distinction
    ok = (512 == 2 ** 9 and 3 ** 8 == 6561 and 2 ** 8 - 1 == 255)
    d_cantor = 255 / 6561
    d_cap = 512 / 6561
    check("C6.1", "cap-set record arithmetic sanity: FunSearch cap set = "
          "512 = 2^9 points in F_3^8 (|F_3^8| = 3^8 = 6561, density "
          "%.4f); integer-interval Cantor T_8 = 2^8-1 = 255 points in "
          "[1,6560] (density %.4f) — related ternary-digit constructions, "
          "DISTINCT problems (F_3^n affine vs [1,N] interval), no "
          "comparability claimed" % (d_cap, d_cantor), ok)

    # honest gap map: r_3(N)/N vs the certified block envelope N<=30
    ok = True
    worst = 0.0
    for N in range(1, 31):
        r = R3[N]
        ub = block_rhs(N, 3)
        if r > ub:
            ok = False
            info("r_3(%d) = %d exceeds block envelope %d" % (N, r, ub))
        worst = max(worst, r / N)
    info("N=30: r_3/N = %.4f (12/30) vs block envelope %.4f (20/30) vs "
         "Cantor floor at N=26: %.4f (7/26)"
         % (R3[30] / 30, block_rhs(30, 3) / 30, 7 / 26))
    check("C6.2", "honest gap map N=1..30: r_3(N) <= 2*floor(N/3) + "
          "(N mod 3) everywhere; max observed density %.4f; the TRUE "
          "asymptotic density is known (context: Roth 1953) to be 0 — "
          "the #142 asymptotic itself stays OPEN" % worst, ok)

    # monotonicity shadow vs the k=2 edge: r_2(N) <= r_3(N)
    ok = all(1 <= R3[N] for N in range(1, 31))
    check("C6.3", "k=2 edge sits below the r_3 table (r_2(N)=1 <= "
          "r_3(N), N=1..30) — consistent with the mono law starting at "
          "k=2", ok)
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C7 honest-label audit
# ---------------------------------------------------------------------------

def section_c7(sol):
    print("[C7] HONEST-LABEL AUDIT (campaign law 8)", flush=True)
    labels_ok = all(str(c.get("label", "")).strip() for c in sol["claims"])
    check("C7.1", "every solution claim carries a nonempty exact label",
          labels_ok)

    scope = [c for c in sol["claims"] if c["id"] == "OPEN-SCOPE"]
    ok = bool(scope) and "OPEN for every k >= 3" in scope[0]["statement"]
    check("C7.2", "OPEN-SCOPE declaration present: the asymptotic formula "
          "is declared OPEN for every k >= 3 (the $10000 target is NOT "
          "claimed)", ok)

    # no claim may assert a closed asymptotic formula
    bad = []
    for c in sol["claims"]:
        st = c["statement"].lower()
        if c["id"] != "OPEN-SCOPE" and "asymptotic formula" in st \
                and "not" not in st and "open" not in st:
            bad.append(c["id"])
    check("C7.3", "no claim asserts a closed asymptotic formula (checked "
          "all claim statements)", not bad, "offenders=%s" % bad)

    lab = {c["id"]: c["label"] for c in sol["claims"]}
    ok = ("EXACT TABLE" in lab["R3-TABLE"]
          and "EXACT TABLE" in lab["R4-TABLE"]
          and "EXACT TABLE" in lab["R5-TABLE"]
          and "WITNESS" in lab["CANTOR-LOWER"]
          and "ENVELOPE" in lab["BLOCK-UPPER"]
          and "EDGE" in lab["K2-EDGE"]
          and "MONOTONICITY" in lab["MONO-LAW"]
          and "OPEN-SCOPE" in lab["OPEN-SCOPE"])
    check("C7.4", "label vocabulary exact: EXACT TABLE x3, WITNESS "
          "lower-bound, ENVELOPE upper-bound, EDGE, MONOTONICITY, "
          "OPEN-SCOPE", ok)
    print("    %s" % stamp(), flush=True)


# ---------------------------------------------------------------------------
# §C8 final gate
# ---------------------------------------------------------------------------

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    chal = load_json(os.path.join(here, "challenge.json"))
    sol = load_json(os.path.join(here, "solution.json"))

    section_c0(chal, sol)
    if not Z3_OK:
        print("FATAL: z3 is REQUIRED for the dual-certificate methodology "
              "(no evaluation, no green — DeepMind evaluator discipline)",
              flush=True)
        print("COMPARATOR_142_RED", flush=True)
        sys.exit(1)
    R3, W3 = section_c1(chal, sol)
    tables = section_c2(chal, sol, R3)
    section_c3(chal, sol, R3)
    section_c4(chal, sol, R3, W3, tables)
    section_c5(chal, sol)
    section_c6(chal, sol, R3)
    section_c7(sol)

    print("=" * 76, flush=True)
    print("[C8] FINAL VERDICT", flush=True)
    print("  checks passed: %d | checks failed: %d | criticals: %d"
          % (CHECKS[0], CHECKS[1], len(CRITICALS)), flush=True)
    print("  CERTIFIED: r_3 table N=1..30 (3 methods) | r_4, r_5 tables "
          "N=1..20 (2 methods) | Cantor lower-bound family k=1..10 | "
          "block upper bound k=3..6 N=1..60 | r_2 edge | monotonicity "
          "shadows | honest labels + open scope", flush=True)
    print("  NOT CERTIFIED (open): the #142 asymptotic formula for every "
          "k >= 3 — exactly as the solution's OPEN-SCOPE label declares",
          flush=True)
    print("  comparator wall time: %s" % stamp(), flush=True)
    if CRITICALS:
        print("COMPARATOR_142_RED (CRITICAL — disagreement with "
              "solution.json)", flush=True)
        for c in CRITICALS:
            print("  " + c, flush=True)
        sys.exit(2)
    if FAILURES or CHECKS[1] > 0:
        print("COMPARATOR_142_RED (%d failure lines)" % len(FAILURES),
              flush=True)
        for f in FAILURES:
            print("  " + f, flush=True)
        sys.exit(1)
    print("COMPARATOR_142_GREEN=1", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
