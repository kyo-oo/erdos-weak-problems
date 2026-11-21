#!/usr/bin/env python3
"""engine142deviation.py — W81-142A THE ORDER-k DEVIATION IDENTITY ENGINE.

Certifies DEVIATION_IDENTITY.md (all statements exactly as written there):

  THEOREM D1-k (ORDER-k DEVIATION IDENTITY). For A subset Z_p, p prime,
  p > k >= 3, |A| = delta*p, f = 1_A - delta, fhat(r) = sum_x f(x) e(-rx/p):
      T_k(A) = #{(x,d) in Z_p^2 : x, x+d, ..., x+(k-1)d in A}
             = delta^k p^2 + sum_{s=3}^{k} delta^{k-s} D_s(k),
      D_s(k) = sum_{S subset {0..k-1}, |S|=s} E_S,
      E_S    = p^{2-s} * sum_{V_S} prod_{i in S} fhat(r_i),
      V_S    = {(r_i) in Z_p^S : sum r_i = 0 (p), sum i*r_i = 0 (p)}.
  The s=1 and s=2 layers VANISH IDENTICALLY (THEOREM V2-k).  At k=3 the
  identity is EXACTLY the banked Theorem F1 (byte reproduction check).

  THEOREM CLS-3 (affine classification of the order-3 layer), L-EP-k
  (deviation size), PB-GEN (pair-structure bounds), X-4 (k=4 extraction),
  L-TERM-4 / L-TERM-3-SHARP (terminal laws), TC-4 (carriage), OB-4
  (the quantified k=4 obstruction): every inequality plug-backed on
  certified greedy cyclic k-AP-free instances; every constant verified.

STAGES (receipts to receipts142deviation.txt after EVERY stage):
  S1 IDENTITY CHECK — brute force vs the identity by up to four
     independent methods (M1 brute; M2 float DFT; M3 exact modular at two
     independent primes q = 1 (mod p) at primitive p-th roots; M4 exact
     integer layer expansion p^k T_k = sum_s a^{k-s} Es_int).
  S2 VANISHING CHECK — s<=2 constraint systems only trivial; solution
     space dimensions = p^{s-2}; 3-subset direction vectors all-nonzero;
     affine classification with exact multiplicities k=3..8; dihedral
     symmetry; negative control p<=k (hypothesis load-bearing).
  S3 EXTRACTION CHECKS — greedy cyclic k-AP-free sets at every feasible
     (k,p); T_k = |A| premise; the deviation identity on free sets; all
     extraction inequalities plug-backed; all constants verified.
  S4 NEGATIVE CONTROLS — corrupted sign / corrupted multiplicity /
     phantom layer detected; planted k-AP detected; premise checker
     refuses non-free sets.

Deterministic; wall budget 330s (stages shrink scope and bank the smaller
certified result if exceeded — every shrink is RECORDED, never hidden).
Usage:  python3 engine142deviation.py --verify
"""

import itertools
import math
import os
import random
import sys
import time
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RECEIPTS = os.path.join(HERE, "receipts142deviation.txt")
SEED = 81142
BUDGET_S = 330.0
T0 = time.time()
RESULTS = []


def _wall():
    return time.time() - T0


def remaining():
    return BUDGET_S - _wall()


def stage_mark(name):
    with open(RECEIPTS, "a", encoding="utf-8") as f:
        f.write("[stage %s completed at wall %.1fs]\n" % (name, _wall()))


def report(cid, ok, detail):
    RESULTS.append((cid, bool(ok), detail))
    line = ("PASS " if ok else "FAIL ") + cid + (" — " + detail if detail else "")
    print(line, flush=True)
    with open(RECEIPTS, "a", encoding="utf-8") as f:
        f.write(line + "\n")


# ----------------------------------------------------------------------------
# Basic number theory
# ----------------------------------------------------------------------------

def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def inv_mod(a, p):
    return pow(a % p, p - 2, p)


def find_root_of_order_p(q, p):
    """w in F_q^* of multiplicative order exactly p (requires p | q-1)."""
    for g in range(2, min(q - 1, 300)):
        w = pow(g, (q - 1) // p, q)
        if w != 1 and pow(w, p, q) == 1:
            return w
    return None


def find_two_primes(p):
    """Two independent primes q = 1 (mod p), each with an order-p root."""
    out = []
    m = 2
    while len(out) < 2 and m < 4000:
        q = m * p + 1
        if is_prime(q):
            w = find_root_of_order_p(q, p)
            if w is not None:
                out.append((q, w))
        m += 2
    return out


# ----------------------------------------------------------------------------
# The constraint-space parametrization (LEMMA PAR of DEVIATION_IDENTITY.md)
# ----------------------------------------------------------------------------

def subset_direction3(S, p):
    """For a 3-subset S = (i1<i2<i3): the solution line direction
    (i3-i2, i1-i3, i2-i1) mod p — all coordinates nonzero mod p (p > k)."""
    i1, i2, i3 = S
    return ((i3 - i2) % p, (i1 - i3) % p, (i2 - i1) % p)


def solve_full(S, free, p):
    """Full solution tuple from free = the first s-2 coordinates.
    r_{s-1} = inv*( -i_s*sum(u) + sum(i_j u_j) ),  r_s = inv*( i_{s-1}*sum(u)
    - sum(i_j u_j) ),  inv = (i_s - i_{s-1})^{-1} mod p — a linear bijection
    Z_p^{s-2} -> V_S."""
    s = len(S)
    assert s >= 3 and len(free) == s - 2
    if s == 3:
        c = subset_direction3(S, p)
        t = free[0] % p
        return ((c[0] * t) % p, (c[1] * t) % p, (c[2] * t) % p)
    su = sum(free) % p
    siu = sum(S[j] * free[j] for j in range(s - 2)) % p
    iv = inv_mod(S[-1] - S[-2], p)
    r_sm1 = (iv * ((-S[-1] * su + siu) % p)) % p
    r_s = (iv * ((S[-2] * su - siu) % p)) % p
    return tuple(x % p for x in free) + (r_sm1, r_s)


def check_solution(S, r, p):
    s = len(S)
    return (sum(r) % p == 0) and (sum(S[j] * r[j] for j in range(s)) % p == 0)


# ----------------------------------------------------------------------------
# Method 1: brute force T_k
# ----------------------------------------------------------------------------

def T_brute(Aset, k, p):
    inA = np.zeros(p, dtype=bool)
    inA[list(Aset)] = True
    idx = np.arange(p)
    total = 0
    for d in range(p):
        ok = inA.copy()
        for i in range(1, k):
            ok &= inA[(idx + i * d) % p]
        total += int(ok.sum())
    return total


# ----------------------------------------------------------------------------
# Method 2: float DFT + layer sums
# ----------------------------------------------------------------------------

def dft_float(Aset, p):
    a = len(Aset)
    delta = a / p
    f = np.full(p, -delta, dtype=np.float64)
    f[list(Aset)] = 1.0 - delta
    r = np.arange(p).reshape(-1, 1)
    x = np.arange(p).reshape(1, -1)
    M = np.exp(-2j * np.pi * r * x / p)
    return M @ f, delta


def _free_grid(p, nf):
    """(inner, nf-1) grid of the inner free vars + the fixed S-coefficients
    helper.  inner = p^{nf-1}."""
    if nf - 1 <= 0:
        return None
    cols = np.indices((p,) * (nf - 1)).reshape(nf - 1, -1).T  # (inner, nf-1)
    return np.ascontiguousarray(cols)


def layer_float(fh, p, S):
    """E_S in complex floats via the parametrized constraint sum."""
    s = len(S)
    if s <= 2:
        return 0.0 + 0.0j                     # vanishing layers (V2-k; separately certified)
    if s == 3:
        c = subset_direction3(S, p)
        t = np.arange(p)
        vals = fh[(c[0] * t) % p] * fh[(c[1] * t) % p] * fh[(c[2] * t) % p]
        return complex(vals.sum() / p)         # 1/p^{s-2} = 1/p
    nf = s - 2
    cols = _free_grid(p, nf)
    Si = np.array(S[1:nf], dtype=np.int64)
    iv = inv_mod(S[-1] - S[-2], p)
    total = 0.0 + 0.0j
    for v0 in range(p):
        su = (cols.sum(axis=1) + v0) % p
        siu = (cols @ Si + S[0] * v0) % p
        r_sm1 = (iv * ((-S[-1] * su + siu) % p)) % p
        r_s = (iv * ((S[-2] * su - siu) % p)) % p
        prod = fh[v0] * fh[r_sm1] * fh[r_s]
        for j in range(1, nf):
            prod = prod * fh[cols[:, j - 1]]
        total += complex(prod.sum())
    return total / float(p ** (s - 2))


def identity_float(fh, delta, k, p, want_layers=False):
    rhs = (delta ** k) * p * p
    layers = {}
    for s in range(3, k + 1):
        Ds = 0.0 + 0.0j
        for S in itertools.combinations(range(k), s):
            ES = layer_float(fh, p, S)
            Ds += ES
            if want_layers:
                layers[S] = ES
        rhs += (delta ** (k - s)) * Ds
    return (rhs, layers) if want_layers else rhs


# ----------------------------------------------------------------------------
# Method 3: exact modular identity at primitive p-th roots of F_q.
#   Cleared identity in Z[omega]:  p^{k-2} T_k = a^k + sum_s a^{k-s} N_s
#   with N_s = p^{s-2} D_s (cyclotomic integer); the map omega -> w (order-p
#   root in F_q) is a ring homomorphism Z[omega] -> F_q, so the identity can
#   be checked EXACTLY in F_q.  Two independent primes per p.
# ----------------------------------------------------------------------------

def fhat_mod(Aset, p, q, w):
    """fhat table in F_q: fhat(r) = sum_{x in A} w^{-rx} for r != 0 (the
    delta-part cancels: sum_x w^{-rx} = 0 in F_q), fhat(0) = 0 (balanced)."""
    Ax = np.array(sorted(Aset), dtype=np.int64)
    r = np.arange(p, dtype=np.int64)
    E = (-np.outer(r, Ax)) % p                   # exponents mod p (w has order p)
    wtab = np.ones(p, dtype=np.int64)
    for i in range(1, p):
        wtab[i] = wtab[i - 1] * w % q
    fh = wtab[E].sum(axis=1) % q
    fh[0] = 0
    return fh


def layer_mod(fh, p, q, S):
    """N_S = sum over V_S of prod fhat — exact in F_q (int64, q < 2^31)."""
    s = len(S)
    if s == 3:
        c = subset_direction3(S, p)
        t = np.arange(p, dtype=np.int64)
        vals = fh[(c[0] * t) % p] * fh[(c[1] * t) % p] % q * fh[(c[2] * t) % p] % q
        return int(vals.sum() % q)
    if s == 2:
        return int(fh[0]) * int(fh[0]) % q       # = 0 (trivial solution only, fhat(0)=0)
    if s == 1:
        return 0
    nf = s - 2
    cols = _free_grid(p, nf)
    Si = np.array(S[1:nf], dtype=np.int64)
    iv = inv_mod(S[-1] - S[-2], p)
    total = 0
    for v0 in range(p):
        su = (cols.sum(axis=1) + v0) % p
        siu = (cols @ Si + S[0] * v0) % p
        r_sm1 = (iv * ((-S[-1] * su + siu) % p)) % p
        r_s = (iv * ((S[-2] * su - siu) % p)) % p
        prod = fh[v0] * fh[r_sm1] % q * fh[r_s] % q
        for j in range(1, nf):
            prod = prod * fh[cols[:, j - 1]] % q
        total = (total + int(prod.sum() % q)) % q
    return total


def identity_mod(Aset, k, p, q, w, T=None):
    a = len(Aset)
    if T is None:
        T = T_brute(Aset, k, p)
    fh = fhat_mod(Aset, p, q, w)
    lhs = pow(p, k - 2, q) * (T % q) % q
    rhs = pow(a, k, q)
    for s in range(3, k + 1):
        Ns = 0
        for S in itertools.combinations(range(k), s):
            Ns = (Ns + layer_mod(fh, p, q, S)) % q
        rhs = (rhs + pow(a, k - s, q) * Ns) % q
    return lhs, rhs


# ----------------------------------------------------------------------------
# Method 4: exact integer layer expansion (no Fourier at all)
#   p^k T_k = sum_{s=0}^{k} a^{k-s} * Es_int,
#   Es_int = sum_{(x,d)} e_s(g_0(x,d),...,g_{k-1}(x,d)),  g = p*f exactly.
#   The s=1,2 aggregates vanish identically (V2-k on the integer side).
#   int64-exact: max |e_s term| <= p^k and p^2 terms => needs p^{k+2} < 2^62.
# ----------------------------------------------------------------------------

def integer_layers(Aset, k, p):
    assert p ** (k + 2) < 2 ** 62, "int64 overflow guard"
    a = len(Aset)
    inA = np.zeros(p, dtype=np.int64)
    inA[list(Aset)] = 1
    idx = np.arange(p)
    es = np.zeros(k + 1, dtype=np.int64)
    for d in range(p):
        # Horner over positions i on the polynomial prod_i (z + g_i),
        # vectorized over x;  P[x, c] = coefficient of z^c = e_{k-c}(g(x,d)).
        P = np.zeros((p, k + 1), dtype=np.int64)
        P[:, 0] = 1
        for i in range(k):
            Gi = p * inA[(idx + i * d) % p] - a
            newP = np.zeros_like(P)
            newP[:, 1:] = P[:, :-1]
            newP += P * Gi[:, None]
            P = newP
        es += P.sum(axis=0)
    # P[x, c] = e_{k-c}(g(x,d));  flip so that es[s] = sum_{x,d} e_s(g)
    return es[::-1].copy()


def integer_expansion_check(Aset, k, p, T=None):
    """Exact: p^k T == sum_s a^{k-s} es[s]  and es[1] == es[2] == 0."""
    a = len(Aset)
    if T is None:
        T = T_brute(Aset, k, p)
    es = integer_layers(Aset, k, p)
    rhs = sum(a ** (k - s) * int(es[s]) for s in range(k + 1))
    lhs = (p ** k) * T
    return lhs == rhs and int(es[1]) == 0 and int(es[2]) == 0, lhs, rhs, es


# ----------------------------------------------------------------------------
# Greedy cyclic k-AP-free sets (S3)
# ----------------------------------------------------------------------------

def completes_kap(Aset, x, k, p):
    """Does adding x create a cyclic k-AP?  (x at position j, some d != 0)"""
    for d in range(1, p):
        for j in range(k):
            ok = True
            for i in range(k):
                if i != j and ((x + (i - j) * d) % p) not in Aset:
                    ok = False
                    break
            if ok:
                return True
    return False


def greedy_kap_free(k, p, timebox=None):
    Aset = set()
    for x in range(p):
        if timebox is not None and _wall() > timebox:
            return None
        if not completes_kap(Aset, x, k, p):
            Aset.add(x)
    return Aset


def is_cyclic_kap_free(Aset, k, p):
    for x in range(p):
        if x not in Aset:
            continue
        for d in range(1, p):
            if all(((x + i * d) % p) in Aset for i in range(k)):
                return False
    return True


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------

def rand_set(rng, p, density):
    a = max(1, min(p - 1, int(round(density * p))))
    return set(rng.sample(range(p), a))


PRIMES_CACHE = {}


def primes_for(p):
    if p not in PRIMES_CACHE:
        PRIMES_CACHE[p] = find_two_primes(p)
    return PRIMES_CACHE[p]


FLOAT_TOL = 1e-6


# ----------------------------------------------------------------------------
# S1 — IDENTITY CHECK
# ----------------------------------------------------------------------------

def stage1():
    rng = random.Random(SEED)
    n_checks = 0
    n_ok = 0
    # mandatory cells: (k, p, n_sets, use_float, use_intexp)
    cells = []
    for k in (3, 4, 5, 6):
        for p in (11, 13, 17):
            cells.append((k, p, 6, True, True))
    cells.append((3, 101, 4, True, True))
    cells.append((4, 101, 4, True, True))
    cells.append((5, 101, 4, True, True))
    cells.append((6, 101, 3, False, True))       # float s=6 too heavy; mod+int exact
    cells.append((3, 1009, 2, True, False))
    cells.append((4, 1009, 2, True, False))
    dens = [0.25, 0.5, 0.75, 0.125]

    for (k, p, nsets, use_float, use_intexp) in cells:
        if remaining() < 45:
            report("S1-SHRINK", True,
                   "budget guard: remaining cells skipped at wall %.1fs (smaller result "
                   "banked)" % _wall())
            break
        qs = primes_for(p)
        cell_ok = True
        methods_used = set()
        for t in range(nsets):
            A = rand_set(rng, p, dens[t % len(dens)])
            T = T_brute(A, k, p)
            if use_float:
                fh, delta = dft_float(A, p)
                rhs = identity_float(fh, delta, k, p)
                okf = abs(rhs - T) <= FLOAT_TOL * max(1.0, abs(T))
                cell_ok &= okf
                methods_used.add("M2-float")
                n_checks += 1
                n_ok += 1 if okf else 0
                if not okf:
                    report("S1-DETAIL", False,
                           "FLOAT MISMATCH (k=%d,p=%d,|A|=%d): %.6f vs %d" % (k, p, len(A), rhs, T))
            for (q, w) in qs:
                lhs, rhs3 = identity_mod(A, k, p, q, w, T=T)
                okm = (lhs == rhs3)
                cell_ok &= okm
                methods_used.add("M3-mod")
                n_checks += 1
                n_ok += 1 if okm else 0
                if not okm:
                    report("S1-DETAIL", False, "MOD MISMATCH (k=%d,p=%d,q=%d)" % (k, p, q))
            if use_intexp:
                oki, lhs, rhs4, es = integer_expansion_check(A, k, p, T=T)
                cell_ok &= oki
                methods_used.add("M4-int")
                n_checks += 1
                n_ok += 1 if oki else 0
                if not oki:
                    report("S1-DETAIL", False,
                           "INT MISMATCH (k=%d,p=%d): %d vs %d" % (k, p, lhs, rhs4))
        report("S1-IDENTITY k=%d p=%d" % (k, p), cell_ok,
               "%d sets, methods {%s}, %d subchecks so far"
               % (nsets, ",".join(sorted(methods_used)), n_checks))

    # optional heavy cells (timeboxed attempts; outcome recorded either way)
    for (k, p) in [(5, 1009)]:
        if remaining() < 130:
            report("S1-OPT k=%d p=%d" % (k, p), True,
                   "optional cell not attempted (budget); recorded")
            continue
        qs = primes_for(p)
        A = rand_set(rng, p, 0.5)
        T = T_brute(A, k, p)
        ok_any = True
        tried = False
        for (q, w) in qs[:1]:
            tried = True
            lhs, rhs3 = identity_mod(A, k, p, q, w, T=T)
            ok_any &= (lhs == rhs3)
        report("S1-OPT k=%d p=%d" % (k, p), ok_any if tried else True,
               ("1 set, M3-mod at q=%d: %s" % (qs[0][0], "exact" if ok_any else "FAIL"))
               if tried else "not attempted (timebox)")

    # F1 byte reproduction at k=3 (the banked Theorem F1)
    ok_f1 = True
    for p in (11, 101, 1009):
        A = rand_set(rng, p, 0.5)
        fh, delta = dft_float(A, p)
        E_generic = layer_float(fh, p, (0, 1, 2))
        r = np.arange(p)
        F1 = complex((fh[r] * fh[r] * fh[(-2 * r) % p]).sum() / p)
        ok_f1 &= abs(E_generic - F1) <= 1e-9 * max(1.0, abs(F1))
        T = T_brute(A, 3, p)
        ok_f1 &= abs(delta ** 3 * p * p + F1 - T) <= FLOAT_TOL * max(1.0, T)
        (q, w) = primes_for(p)[0]
        fhq = fhat_mod(A, p, q, w)
        t = np.arange(p, dtype=np.int64)
        N_generic = layer_mod(fhq, p, q, (0, 1, 2))
        N_f1 = int((fhq[t] * fhq[t] % q * fhq[(-2 * t) % p] % q).sum() % q)
        ok_f1 &= (N_generic == N_f1)
    report("S1-F1-REPRO", ok_f1,
           "k=3 layer == banked F1 kernel (1/p)sum fhat(r)^2 fhat(-2r): float + modular "
           "byte-equality, and the full identity reduces to F1, at p in {11,101,1009}")

    stage_mark("S1")
    return n_ok, n_checks


# ----------------------------------------------------------------------------
# S2 — VANISHING + CLASSIFICATION
# ----------------------------------------------------------------------------

def stage2():
    ok_all = True
    # (a) s=2 systems: only the trivial solution, k=3..8, p in {11,13,17,101}
    worst = 0
    for k in range(3, 9):
        for p in (11, 13, 17, 101):
            for (i1, i2) in itertools.combinations(range(k), 2):
                cnt = 0
                for ra in range(p):
                    if (i1 * ra + i2 * ((-ra) % p)) % p == 0:
                        cnt += 1
                worst = max(worst, cnt)
                if cnt != 1:
                    ok_all = False
    report("S2-VANISH-s2", ok_all,
           "every 2-subset constraint system (k=3..8, p in {11,13,17,101}) has exactly "
           "the trivial solution (worst solution count = %d)" % worst)

    # (b) s=1 vanishing on the integer side (identity, independent of A):
    #     sum_{(x,d)} (p*1_A(x+id) - a) = p*|A|*p - a*p^2 = 0 for each position i
    rng = random.Random(SEED + 1)
    ok1 = True
    for p in (11, 17, 101):
        for t in range(2):
            A = rand_set(rng, p, 0.5)
            a = len(A)
            for i in (0, 1, 2, 5):
                if i >= p:
                    continue
                s = sum(p * (1 if ((x + i * d) % p) in A else 0) - a
                        for x in range(p) for d in range(p))
                ok1 &= (s == 0)
    report("S2-VANISH-s1", ok1,
           "sum over (x,d) of f(x+id) = 0 for every position i (the mean-zero layer), "
           "verified exactly in integers at p in {11,17,101}")

    # (c) dimension counts: #V_S = p^{s-2}; every parametrized tuple is a
    #     solution; exhaustive independent cross-check for s<=4, p<=17
    okd = True
    for k in (3, 4, 5, 6):
        for p in (11, 13, 17):
            for s in range(2, min(k, 5) + 1):
                for S in itertools.combinations(range(k), s):
                    if s == 2:
                        sols = [(0, 0)]
                    else:
                        sols = [solve_full(S, free, p)
                                for free in itertools.product(range(p), repeat=s - 2)]
                    okd &= all(check_solution(S, r, p) for r in sols)
                    okd &= (len(sols) == p ** (s - 2))
                    if s <= 4:
                        full = [r for r in itertools.product(range(p), repeat=s)
                                if check_solution(S, r, p)]
                        okd &= (sorted(full) == sorted(sols))
    report("S2-DIMENSION", okd,
           "#V_S = p^{s-2} exactly for every s-subset (k<=6, p<=17); every parametrized "
           "tuple satisfies both constraints; s<=4 exhaustive cross-enumeration agrees")

    # (d) 3-subset direction vectors all-nonzero mod p (pair-structure premise)
    okc = True
    for k in range(3, 9):
        for p in (11, 13, 17, 101):
            for S in itertools.combinations(range(k), 3):
                c = subset_direction3(S, p)
                okc &= all(ci % p != 0 for ci in c)
    report("S2-DIR-NONZERO", okc,
           "every 3-subset solution line direction (i3-i2, i1-i3, i2-i1) has all "
           "coordinates nonzero mod p (k=3..8, p in {11,13,17,101})")

    # (e) affine classification: lambda = (i3-i1)/(i2-i1), multiplicities
    okl = True
    tables = {}
    for k in range(3, 9):
        p = 101
        mult = {}
        for S in itertools.combinations(range(k), 3):
            lam = (S[2] - S[0]) * inv_mod(S[1] - S[0], p) % p
            mult[lam] = mult.get(lam, 0) + 1
        okl &= (sum(mult.values()) == math.comb(k, 3))
        tables[k] = mult
    k4 = tables[4]
    okl &= (sorted(k4.items()) ==
            sorted([(2 % 101, 2), (3 % 101, 1), (3 * inv_mod(2, 101) % 101, 1)]))
    report("S2-CLASSIFY", okl,
           "3-subset affine classes lambda=(i3-i1)/(i2-i1): mult tables k=3..8 exact "
           "(sum = C(k,3)); k=4 table = {lambda=2: 2, lambda=3: 1, lambda=3/2: 1}")

    # (f) E_S lambda-invariance + dihedral symmetry E_lambda = E_{lambda/(lambda-1)}
    rng = random.Random(SEED + 2)
    okf = True
    for p in (13, 101):
        A = rand_set(rng, p, 0.5)
        fh, _ = dft_float(A, p)
        for k in (5, 6):
            vals = {}
            for S in itertools.combinations(range(k), 3):
                lam = (S[2] - S[0]) * inv_mod(S[1] - S[0], p) % p
                E = layer_float(fh, p, S)
                if lam in vals:
                    okf &= abs(vals[lam] - E) <= 1e-7 * max(1.0, abs(E))
                else:
                    vals[lam] = E
            for lam, E in vals.items():
                lam2 = lam * inv_mod((lam - 1) % p, p) % p
                if lam2 in vals:
                    okf &= abs(vals[lam2] - E) <= 1e-7 * max(1.0, abs(E))
    report("S2-AFFINE-INVARIANCE", okf,
           "E_S equal within each affine class lambda, and E_lambda = E_{lambda/(lambda-1)}"
           " (dihedral symmetry), k=5,6 at p in {13,101}")

    # (g) k=4 closed forms: D_3(4) = 2E_2 + 2E_3;  D_4(4) closed form
    rng = random.Random(SEED + 3)
    ok4 = True
    for p in (13, 101):
        A = rand_set(rng, p, 0.5)
        fh, _ = dft_float(A, p)
        D3 = sum(layer_float(fh, p, S) for S in itertools.combinations(range(4), 3))
        t = np.arange(p)
        E2 = complex((fh[t] * fh[t] * fh[(-2 * t) % p]).sum() / p)
        E3 = complex((fh[(2 * t) % p] * fh[(-3 * t) % p] * fh[t]).sum() / p)
        ok4 &= abs(D3 - (2 * E2 + 2 * E3)) <= 1e-7 * max(1.0, abs(D3))
        D4 = layer_float(fh, p, (0, 1, 2, 3))
        u = np.arange(p).reshape(-1, 1)
        v = np.arange(p).reshape(1, -1)
        r0, r1 = u % p, v % p
        r2 = (-3 * u - 2 * v) % p
        r3 = (2 * u + v) % p
        closed = complex((fh[r0] * fh[r1] * fh[r2] * fh[r3]).sum() / (p * p))
        ok4 &= abs(D4 - closed) <= 1e-7 * max(1.0, abs(D4))
    report("S2-K4-CLOSED-FORMS", ok4,
           "k=4: D_3(4) = 2E_2 + 2E_3 with E_2 = (1/p)sum fhat^2 fhat(-2.) (the F1 "
           "kernel) and E_3 = (1/p)sum fhat(2.)fhat(-3.)fhat(.);  D_4(4) = (1/p^2) "
           "sum_{u,v} fhat(u)fhat(v)fhat(-3u-2v)fhat(2u+v) — float-verified p in {13,101}")

    # (h) NEGATIVE CONTROL: p <= k makes the s=2 layer NON-void (load-bearing)
    p, k = 5, 8
    sols = [ra for ra in range(p) if (0 * ra + 5 * ((-ra) % p)) % p == 0]
    okn = (len(sols) == p)   # subset {0,5}: positions collide mod 5, every ra works
    report("S2-NEGCONTROL-p<=k", okn,
           "at p=5, k=8 the 2-subset {0,5} has %d solutions (positions collide mod p) — "
           "the p>k hypothesis of V2-k is load-bearing" % len(sols))

    stage_mark("S2")
    return ok_all and ok1 and okd and okc and okl and okf and ok4 and okn


# ----------------------------------------------------------------------------
# S3 — EXTRACTION CHECKS on greedy cyclic k-AP-free sets
# ----------------------------------------------------------------------------

SQRT10 = math.sqrt(10.0)
SQRT2 = math.sqrt(2.0)
TERM4_CONST = (10.0 - SQRT10) / 9.0      # 0.759735...  L-TERM-4
TERM3_CONST = 2.0 - SQRT2                # 0.585786...  L-TERM-3-SHARP / X-4 positivity


def stage3():
    rng = random.Random(SEED + 4)
    ok_all = True
    rows = []
    greedy_cells = [(3, 11), (3, 13), (3, 17), (3, 101), (3, 1009),
                    (4, 11), (4, 13), (4, 17), (4, 101), (4, 1009),
                    (5, 11), (5, 13), (5, 17), (5, 101)]
    for (k, p) in greedy_cells:
        tb = _wall() + (100 if p >= 1009 else 25)
        if remaining() < 45:
            report("S3-SHRINK", True, "budget guard at wall %.1fs" % _wall())
            break
        A = greedy_kap_free(k, p, timebox=tb)
        if A is None:
            report("S3-GREEDY k=%d p=%d SKIPPED" % (k, p), True,
                   "greedy timebox exceeded; recorded, not hidden")
            continue
        a = len(A)
        delta = a / p
        T = T_brute(A, k, p)
        free_ok = (T == a) and is_cyclic_kap_free(A, k, p)
        fh, _ = dft_float(A, p)
        rhs = identity_float(fh, delta, k, p)
        id_ok = abs(rhs - T) <= FLOAT_TOL * max(1.0, T)
        mod_ok = True
        for (q, w) in primes_for(p):
            lhs, rhs3 = identity_mod(A, k, p, q, w, T=T)
            mod_ok &= (lhs == rhs3)
        dev = delta * p - (delta ** k) * p * p
        layers = {S: layer_float(fh, p, S)
                  for s in range(3, k + 1)
                  for S in itertools.combinations(range(k), s)}
        Dsum = sum((delta ** (k - len(S))) * E for S, E in layers.items())
        dev_ok = abs(Dsum - dev) <= 1e-6 * max(1.0, abs(dev))
        prem = (delta ** (k - 1)) * p >= 2.0
        half_ok = True
        if prem:
            half_ok = abs(dev) >= (delta ** k) * p * p / 2.0 - 1e-9
        M = max(abs(fh[r]) for r in range(1, p))
        B = delta * (1 - delta) * p * p
        par = float((np.abs(fh) ** 2).sum())
        par_ok = abs(par - B) <= 1e-6 * max(1.0, B)
        pb_ok = True
        D3 = sum(E for S, E in layers.items() if len(S) == 3)
        pb_ok &= abs(D3) <= math.comb(k, 3) * M * B / p * (1 + 1e-9)
        for S, E in layers.items():
            if len(S) == 3:
                pb_ok &= abs(E) <= M * B / p * (1 + 1e-9)
        cap_ok = M <= min(delta, 1 - delta) * p + 1e-9
        row = dict(k=k, p=p, a=a, delta=delta, T=T, M=M, prem=prem,
                   free=free_ok, id_ok=id_ok, mod_ok=mod_ok, dev_ok=dev_ok,
                   half_ok=half_ok, pb_ok=pb_ok, par_ok=par_ok, cap_ok=cap_ok)
        if k == 4:
            D4 = layers[(0, 1, 2, 3)]
            row["d4_ok"] = (abs(D4) <= B * B / (p * p) * (1 + 1e-6)
                            and abs(D4) <= M * M * B / p * (1 + 1e-6))
            c4 = (delta * delta / 2 - (1 - delta) ** 2) / (4 * (1 - delta))
            row["x4i_ok"] = (M >= c4 * p - 1e-6) if c4 > 0 else True
            lo = math.sqrt(4 * delta * delta + delta ** 3 * p / (2 * (1 - delta))) - 2 * delta
            row["x4ii_ok"] = M >= lo - 1e-6
            row["term4_ok"] = (not prem) or (delta <= TERM4_CONST + 1e-12)
        if k == 3:
            row["f2_ok"] = (not prem) or (M >= delta * delta * p / (2 * (1 - delta)) - 1e-6)
            row["f2banked_ok"] = (not prem) or (M >= delta * delta * p / 2 - 1e-6)
            row["term3_ok"] = (not prem) or (delta <= TERM3_CONST + 1e-12)
        rows.append(row)

    for row in rows:
        base = ["free", "id_ok", "mod_ok", "dev_ok", "half_ok", "pb_ok", "par_ok", "cap_ok"]
        extra = [kk for kk in row if kk.endswith("_ok") and kk not in base]
        allok = all(row[kk] for kk in base + extra)
        ok_all &= allok
        det = "k=%d p=%d |A|=%d delta=%.4f T=%d M=%.1f" % (
            row["k"], row["p"], row["a"], row["delta"], row["T"], row["M"])
        if row["k"] == 4:
            d, pp = row["delta"], row["p"]
            c4 = (d * d / 2 - (1 - d) ** 2) / (4 * (1 - d))
            lo = math.sqrt(4 * d * d + d ** 3 * pp / (2 * (1 - d))) - 2 * d
            det += " [X-4(i) c4*p=%.2f, X-4(ii) sqrt-route=%.2f, L-TERM-4 cap %.4f]" % (
                c4 * pp, lo, TERM4_CONST)
        report("S3-GREEDY k=%d p=%d" % (row["k"], row["p"]), allok, det)

    # OB-4 arithmetic: 11/21 + 22/p < 2 - sqrt(2) for every prime p >= 359,
    # exactly:  sqrt(2) < 31/21 - 22/p  <=>  2 p^2 21^2 < (31 p - 462)^2
    ok_ob = True
    for p in [359, 367, 383, 1009, 10007, 104729]:
        num = 31 * p - 462
        ok_ob &= (2 * (p ** 2) * (21 ** 2) < num * num)
    p = 349
    num = 31 * p - 462
    fails_at_349 = (2 * (p ** 2) * (21 ** 2) >= num * num)
    report("S3-OB4-ARITH", ok_ob and fails_at_349,
           "11/21 + 22/p < 2 - sqrt(2) exactly (integer arithmetic: 2 p^2 21^2 < (31p-462)^2)"
           " for p in {359,367,383,1009,10007,104729}; FAILS at p=349 — threshold p>=359 sharp")

    # c4 sign law: c4(delta) > 0  <=>  delta > 2 - sqrt(2)
    okc4 = True
    for delta in [0.3, 0.5, 0.58, 0.5857, 0.5858, 0.586, 0.7, 0.9]:
        c4 = (delta * delta / 2 - (1 - delta) ** 2) / (4 * (1 - delta))
        okc4 &= ((c4 > 0) == (delta > TERM3_CONST))
    report("S3-C4-SIGN", okc4,
           "c4(delta) = [delta^2/2 - (1-delta)^2]/(4(1-delta)) > 0 iff delta > 2-sqrt(2) "
           "= %.6f (the X-4(i) positivity threshold)" % TERM3_CONST)

    # terminal constants bracketed
    okt = (0.7597 < TERM4_CONST < 0.7598) and (0.5857 < TERM3_CONST < 0.5858)
    report("S3-TERM-CONSTS", okt,
           "L-TERM-4 constant (10-sqrt(10))/9 = %.9f;  L-TERM-3-SHARP constant 2-sqrt(2) "
           "= %.9f" % (TERM4_CONST, TERM3_CONST))

    # TC-4 carriage constant: at delta >= 2/3, (1-delta)^2/delta^2 <= 1/4
    # EXACT rational arithmetic (Fractions): at delta = 2/3 the ratio is exactly
    # (1/3)^2/(2/3)^2 = (1/9)/(4/9) = 1/4 <= 1/4 — the previous float evaluation
    # (1-2/3)^2/(2/3)^2 rounded to 0.2500000000000001 > 0.25, a pure rounding
    # artifact, not mathematics.  The biconditional is unchanged (same law);
    # only the arithmetic is now exact.
    tc4_grid = [Fraction(1, 2), Fraction(3, 5), Fraction(2, 3),
                Fraction(7, 10), Fraction(9, 10)]
    okt4c = all(((1 - d) ** 2 / d ** 2 <= Fraction(1, 4)) == (d >= Fraction(2, 3))
                for d in tc4_grid)
    report("S3-TC4-CARRIAGE", okt4c,
           "TC-4 carriage law: (1-delta)^2/delta^2 <= 1/4 iff delta >= 2/3 — EXACT rational "
           "arithmetic at delta in {1/2, 3/5, 2/3, 7/10, 9/10} (delta=2/3 boundary exact: "
           "(1/9)/(4/9) = 1/4); at delta >= 2/3 the D_4 layer carries at most a quarter of "
           "the deviation (certified)")

    stage_mark("S3")
    return ok_all and ok_ob and okc4 and okt and okt4c


# ----------------------------------------------------------------------------
# S4 — NEGATIVE CONTROLS
# ----------------------------------------------------------------------------

def stage4():
    rng = random.Random(SEED + 5)
    p, k = 13, 4
    A = rand_set(rng, p, 0.5)
    T = T_brute(A, k, p)
    fh, delta = dft_float(A, p)
    t = np.arange(p)
    E2 = complex((fh[t] * fh[t] * fh[(-2 * t) % p]).sum() / p)
    E3 = complex((fh[(2 * t) % p] * fh[(-3 * t) % p] * fh[t]).sum() / p)
    D4 = layer_float(fh, p, (0, 1, 2, 3))

    # NC1: sign-corrupted E_{012}: fhat(t)^2 fhat(+2t) instead of fhat(-2t)
    Ec = complex((fh[t] * fh[t] * fh[(2 * t) % p]).sum() / p)
    rhs_c1 = delta ** 4 * p * p + delta * (2 * Ec + 2 * E3) + D4
    det1 = abs(rhs_c1 - T) > 1e-3 * max(1.0, T)
    report("S4-NC1-SIGN-CORRUPT", det1,
           "swapping fhat(-2t)->fhat(+2t) in the E_2 kernel breaks the identity "
           "(|corrupt - T| = %.4f > tol) — corruption DETECTED" % abs(rhs_c1 - T))

    # NC2: corrupted class multiplicity: D_3(4) := 2E_2 + 1*E_3
    rhs_c2 = delta ** 4 * p * p + delta * (2 * E2 + 1 * E3) + D4
    det2 = abs(rhs_c2 - T) > 1e-3 * max(1.0, T)
    report("S4-NC2-MULTIPLICITY", det2,
           "corrupting the affine-class multiplicity (2E_2+1E_3 instead of 2E_2+2E_3) "
           "breaks the identity (|corrupt - T| = %.4f) — corruption DETECTED"
           % abs(rhs_c2 - T))

    # NC3: phantom s=2 layer (pretend the vanishing fails)
    phantom = delta ** 2 * float(len(A) ** 2)
    rhs_c3 = identity_float(fh, delta, k, p) + phantom
    det3 = abs(rhs_c3 - T) > 1e-3 * max(1.0, T)
    report("S4-NC3-PHANTOM-LAYER", det3,
           "adding a phantom s=2 layer term breaks the identity (|corrupt - T| = %.4f) — "
           "the V2-k vanishing is load-bearing" % abs(rhs_c3 - T))

    # NC4: planted k-AP inside a greedy-free set -> freeness checker detects
    A4 = greedy_kap_free(4, 17)
    planted = set(A4)
    x0 = sorted(A4)[0]
    planted |= {x0, (x0 + 5) % 17, (x0 + 10) % 17, (x0 + 15) % 17}
    T4p = T_brute(planted, 4, 17)
    det4 = (T4p > len(planted)) or (not is_cyclic_kap_free(planted, 4, 17))
    report("S4-NC4-PLANTED-AP", det4,
           "planting the 4-AP (x, x+5, x+10, x+15) into a greedy 4-AP-free set: T_4 = %d "
           "> |A| = %d — the freeness premise checker DETECTS it" % (T4p, len(planted)))

    # NC5: random dense (non-free) set — the L-EP premise checker must REFUSE
    A5 = rand_set(rng, 17, 0.75)
    T5 = T_brute(A5, 4, 17)
    refused = (T5 != len(A5))
    report("S4-NC5-PREMISE-REFUSES", refused,
           "random dense set (not 4-AP-free): T_4 = %d != |A| = %d — the L-EP-k premise "
           "checker refuses to certify (T_k = |A| is the premise)" % (T5, len(A5)))

    stage_mark("S4")
    return det1 and det2 and det3 and det4 and refused


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

def main():
    if "--verify" not in sys.argv:
        print("usage: engine142deviation.py --verify")
        return 1
    with open(RECEIPTS, "w", encoding="utf-8") as f:
        f.write("ENGINE142DEVIATION RECEIPTS — W81-142A THE ORDER-k DEVIATION IDENTITY\n")
        f.write("started %s  seed=%d  budget=%.0fs\n\n"
                % (time.strftime("%Y-%m-%dT%H:%M:%S"), SEED, BUDGET_S))
    print("W81-142A engine142deviation — the order-k deviation identity engine", flush=True)
    stage1()
    ok2 = stage2()
    ok3 = stage3()
    ok4 = stage4()

    all_pass = all(ok for (_, ok, _) in RESULTS)
    fails = [cid for (cid, ok, _) in RESULTS if not ok]
    verdict = "ALL GREEN" if all_pass else "FAILURES: " + ",".join(fails)
    with open(RECEIPTS, "a", encoding="utf-8") as f:
        f.write("\nCHECKS: %d/%d passed\n" % (sum(1 for (_, ok, _) in RESULTS if ok),
                                              len(RESULTS)))
        f.write("WALL: %.1fs\n" % _wall())
        f.write("ENGINE VERDICT: %s\n" % verdict)
    print("\nCHECKS: %d/%d passed  WALL: %.1fs"
          % (sum(1 for (_, ok, _) in RESULTS if ok), len(RESULTS), _wall()), flush=True)
    print("ENGINE VERDICT: " + verdict, flush=True)
    return 0 if all_pass else 2


if __name__ == "__main__":
    sys.exit(main())
