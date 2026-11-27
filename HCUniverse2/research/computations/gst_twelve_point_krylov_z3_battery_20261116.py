#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W2-C — GST twelve-cell Krylov spanning certificate: Z3 5.4.1 certification battery.

Target of certification (the numeric core of the GST hypothesis program):
    The Krylov matrix K of the fold-word operator T (Twave = F1 = U + J + M,
    b = 1) acting on the native seed has
        det K = -1,149,656,584,000 != 0,
    so the twelve orbit vectors {T^i seed : i = 0..11} span the 12-dimensional
    Hodge fiber (WaveSignal12 = TwelveCell -> Q).  This is the rank-12
    cyclicity behind NativeGSTSingleFoldOrbitLaw's first live discharge and
    the spanning law `span_range_worldOrbit_eq_top`.

CANONICAL DATA (extracted from the repo, with file:line citations):

  * TwelveCell = Fin 4 x Fin 3            GSTHypothesisComplete.lean:503
  * nullCell = (0,0), maxCell = (3,2)     GSTHypothesisComplete.lean:506,509
  * shuffleCell (c,d) = ((c+4d)/3, (c+4d)%3)   GSTHypothesisComplete.lean:512-517
  * mirrorCell (c,d) = (3-c, 2-d)              GSTHypothesisComplete.lean:521-527
  * cmSign s = +1 if c+4d in {0,1,3,4,5,9} else -1  GSTHypothesisComplete.lean:531-534
  * U12 u s = u (shuffleCell s)            GSTHypothesisComplete.lean:541-542
  * J12 u s = cmSign s * u (mirrorCell s)  GSTHypothesisComplete.lean:545-546
  * M12 src u s = src s * u s              GSTHypothesisComplete.lean:551-552
  * seed12 = e_(0,0) + e_(0,1)             GSTHypothesisComplete.lean:555-558
  * F12 src b u = U12 u + J12 u + b * M12 src u   GSTHypothesisComplete.lean:562-564
  * surviveI (the SURVIVE source)          GST2DMixedEmergence.lean:49-51
      surviveI C d = twoI d * twoI (midDigit C d)
                   + twoI (midDigit C d) * twoI (finalMicroDigit C d)
      with twoI:34, microOutput:9, highBit:11, lowBit:12, midDigit:14,
      finalMicroDigit:16-17.
  * ownerSource s = surviveI s.1 s.2       GSTHypothesisSpanningProof.lean:67-68
      certified cell values (decided):  GSTHypothesisSpanningProof.lean:73-84
      (0,0)=0 (0,1)=0 (0,2)=0 (1,0)=0 (1,1)=1 (1,2)=0
      (2,0)=0 (2,1)=0 (2,2)=1 (3,0)=0 (3,1)=0 (3,2)=2
      the two cell certificates:
        ownerSource_null : ownerSource nullCell = 0   (:70)
        ownerSource_max  : ownerSource maxCell  = 2   (:71)
  * N12 = F12 ownerSource 1 (Module.End)   GSTHypothesisSpanningProof.lean:117-120
      N12_val: N12 u s = u (shuffleCell s) + cmSign s * u (mirrorCell s)
                          + ownerSource s * u s        (:123-127)
  * worldOrbit 0 = seed12, worldOrbit (n+1) = N12 (worldOrbit n)  (:138-141)
  * Kvec : Fin 12 -> WaveSignal12, the exact Krylov table  (:147-161)
  * the eleven Krylov step lemmas N12_Kvec_step_0..10 :
      N12 (Kvec k) = Kvec (k+1)                     (:203-333)
  * orbit_val_0..11 : worldOrbit k = Kvec k         (:336-391)
  * certRowOf + eCell_eq_cert (the Gauss-Jordan spanning certificate) (:420-444)
  * span_range_worldOrbit_eq_top : span Q (range worldOrbit) = Topp  (:463-468)
  * Twave : Matrix (Fin 12) (Fin 12) Q — the explicit operator matrix,
      Twave i j = N12 (e_j) i, carry-major index i = 3*c + d
                                              GSTHypothesisSpanningCompilerFace.lean:63-77
      Twave_bridge                                            (:81-93)
  * coordSeed = (1,1,0,...,0)                               (:98)
  * C 0 = coordSeed, C (n+1) = Twave.mulVec (C n)           (:101-106)
  * Cvec : the coordinate Krylov table                        (:109-123)
  * orbitMatrix : Matrix Cell (Fin 12) Q := fun s k => orbit k.val s
      (rows = cells, columns = Krylov steps)
                                              GSTGraphV2CMWaveFusion.lean:175-176
  * the certified determinant constant -1149656584000
                                              GSTHypothesisSpanningProof.lean:33-35

KRYLOV CONVENTION (extracted): K[i][j] = (T^j * seed)[i] — column j of K is
the j-th orbit vector (orbitMatrix s k = orbit k s; C (n+1) = Twave.mulVec
(C n)).  Rows are the twelve cells in carry-major order (0,0),(0,1),(0,2),
(1,0),...,(3,2).  det is invariant under transposition, so the determinant
value certifies the spanning in either orientation.

BATTERY:
  Method A — exact integer certificate: fraction-free Bareiss elimination on
             the 12x12 integer Krylov matrix (cross-checked by an independent
             Fraction-arithmetic Gaussian elimination and by Bareiss on K^T).
  Method B — Z3 direct: (i) kernel-UNSAT over Z: NOT exists c != 0 with
             K^T c = 0 (twelve linear equations + a 12-way nonzero
             disjunction) — this certifies full rank / spanning; (ii) 144 Z3
             validity queries for adj(K)*K = det*I and 144 for K*adj(K) =
             det*I, where adj(K) is computed exactly in Python (integer
             cofactors) and each equation is re-verified by Z3 as an integer
             arithmetic identity with the dot products built as Z3 terms.
  Method C — modular cross-checks: det mod p by GF(p) elimination for twelve
             odd primes p in {3,5,7,11,13,17,19,23,29,31,37,41} (all must
             equal -1149656584000 mod p), plus Z3 mod-p kernel-UNSAT queries
             for four primes with det =/= 0 mod p.  NOTE: the canonical
             determinant is -(2^6 * 5^3 * 149^2 * 6473), so p = 5 DIVIDES it
             (v_5(det) = 3): for p = 5 the mod-p kernel is legitimately
             nontrivial.  The battery therefore (a) selects the Z3
             kernel-UNSAT primes among those with det mod p != 0
             ({3,7,11,13}), and (b) turns the p = 5 fact into a positive
             certificate: it exhibits a nonzero mod-5 annihilator of K^T and
             Z3-verifies the witness (expected verdict sat), which CERTIFIES
             5 | det rather than papering over it.
  Method D — independent recomputation of T^i * seed by three routes
             (Twave matvec iteration; the semantic operator N12 applied as a
             function; matrix powers by repeated squaring) and elementwise
             comparison with BOTH Lean Krylov tables (Kvec, Cvec), the seed
             tables, the ownerSource table, and the Twave matrix itself
             (Twave_bridge data).  Also verifies the eleven Lean step lemmas'
             data (N12 (Kvec k) = Kvec (k+1)) and the full Gauss-Jordan
             certificate certRowOf (certRow * K^T = I, exact Fractions).

All numbers are exact (Python ints / Fractions).  No numpy.  Z3 5.4.1 only.
"""

from __future__ import annotations

import datetime
import json
import os
import re
import sys
import time
from fractions import Fraction

import z3

# ----------------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------------

REPO = "/home/z/hc"
SPAN_FILE = os.path.join(REPO, "GSTHypothesisSpanningProof.lean")
FACE_FILE = os.path.join(REPO, "GSTHypothesisSpanningCompilerFace.lean")
VERDICT_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "gst_twelve_point_krylov_z3_battery_20261116_VERDICT.json",
)

CANONICAL_DET = -1149656584000  # GSTHypothesisSpanningProof.lean:33-34

PRIMES_PY = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]  # 12 odd primes
PRIMES_Z3_COUNT = 4  # Z3 kernel-UNSAT primes: first primes with det mod p != 0

CELLS = [(c, d) for c in range(4) for d in range(3)]  # carry-major order
IDX = {(c, d): 3 * c + d for (c, d) in CELLS}  # the Fin 12 index of the face
N = 12

_z3_query_log = []  # (label, verdict-string) for every z3 check() call


def log(msg: str) -> None:
    print(msg, flush=True)


# ----------------------------------------------------------------------------
# §1 The semantic operator, rebuilt literally from the Lean definitions
# ----------------------------------------------------------------------------

def twoI(x: int) -> int:  # GST2DMixedEmergence.twoI :34
    return 1 if x == 2 else 0


def micro_output(a: int, d: int) -> int:  # microOutput :9
    return (a + 2 * d) % 3


def high_bit(C: int) -> int:  # highBit :11
    return C // 2


def low_bit(C: int) -> int:  # lowBit :12
    return C % 2


def mid_digit(C: int, d: int) -> int:  # midDigit :14
    return micro_output(high_bit(C), d)


def final_micro_digit(C: int, d: int) -> int:  # finalMicroDigit :16-17
    return micro_output(low_bit(C), mid_digit(C, d))


def surviveI(C: int, d: int) -> int:  # surviveI :49-51
    return (twoI(d) * twoI(mid_digit(C, d))
            + twoI(mid_digit(C, d)) * twoI(final_micro_digit(C, d)))


def owner_source(s) -> int:  # ownerSource, GSTHypothesisSpanningProof.lean:67-68
    return surviveI(s[0], s[1])


def shuffle_cell(s):  # GSTHypothesisComplete.lean:512-517
    t = s[0] + 4 * s[1]
    return (t // 3, t % 3)


def mirror_cell(s):  # GSTHypothesisComplete.lean:521-527
    return (3 - s[0], 2 - s[1])


def cm_sign(s) -> int:  # GSTHypothesisComplete.lean:531-534
    return 1 if (s[0] + 4 * s[1]) in {0, 1, 3, 4, 5, 9} else -1


def n12_apply(u: dict) -> dict:
    """N12_val: N12 u s = u (shuffleCell s) + cmSign s * u (mirrorCell s)
    + ownerSource s * u s   (GSTHypothesisSpanningProof.lean:123-127)."""
    return {s: (u[shuffle_cell(s)]
                + cm_sign(s) * u[mirror_cell(s)]
                + owner_source(s) * u[s])
            for s in CELLS}


def seed12() -> dict:  # GSTHypothesisComplete.lean:555-558
    return {s: (1 if s in {(0, 0), (0, 1)} else 0) for s in CELLS}


def vec_to_list(u: dict):
    return [u[s] for s in CELLS]


def semantic_T_matrix():
    """T[i][j] = coefficient of u(cell j) in N12 u (cell i) — derived from
    the semantic definition only (never from the parsed Twave)."""
    T = [[0] * N for _ in range(N)]
    for i, s in enumerate(CELLS):
        T[i][IDX[shuffle_cell(s)]] += 1
        T[i][IDX[mirror_cell(s)]] += cm_sign(s)
        T[i][IDX[s]] += owner_source(s)
    return T


# ----------------------------------------------------------------------------
# §2 Parsing the canonical data straight out of the Lean sources
# ----------------------------------------------------------------------------

def _read(path: str) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def parse_owner_source_values(span_text: str):
    """The twelve decided cell values of ownerSource
    (GSTHypothesisSpanningProof.lean:73-84)."""
    pat = re.compile(
        r"ownerSource_val_(\d+)_(\d+) : ownerSource \(\((\d+) : Fin 4\), "
        r"\((\d+) : Fin 3\)\) = \((-?\d+) : ℚ\)")
    table = {}
    for m in pat.finditer(span_text):
        c, d, c2, d2, v = m.groups()
        assert (int(c), int(d)) == (int(c2), int(d2))
        table[(int(c), int(d))] = int(v)
    return table


def parse_kvec(span_text: str):
    """Kvec : Fin 12 -> WaveSignal12 (GSTHypothesisSpanningProof.lean:147-161).
    Returns dict n -> {cell: value} for n = 1..11 (n = 0 is seed12)."""
    body = re.search(r"def Kvec : Fin 12 → WaveSignal12 :=([\s\S]*?)\n\n", span_text)
    assert body is not None, "Kvec definition not found"
    text = body.group(1)
    tables = {}
    row_pat = re.compile(r"if n = (\d+) then \((.*)\)\s*$", re.M)
    cell_pat = re.compile(
        r"if s = \(\((\d+) : Fin 4\), \((\d+) : Fin 3\)\) then \((-?\d+) : ℚ\)")
    for m in row_pat.finditer(text):
        n = int(m.group(1))
        inner = m.group(2)
        table = {}
        for cm in cell_pat.finditer(inner):
            table[(int(cm.group(1)), int(cm.group(2)))] = int(cm.group(3))
        assert len(table) > 0, f"Kvec row {n} parsed empty"
        tables[n] = table
    return tables


def parse_cvec(face_text: str):
    """Cvec : the coordinate Krylov table
    (GSTHypothesisSpanningCompilerFace.lean:109-123).
    Returns dict n -> {index: value} for n = 0..11."""
    body = re.search(r"def Cvec : Fin 12 → \(Fin 12 → ℚ\) :=([\s\S]*?)\n\n",
                     face_text)
    assert body is not None, "Cvec definition not found"
    text = body.group(1)
    tables = {}
    row_pat = re.compile(r"if n = \((\d+) : Fin 12\) then \((.*)\)\s*$", re.M)
    idx_pat = re.compile(r"if i = \((\d+) : Fin 12\) then \((-?\d+) : ℚ\)")
    for m in row_pat.finditer(text):
        n = int(m.group(1))
        inner = m.group(2)
        table = {}
        for im in idx_pat.finditer(inner):
            table[int(im.group(1))] = int(im.group(2))
        assert len(table) > 0, f"Cvec row {n} parsed empty"
        tables[n] = table
    return tables


def parse_twave(face_text: str):
    """Twave : Matrix (Fin 12) (Fin 12) ℚ
    (GSTHypothesisSpanningCompilerFace.lean:63-77).  Column j is F1 applied
    to the j-th cell basis vector; row i is the i-th cell, i = 3c + d."""
    body = re.search(r"def Twave : Matrix \(Fin 12\) \(Fin 12\) ℚ :=([\s\S]*?)\n\n",
                     face_text)
    assert body is not None, "Twave definition not found"
    text = body.group(1)
    T = [[0] * N for _ in range(N)]
    row_pat = re.compile(r"if i = \((\d+) : Fin 12\) then \((.*)\)\s*$", re.M)
    idx_pat = re.compile(r"if j = \((\d+) : Fin 12\) then \((-?\d+) : ℚ\)")
    seen_rows = set()
    for m in row_pat.finditer(text):
        i = int(m.group(1))
        inner = m.group(2)
        seen_rows.add(i)
        for jm in idx_pat.finditer(inner):
            T[i][int(jm.group(1))] = int(jm.group(2))
    assert seen_rows == set(range(N)), f"Twave rows parsed: {sorted(seen_rows)}"
    return T


def parse_cert_row_of(span_text: str):
    """certRowOf : the Gauss-Jordan spanning certificate coefficients
    (GSTHypothesisSpanningProof.lean:420-434).
    Returns dict cell -> {n: Fraction}."""
    body = re.search(r"def certRowOf : TwelveCell → Fin 12 → ℚ :=([\s\S]*?)\n\n",
                     span_text)
    assert body is not None, "certRowOf definition not found"
    text = body.group(1)
    cert = {}
    row_pat = re.compile(
        r"if s = \(\((\d+) : Fin 4\), \((\d+) : Fin 3\)\) then \((.*)\)\s*$", re.M)
    frac_pat = re.compile(r"if n = (\d+) then \((-?\d+) / (\d+) : ℚ\)")
    for m in row_pat.finditer(text):
        cell = (int(m.group(1)), int(m.group(2)))
        inner = m.group(3)
        table = {}
        for fm in frac_pat.finditer(inner):
            table[int(fm.group(1))] = Fraction(int(fm.group(2)), int(fm.group(3)))
        assert len(table) == 12, f"certRowOf cell {cell}: {len(table)} entries"
        cert[cell] = table
    return cert


# ----------------------------------------------------------------------------
# §3 Exact linear algebra (pure Python)
# ----------------------------------------------------------------------------

def mat_vec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]


def transpose(M):
    return [list(col) for col in zip(*M)]


def bareiss_det(M):
    """Fraction-free Bareiss elimination with pivoting; exact integer det."""
    n = len(M)
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            swap = None
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    swap = r
                    break
            if swap is None:
                return 0
            A[k], A[swap] = A[swap], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = A[i][j] * A[k][k] - A[i][k] * A[k][j]
                assert num % prev == 0, "Bareiss division not exact (bug)"
                A[i][j] = num // prev
            A[i][k] = 0
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def fraction_det(M):
    """Independent cross-check: Gaussian elimination over Fractions."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for k in range(n):
        piv = None
        for r in range(k, n):
            if A[r][k] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            det = -det
        det *= A[k][k]
        inv = Fraction(1) / A[k][k]
        for r in range(k + 1, n):
            f = A[r][k] * inv
            if f != 0:
                for c in range(k, n):
                    A[r][c] -= f * A[k][c]
    return det


def det_mod_p(M, p):
    """Determinant over GF(p) by elimination with modular inverses."""
    n = len(M)
    A = [[x % p for x in row] for row in M]
    det = 1
    for k in range(n):
        piv = None
        for r in range(k, n):
            if A[r][k] != 0:
                piv = r
                break
        if piv is None:
            return 0
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            det = -det
        det = (det * A[k][k]) % p
        inv = pow(A[k][k], -1, p)
        for r in range(k + 1, n):
            f = (A[r][k] * inv) % p
            if f:
                for c in range(k, n):
                    A[r][c] = (A[r][c] - f * A[k][c]) % p
    return det % p


def minor(M, r, c):
    return [[M[i][j] for j in range(len(M[0])) if j != c]
            for i in range(len(M)) if i != r]


def adjugate(M):
    """Integer adjugate via cofactors (each minor det by Bareiss)."""
    n = len(M)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            cof = ((-1) ** (i + j)) * bareiss_det(minor(M, j, i))
            adj[i][j] = cof
    return adj


def mat_pow_by_squaring(M, e):
    """T^e by repeated squaring (independent of iterated matvec)."""
    n = len(M)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    base = [row[:] for row in M]
    while e > 0:
        if e & 1:
            R = mat_mul(R, base)
        base = mat_mul(base, base)
        e >>= 1
    return R


# ----------------------------------------------------------------------------
# §4 Z3 queries
# ----------------------------------------------------------------------------

def z3_check(label: str, solver: z3.Solver) -> str:
    verdict = str(solver.check())
    _z3_query_log.append((label, verdict))
    return verdict


def z3_kernel_unsat_int(K):
    """Z3 query: exists c in Z^12, c != 0 and K^T c = 0?  Must be UNSAT.
    Equation j: sum_i K[i][j] * c_i = 0  (c annihilates every orbit column)."""
    c = [z3.Int(f"c_{i}") for i in range(N)]
    s = z3.Solver()
    for j in range(N):
        s.add(z3.Sum([z3.IntVal(K[i][j]) * c[i] for i in range(N)]) == 0)
    s.add(z3.Or([c[i] != 0 for i in range(N)]))
    return z3_check("kernel_int_KT_c_eq_0_nonzero", s)


def z3_identity_queries(A, B, C, label):
    """Z3 validity queries: for each (i, j), assert (A*B)[i][j] != C[i][j]
    and require UNSAT.  The dot products are built as Z3 terms from the
    integer constants, so Z3 re-does the arithmetic."""
    verdicts = []
    for i in range(N):
        for j in range(N):
            lhs = z3.Sum([z3.IntVal(A[i][k]) * z3.IntVal(B[k][j])
                          for k in range(N)])
            s = z3.Solver()
            s.add(lhs != z3.IntVal(C[i][j]))
            verdicts.append(
                z3_check(f"{label}[{i}][{j}]", s))
    return verdicts


def kernel_vector_mod_p(A, p):
    """A nonzero solution c in [0, p-1]^n of A c = 0 over GF(p), where A is
    the (singular mod p) matrix, or None if A is nonsingular mod p."""
    n = len(A)
    R = [[x % p for x in row] for row in A]
    pivots = []  # (row, col)
    r = 0
    for c_ in range(n):
        piv = None
        for rr in range(r, n):
            if R[rr][c_] != 0:
                piv = rr
                break
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c_], -1, p)
        R[r] = [(x * inv) % p for x in R[r]]
        for rr in range(n):
            if rr != r and R[rr][c_] != 0:
                f = R[rr][c_]
                R[rr] = [(R[rr][k] - f * R[r][k]) % p for k in range(n)]
        pivots.append((r, c_))
        r += 1
        if r == n:
            break
    pivot_cols = {c_ for (_, c_) in pivots}
    free_cols = [c_ for c_ in range(n) if c_ not in pivot_cols]
    if not free_cols:
        return None  # nonsingular mod p
    f = free_cols[0]
    x = [0] * n
    x[f] = 1
    for (rr, c_) in pivots:
        # RREF row rr: x[c_] + sum_{j != c_} R[rr][j] x[j] = 0 (mod p)
        x[c_] = (-R[rr][f]) % p
    assert all(sum(A[i][j] * x[j] for j in range(n)) % p == 0 for i in range(n))
    assert any(v % p != 0 for v in x)
    return x


def z3_witness_mod_p(K, p, witness):
    """Z3 check that the exhibited witness c satisfies K^T c = 0 (mod p)
    with c != 0.  Expected verdict: SAT (the witness exists — this
    certifies p | det).  All c_i are Z3 constants, so SAT means the
    arithmetic identity system is verified consistent with the witness."""
    c = [z3.Int(f"w_{i}") for i in range(N)]
    s = z3.Solver()
    for i in range(N):
        s.add(c[i] == witness[i])
    q = [z3.Int(f"wq_{j}") for j in range(N)]
    for j in range(N):
        s.add(z3.Sum([z3.IntVal(K[i][j] % p) * c[i] for i in range(N)])
              == p * q[j])
    s.add(z3.Or([c[i] != 0 for i in range(N)]))
    return z3_check(f"divisor_witness_mod_{p}", s)


def z3_kernel_unsat_mod_p(K, p):
    """Z3 query mod p: exists c in [0,p-1]^12, c != 0, with
    sum_i (K[i][j] mod p) * c_i = 0 (mod p) for all j?  Must be UNSAT
    exactly when det K is nonzero mod p.  Encoded as pure LIA:
    sum_i a_ij c_i = p * q_j with bounded q_j."""
    c = [z3.Int(f"cp_{i}") for i in range(N)]
    q = [z3.Int(f"q_{j}") for j in range(N)]
    s = z3.Solver()
    for i in range(N):
        s.add(c[i] >= 0, c[i] <= p - 1)
    qmax = (N * (p - 1) * (p - 1)) // p + 2
    for j in range(N):
        s.add(z3.Sum([z3.IntVal(K[i][j] % p) * c[i] for i in range(N)])
              == p * q[j])
        s.add(q[j] >= 0, q[j] <= qmax)
    s.add(z3.Or([c[i] != 0 for i in range(N)]))
    return z3_check(f"kernel_mod_{p}", s)


# ----------------------------------------------------------------------------
# Main battery
# ----------------------------------------------------------------------------

def main() -> int:
    t0 = time.time()
    discrepancies = []

    log("=" * 78)
    log("W2-C  GST TWELVE-CELL KRYLOV SPANNING CERTIFICATE — Z3 5.4.1 BATTERY")
    log("=" * 78)
    z3_version = z3.get_version_string()
    log(f"Z3 version: {z3_version}")
    assert z3_version == "5.4.1", f"unexpected Z3 version {z3_version}"

    # ---------------- parse canonical data ----------------
    span_text = _read(SPAN_FILE)
    face_text = _read(FACE_FILE)

    Twave = parse_twave(face_text)
    kvec_tables = parse_kvec(span_text)
    cvec_tables = parse_cvec(face_text)
    owner_table = parse_owner_source_values(span_text)
    cert = parse_cert_row_of(span_text)

    assert sorted(kvec_tables.keys()) == list(range(1, 12)), \
        f"Kvec rows parsed: {sorted(kvec_tables.keys())}"
    assert sorted(cvec_tables.keys()) == list(range(0, 12)), \
        f"Cvec rows parsed: {sorted(cvec_tables.keys())}"
    assert len(owner_table) == 12, f"ownerSource values parsed: {len(owner_table)}"
    assert len(cert) == 12, f"certRowOf cells parsed: {len(cert)}"

    log("[PARSE] Twave matrix (12x12), Kvec table (rows 1..11), "
        "Cvec table (rows 0..11), ownerSource table (12 cells), "
        "certRowOf certificate (12 cells x 12 coefficients): all parsed.")

    # ---------------- semantic rebuild + data agreement ----------------
    # (i) ownerSource: surviveI recomputation vs the twelve decided Lean values
    owner_sem = {s: owner_source(s) for s in CELLS}
    owner_agree = all(owner_sem[s] == owner_table[s] for s in CELLS)
    if not owner_agree:
        for s in CELLS:
            if owner_sem[s] != owner_table[s]:
                discrepancies.append(
                    f"ownerSource{'' if True else ''} {s}: surviveI recomputation "
                    f"{owner_sem[s]} != Lean decided value {owner_table[s]}")
    log(f"[DATA] ownerSource surviveI-recomputed vs Lean decided table: "
        f"{'AGREE (12/12)' if owner_agree else 'DISAGREE'}")
    # the two cell certificates, ownerSource_null / ownerSource_max
    cert_null = owner_sem[(0, 0)] == 0
    cert_max = owner_sem[(3, 2)] == 2
    log(f"[DATA] ownerSource_null (ownerSource (0,0) = 0): {cert_null}")
    log(f"[DATA] ownerSource_max  (ownerSource (3,2) = 2): {cert_max}")
    if not (cert_null and cert_max):
        discrepancies.append("cell certificates ownerSource_null/max failed")

    # (ii) semantic operator matrix vs the parsed Twave (Twave_bridge data)
    T_sem = semantic_T_matrix()
    twave_agree = T_sem == Twave
    if not twave_agree:
        for i in range(N):
            for j in range(N):
                if T_sem[i][j] != Twave[i][j]:
                    discrepancies.append(
                        f"Twave[{i}][{j}]: semantic {T_sem[i][j]} != "
                        f"Lean Twave {Twave[i][j]}")
    log(f"[DATA] semantic T (shuffle/mirror/cmSign/surviveI) vs Lean Twave: "
        f"{'IDENTICAL (144/144)' if twave_agree else 'DISAGREE'}")

    # (iii) seed tables
    seed_sem = seed12()
    seed_list = vec_to_list(seed_sem)
    coord_seed_parsed = [cvec_tables[0].get(i, 0) for i in range(N)]
    seed_agree = (seed_list == coord_seed_parsed
                  and seed_list == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    log(f"[DATA] seed12 vs coordSeed vs canonical (1,1,0,...): "
        f"{'AGREE' if seed_agree else 'DISAGREE'}")
    if not seed_agree:
        discrepancies.append(f"seed disagreement: {seed_list} vs {coord_seed_parsed}")

    # ---------------- Krylov orbit, three independent routes ----------------
    # Route 1: iterated Twave matvec  (C (n+1) = Twave.mulVec (C n))
    orbit1 = [seed_list]
    for _ in range(N - 1):
        orbit1.append(mat_vec(Twave, orbit1[-1]))

    # Route 2: the semantic operator applied as a function (N12_val)
    u = dict(seed_sem)
    orbit2 = [vec_to_list(u)]
    for _ in range(N - 1):
        u = n12_apply(u)
        orbit2.append(vec_to_list(u))

    # Route 3: matrix powers by repeated squaring, then applied to the seed
    orbit3 = []
    for k in range(N):
        Pk = mat_pow_by_squaring(Twave, k)
        orbit3.append(mat_vec(Pk, seed_list))

    route_agree = (orbit1 == orbit2 == orbit3)
    log(f"[ORBIT] routes: Twave-matvec / semantic-N12 / matrix-power-squaring: "
        f"{'ALL IDENTICAL (3 x 144 entries)' if route_agree else 'DISAGREE'}")
    if not route_agree:
        discrepancies.append("orbit route disagreement "
                             f"(matvec==sem: {orbit1 == orbit2}, "
                             f"matvec==pow: {orbit1 == orbit3})")

    # (iv) computed orbit vs the two Lean Krylov tables
    kvec_agree = True
    kvec_details = []
    for n in range(1, 12):
        lean_row = vec_to_list({s: kvec_tables[n].get(s, 0) for s in CELLS})
        if lean_row != orbit1[n]:
            kvec_agree = False
            kvec_details.append(n)
    kvec0_ok = orbit1[0] == vec_to_list(seed_sem)
    log(f"[ORBIT] computed orbit vs Lean Kvec table (Kvec 0..11, 144 entries): "
        f"{'AGREE' if (kvec_agree and kvec0_ok) else 'DISAGREE'}"
        + (f" (bad rows: {kvec_details})" if kvec_details else ""))
    if not (kvec_agree and kvec0_ok):
        discrepancies.append(f"Kvec table disagreement on rows {kvec_details}")

    cvec_agree = True
    cvec_details = []
    for n in range(12):
        lean_row = [cvec_tables[n].get(i, 0) for i in range(N)]
        if lean_row != orbit1[n]:
            cvec_agree = False
            cvec_details.append(n)
    log(f"[ORBIT] computed orbit vs Lean Cvec table (Cvec 0..11, 144 entries): "
        f"{'AGREE' if cvec_agree else 'DISAGREE'}"
        + (f" (bad rows: {cvec_details})" if cvec_details else ""))
    if not cvec_agree:
        discrepancies.append(f"Cvec table disagreement on rows {cvec_details}")

    # (v) the eleven Lean step lemmas' data: N12 (Kvec k) = Kvec (k+1)
    steps_ok = True
    bad_steps = []
    for k in range(11):
        lean_k = {s: (seed_sem[s] if k == 0 else kvec_tables[k].get(s, 0))
                  for s in CELLS}
        nxt = n12_apply(lean_k)
        lean_k1 = vec_to_list({s: kvec_tables[k + 1].get(s, 0) for s in CELLS})
        if vec_to_list(nxt) != lean_k1:
            steps_ok = False
            bad_steps.append(k)
    log(f"[ORBIT] eleven Lean step lemmas N12 (Kvec k) = Kvec (k+1), k=0..10: "
        f"{'ALL VERIFIED ON PARSED DATA' if steps_ok else 'DISAGREE'}"
        + (f" (bad: {bad_steps})" if bad_steps else ""))
    if not steps_ok:
        discrepancies.append(f"Krylov step lemma data disagreement at {bad_steps}")

    # ---------------- the Krylov matrix (canonical convention) ----------------
    # K[i][j] = (T^j seed)[i]: rows = cells (carry-major), columns = steps.
    # This is orbitMatrix (GSTGraphV2CMWaveFusion.lean:175-176) and the
    # column convention of C (n+1) = Twave.mulVec (C n).
    K = [[orbit1[j][i] for j in range(N)] for i in range(N)]
    Kt = transpose(K)
    log("[KRYLOV] K built: rows = 12 cells (carry-major), cols = orbit steps "
        "0..11 (convention of orbitMatrix / Twave.mulVec).")

    # ---------------- Method A: exact integer determinant ----------------
    det_bareiss = bareiss_det(K)
    det_bareiss_T = bareiss_det(Kt)
    det_fraction = fraction_det(K)
    log(f"[A] Bareiss det(K)                = {det_bareiss}")
    log(f"[A] Bareiss det(K^T)              = {det_bareiss_T}")
    log(f"[A] Fraction-Gaussian det(K)      = {det_fraction}")
    log(f"[A] canonical constant            = {CANONICAL_DET}")
    method_a_ok = (det_bareiss == CANONICAL_DET
                   and det_bareiss_T == CANONICAL_DET
                   and det_fraction == CANONICAL_DET)
    log(f"[A] VERDICT: {'det = -1149656584000 CONFIRMED (3 independent computations)'
        if method_a_ok else 'MISMATCH — CRITICAL'}")
    if not method_a_ok:
        discrepancies.append(
            f"Method A determinant mismatch: Bareiss {det_bareiss}, "
            f"Bareiss^T {det_bareiss_T}, Fraction {det_fraction}, "
            f"canonical {CANONICAL_DET}")

    # ---------------- Method B: Z3 direct ----------------
    # (b1) kernel-UNSAT over Z
    v_kernel = z3_kernel_unsat_int(K)
    kernel_unsat = (v_kernel == "unsat")
    log(f"[B1] Z3 kernel query  ¬∃c≠0, K^T c = 0 (over Z): {v_kernel}")
    if not kernel_unsat:
        discrepancies.append(f"Z3 integer kernel query verdict {v_kernel} (sat!)")

    # (b2) adjugate identity queries
    adj = adjugate(K)
    # Python-side verification first (both orders)
    detI = [[CANONICAL_DET if i == j else 0 for j in range(N)] for i in range(N)]
    py_adjK = mat_mul(adj, K)
    py_Kadj = mat_mul(K, adj)
    py_adj_ok = (py_adjK == detI and py_Kadj == detI)
    log(f"[B2] Python exact adj(K)*K = det*I and K*adj(K) = det*I: "
        f"{'VERIFIED (144 + 144 entries)' if py_adj_ok else 'MISMATCH — CRITICAL'}")
    if not py_adj_ok:
        discrepancies.append("Python adjugate identity failed")
    # Z3 re-verification of every entry (dot products built as Z3 terms)
    v_adjK = z3_identity_queries(adj, K, detI, "adjK")
    v_Kadj = z3_identity_queries(K, adj, detI, "Kadj")
    n_adjK_unsat = sum(1 for v in v_adjK if v == "unsat")
    n_Kadj_unsat = sum(1 for v in v_Kadj if v == "unsat")
    log(f"[B2] Z3 adj(K)*K = det*I  : {n_adjK_unsat}/144 queries UNSAT")
    log(f"[B2] Z3 K*adj(K) = det*I  : {n_Kadj_unsat}/144 queries UNSAT")
    if not (n_adjK_unsat == 144 and n_Kadj_unsat == 144):
        discrepancies.append(
            f"Z3 adjugate identity queries not all UNSAT "
            f"({n_adjK_unsat}/144, {n_Kadj_unsat}/144)")

    # ---------------- Method C: modular cross-checks ----------------
    # det factorization (pure-Python trial division): recorded, and used to
    # explain which tested primes divide the determinant.
    def factorize(m):
        f = {}
        d = 2
        while d * d <= m:
            while m % d == 0:
                f[d] = f.get(d, 0) + 1
                m //= d
            d += 1 if d == 2 else 2
        if m > 1:
            f[m] = f.get(m, 0) + 1
        return f
    det_factors = factorize(abs(CANONICAL_DET))
    det_factorization = "(-1) * " + " * ".join(
        f"{q}^{e}" for q, e in sorted(det_factors.items()))
    log(f"[C] canonical det factorization: {det_factorization}")

    mod_p = {}
    det_nonzero_mod = {}
    for p in PRIMES_PY:
        d = det_mod_p(K, p)
        expected = CANONICAL_DET % p
        agree = (d == expected)
        divides = (d == 0)
        det_nonzero_mod[p] = (d != 0)
        mod_p[str(p)] = {"det_mod_p": d, "expected": expected,
                         "agree": agree, "divides_det": divides}
        log(f"[C] det mod {p:>2} = {d:>10}  (canonical mod p = {expected:>10})  "
            f"{'AGREE' if agree else 'MISMATCH'}"
            + (f"  [p={p} DIVIDES det: v_{p}(det) = {det_factors.get(p, 0)}]"
               if divides else ""))
        if not agree:
            discrepancies.append(f"det mod {p} = {d}, expected {expected}")

    # Z3 kernel-UNSAT primes: only primes with det != 0 mod p (a prime
    # dividing det has a nontrivial mod-p kernel by necessity).
    PRIMES_Z3 = [p for p in PRIMES_PY if det_nonzero_mod[p]][:PRIMES_Z3_COUNT]
    excluded = [p for p in PRIMES_PY if not det_nonzero_mod[p]]
    log(f"[C] Z3 kernel-UNSAT primes (det =/= 0 mod p): {PRIMES_Z3}"
        + (f"; excluded (p | det): {excluded}" if excluded else ""))
    assert len(PRIMES_Z3) >= 3, "fewer than 3 primes with det != 0 mod p"
    for p in PRIMES_Z3:
        v = z3_kernel_unsat_mod_p(K, p)
        mod_p[str(p)]["z3_kernel_unsat"] = (v == "unsat")
        mod_p[str(p)]["z3_kernel_verdict"] = v
        log(f"[C] Z3 mod-{p} kernel-UNSAT: {v}")
        if v != "unsat":
            discrepancies.append(f"Z3 mod-{p} kernel query verdict {v} (sat!)")

    # Divisor-prime witnesses: for every tested prime dividing det, exhibit
    # a nonzero mod-p annihilator of K^T and Z3-certify the witness (sat).
    # This certifies p | det — a positive finding, loudly recorded.
    divisor_witnesses = {}
    Kt_m = transpose(K)
    for p in excluded:
        w = kernel_vector_mod_p(Kt_m, p)
        assert w is not None, f"p={p} divides det but no mod-p kernel vector?"
        v = z3_witness_mod_p(K, p, w)
        ok = (v == "sat")
        divisor_witnesses[str(p)] = {
            "witness": w,
            "z3_verdict": v,
            "certifies": f"{p} | det (v_{p}(det) = {det_factors.get(p, 0)}), "
                         f"exhibited nonzero mod-{p} annihilator of K^T",
        }
        log(f"[C] Z3 mod-{p} divisor witness (expected sat): {v}  "
            f"-> CERTIFIES {p} | det; witness c = {w}")
        if not ok:
            discrepancies.append(
                f"mod-{p} divisor witness Z3 verdict {v} (expected sat)")

    # ---------------- Method D summary (computed above) ----------------
    method_d = {
        "twave_vs_semantic_operator": twave_agree,
        "owner_source_table": owner_agree,
        "seed_tables": seed_agree,
        "orbit_route_matvec_vs_semantic": orbit1 == orbit2,
        "orbit_route_matvec_vs_matrix_power": orbit1 == orbit3,
        "orbit_vs_lean_kvec_table": kvec_agree and kvec0_ok,
        "orbit_vs_lean_cvec_table": cvec_agree,
        "eleven_step_lemma_data": steps_ok,
    }
    method_d_ok = all(method_d.values())
    log(f"[D] independent recomputation agreement: "
        f"{'ALL ROUTES AND TABLES AGREE' if method_d_ok else 'DISAGREE'}")
    if not method_d_ok:
        discrepancies.append(f"Method D disagreement: {method_d}")

    # ---------------- Supplementary: the Gauss-Jordan certificate ----------
    # certRow * K^T = I (i.e. eCell_eq_cert data: e_s = sum_n certRowOf s n *
    # worldOrbit n).  Exact Fractions.
    cert_ok = True
    cert_bad = []
    for si, s in enumerate(CELLS):
        row = [cert[s].get(n, Fraction(0)) for n in range(N)]
        for ti, t in enumerate(CELLS):
            val = sum(row[n] * Fraction(K[ti][n]) for n in range(N))
            if val != (1 if si == ti else 0):
                cert_ok = False
                cert_bad.append((s, t, str(val)))
    log(f"[SUPP] Lean spanning certificate certRowOf (certRow * K^T = I, "
        f"exact rationals, 144 entries): "
        f"{'VERIFIED' if cert_ok else 'MISMATCH — CRITICAL'}")
    if not cert_ok:
        discrepancies.append(f"certRowOf certificate failures: {cert_bad[:5]} ...")

    # ---------------- totals and verdict ----------------
    total_queries = len(_z3_query_log)
    witness_labels = {l for (l, _) in _z3_query_log
                      if l.startswith("divisor_witness")}
    core_verdicts = [v for (l, v) in _z3_query_log if l not in witness_labels]
    witness_verdicts = [v for (l, v) in _z3_query_log if l in witness_labels]
    all_unsat = all(v == "unsat" for v in core_verdicts)
    witnesses_all_sat = all(v == "sat" for v in witness_verdicts)
    verdict_ok = (method_a_ok and kernel_unsat and method_d_ok
                  and n_adjK_unsat == 144 and n_Kadj_unsat == 144
                  and all(mod_p[str(p)]["agree"] for p in PRIMES_PY)
                  and all(mod_p[str(p)].get("z3_kernel_unsat") is True
                          for p in PRIMES_Z3)
                  and cert_ok and all_unsat and witnesses_all_sat
                  and not discrepancies)

    log("-" * 78)
    log(f"TOTAL Z3 QUERIES: {total_queries}")
    log(f"ALL UNSAT      : {all_unsat}")
    log(f"VERDICT        : {'PASS — CERTIFIED' if verdict_ok else 'FAIL'}")
    if discrepancies:
        log("!!! DISCREPANCIES !!!")
        for d in discrepancies:
            log(f"  !! {d}")
    log("-" * 78)

    # breakdown of query verdicts
    verdict_counts = {}
    for (_, v) in _z3_query_log:
        verdict_counts[v] = verdict_counts.get(v, 0) + 1
    log(f"Z3 verdict histogram: {verdict_counts}")

    verdict = {
        "task_id": "W2-C",
        "battery": "gst_twelve_point_krylov_z3_battery_20261116",
        "claim": ("Krylov matrix of Twave (= N12 = F12 ownerSource 1) on seed12 "
                  "has det = -1149656584000 != 0; the twelve orbit vectors "
                  "span the 12-dimensional Hodge fiber WaveSignal12"),
        "z3_version": z3_version,
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "method_a_det": {
            "bareiss_det_K": det_bareiss,
            "bareiss_det_K_transpose": det_bareiss_T,
            "fraction_gaussian_det_K": str(det_fraction),
            "canonical_constant": CANONICAL_DET,
            "agrees": method_a_ok,
        },
        "method_b_kernel_unsat": kernel_unsat,
        "method_b_identity_checks": {
            "adj_mul_K_queries": len(v_adjK),
            "adj_mul_K_unsat": n_adjK_unsat,
            "K_mul_adj_queries": len(v_Kadj),
            "K_mul_adj_unsat": n_Kadj_unsat,
            "python_exact_precheck": py_adj_ok,
        },
        "method_c_mod_p": mod_p,
        "method_c_z3_kernel_primes": PRIMES_Z3,
        "method_c_excluded_primes_dividing_det": excluded,
        "method_c_divisor_prime_witnesses": divisor_witnesses,
        "canonical_det_factorization": det_factorization,
        "method_d_agreement": method_d,
        "supplementary_certificate": {
            "certRowOf_times_K_transpose_equals_identity": cert_ok,
            "owner_source_null_and_max_cell_certificates": cert_null and cert_max,
        },
        "total_z3_queries": total_queries,
        "z3_core_queries": len(core_verdicts),
        "z3_core_all_unsat": all_unsat,
        "z3_divisor_witness_queries": len(witness_verdicts),
        "z3_divisor_witnesses_all_sat": witnesses_all_sat,
        "z3_verdict_histogram": verdict_counts,
        "all_unsat": all_unsat,
        "overall_pass": verdict_ok,
        "discrepancies": discrepancies,
        "data_sources": {
            "operator_matrix_T": [
                "GSTHypothesisSpanningCompilerFace.lean:63-77 (Twave, explicit)",
                "GSTHypothesisSpanningCompilerFace.lean:81-93 (Twave_bridge)",
                "GSTHypothesisSpanningProof.lean:117-127 (N12, N12_val)",
                "GSTHypothesisComplete.lean:541-564 (U12, J12, M12, F12)",
                "GSTHypothesisComplete.lean:512-534 (shuffleCell, mirrorCell, cmSign)",
                "GST2DMixedEmergence.lean:49-51 (surviveI), :34 (twoI), :9-17 (digits)",
                "GSTHypothesisSpanningProof.lean:67-84 (ownerSource + decided values)",
            ],
            "seed": [
                "GSTHypothesisComplete.lean:555-558 (seed12 = e_(0,0) + e_(0,1))",
                "GSTHypothesisSpanningCompilerFace.lean:98 (coordSeed)",
                "GSTGraphV2CMWaveFusion.lean:139-141 (seed)",
            ],
            "krylov_convention": [
                "GSTGraphV2CMWaveFusion.lean:175-176 (orbitMatrix s k = orbit k s: "
                "rows = cells, columns = orbit steps)",
                "GSTHypothesisSpanningCompilerFace.lean:101-106 "
                "(C 0 = coordSeed, C (n+1) = Twave.mulVec (C n))",
                "GSTHypothesisSpanningProof.lean:138-141 (worldOrbit recursion)",
            ],
            "krylov_tables": [
                "GSTHypothesisSpanningProof.lean:147-161 (Kvec)",
                "GSTHypothesisSpanningCompilerFace.lean:109-123 (Cvec)",
            ],
            "step_lemmas": [
                "GSTHypothesisSpanningProof.lean:203-333 "
                "(N12_Kvec_step_0..10 : N12 (Kvec k) = Kvec (k+1))",
                "GSTHypothesisSpanningProof.lean:336-391 (orbit_val_0..11)",
            ],
            "cell_certificates": [
                "GSTHypothesisSpanningProof.lean:70 (ownerSource_null : "
                "ownerSource nullCell = 0)",
                "GSTHypothesisSpanningProof.lean:71 (ownerSource_max : "
                "ownerSource maxCell = 2)",
            ],
            "determinant_constant": [
                "GSTHypothesisSpanningProof.lean:33-35 "
                "(Krylov determinant -1149656584000 of the records)",
            ],
            "spanning_certificate": [
                "GSTHypothesisSpanningProof.lean:420-444 (certRowOf, eCell_eq_cert)",
                "GSTHypothesisSpanningProof.lean:463-468 "
                "(span_range_worldOrbit_eq_top)",
            ],
        },
    }

    with open(VERDICT_FILE, "w", encoding="utf-8") as f:
        json.dump(verdict, f, indent=2, ensure_ascii=False)
    log(f"VERDICT written to: {VERDICT_FILE}")
    log(f"battery runtime: {time.time() - t0:.1f}s")
    return 0 if verdict_ok else 1


if __name__ == "__main__":
    sys.exit(main())
